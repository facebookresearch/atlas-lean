/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Code.Assembly.SortSliceSafety
import Code.Transcription.MergeLo
import Code.Transcription.MergeHi
import Lean.Elab.Command

/-!
# Merge memcpy call-site provenance

The generic `sortslice_memcpy` model must reject an overlapping request on one
backing, while CPython's six bulk-copy sites inside `merge_lo` and `merge_hi`
are admissible because they cross between the main list and temporary storage.
This module makes that call-site fact an exported assembly obligation rather
than leaving it implicit in the two C pointers.  The transcriptions enforce
the obligation structurally: their recursive bulk-copy executors themselves
require a call-site tag and a proof of its exact backing direction, with no
lower untagged bulk helper for an evaluator call to bypass.
-/

namespace CPythonListsort

universe u v

variable {κ : Type u} {ν : Type v}

open SortSlice

/-- Assembly contract connecting the exact merge memcpy call sites to the
provenance-sensitive `SortSlice` safety boundary. -/
structure MergeMemcpyCallsiteProvenanceContract
    (κ : Type u) (ν : Type v) : Prop where
  /-- All three pinned `merge_lo` sites cross main and temporary storage. -/
  mergeLoCallsitesDistinct : ∀ site : MergeLoMemcpyCallsite,
    site.backings.Distinct
  /-- All three pinned `merge_hi` sites cross main and temporary storage. -/
  mergeHiCallsitesDistinct : ∀ site : MergeHiMemcpyCallsite,
    site.backings.Distinct
  /-- Explicit distinct-backing provenance discharges memcpy's aliasing
  precondition independently of indices, length, or extensional contents. -/
  distinctBackingAdmissible : ∀ (destination source : SortSlice κ ν)
      (dst src : Int) (count : Nat),
    (MemcpySource.distinctBacking source : MemcpySource destination).Admissible
      dst src count
  /-- Regression on the rejected shape: overlapping same-backing memcpy does
  not execute, emit a partial trace, or disagree with the transcription. -/
  sameBackingOverlapRejected : ∀ (valuesPresent : Bool) (count : Nat)
      (destination : SortSlice κ ν) (dst src : Int),
    ¬ MemcpyRangesDisjoint dst src count →
      (memcpyTraced? valuesPresent count destination .sameBacking dst src).result =
          none ∧
        (memcpyTraced? valuesPresent count destination .sameBacking dst src).trace =
          AccessTrace.empty ∧
        (memcpyTraced? valuesPresent count destination .sameBacking dst src).erase =
          memcpy? count destination .sameBacking dst src

/-- The exact `merge_lo`/`merge_hi` memcpy sites satisfy distinct-backing
provenance, while the generic same-backing overlap case remains rejected.

This is the declaration intended for the roadmap node's `lean:` field. -/
theorem mergeMemcpyCallsiteProvenance :
    MergeMemcpyCallsiteProvenanceContract κ ν where
  mergeLoCallsitesDistinct := mergeLo_memcpyCallsite_distinct
  mergeHiCallsitesDistinct := mergeHi_memcpyCallsite_distinct
  distinctBackingAdmissible := by
    intro destination source dst src count
    trivial
  sameBackingOverlapRejected := memcpyTraced_sameBacking_overlap_rejected

/-! ## Closed bulk-movement inventory -/

/-- The primitive class used at a merge bulk-movement site. -/
inductive MergeBulkMoveKind where
  | distinctBackingMemcpy
  | sameStoreMemmove
  deriving DecidableEq, Repr

/-- Type-level vocabulary for the six temp/main `memcpy` tags and four
same-main-store `memmove` tags.  Actual evaluator coverage is checked against
declaration bodies below; constructor counting is not used as coverage proof. -/
inductive MergeBulkMoveCallsite where
  | loMemcpy (site : MergeLoMemcpyCallsite)
  | hiMemcpy (site : MergeHiMemcpyCallsite)
  | memmove (site : MergeMemmoveCallsite)
  deriving DecidableEq, Repr

namespace MergeBulkMoveCallsite

def kind : MergeBulkMoveCallsite → MergeBulkMoveKind
  | .loMemcpy _ | .hiMemcpy _ => .distinctBackingMemcpy
  | .memmove _ => .sameStoreMemmove

/-- Backing direction exists exactly for the six `memcpy`-class sites. -/
def memcpyBackings? : MergeBulkMoveCallsite → Option MergeMemcpyBackings
  | .loMemcpy site => some site.backings
  | .hiMemcpy site => some site.backings
  | .memmove _ => none

/-- Each declared site is classified exclusively by its physical backing
relationship: all `memcpy` sites have proved-distinct backings, while all
same-store sites carry one of the four memmove tags. -/
theorem classification (site : MergeBulkMoveCallsite) :
    (site.kind = .distinctBackingMemcpy ↔
      ∃ backings, site.memcpyBackings? = some backings ∧ backings.Distinct) ∧
    (site.kind = .sameStoreMemmove ↔
      ∃ memmoveSite, site = .memmove memmoveSite) := by
  cases site with
  | loMemcpy site =>
      cases site <;>
        simp [kind, memcpyBackings?, MergeLoMemcpyCallsite.backings,
          MergeMemcpyBackings.Distinct]
  | hiMemcpy site =>
      cases site <;>
        simp [kind, memcpyBackings?, MergeHiMemcpyCallsite.backings,
          MergeMemcpyBackings.Distinct]
  | memmove site =>
      exact ⟨by simp [kind, memcpyBackings?], by simp [kind]⟩

end MergeBulkMoveCallsite

/-! ## Compile-time evaluator-body coverage audit

This audit starts at the two public merge evaluators and follows the bodies of
every reachable declaration in the `CPythonListsort` namespace.  The tagged
call-site audit treats the five classified bulk wrappers as boundaries.  A
second raw-primitive audit traverses through the four memcpy wrappers and
permits exactly one direct `SortSlice.memmove?` reference: the implementation
of `mergeDataMemmove?`.  Thus adding, deleting, duplicating, retagging, or
bypassing an actual evaluator call site makes this module fail to compile.
-/

open Lean Elab Command

private meta structure MergeBulkTaggedUse where
  owner : Name
  wrapper : Name
  tag : Name
  deriving BEq, Repr

private meta structure MergeBulkDirectAudit where
  rawMemmoveRefs : Nat := 0
  taggedUses : Array (Name × Option Name) := #[]
  deriving Inhabited, Repr

private meta def mergeBulkWrappers : Array Name :=
  #[``mergeDataMemmove?,
    ``mergeLoMemcpyDataToTemp?, ``mergeLoMemcpyTempToData?,
    ``mergeHiMemcpyDataToTemp?, ``mergeHiMemcpyTempToData?]

private meta def mergeMemcpyWrappers : Array Name :=
  #[``mergeLoMemcpyDataToTemp?, ``mergeLoMemcpyTempToData?,
    ``mergeHiMemcpyDataToTemp?, ``mergeHiMemcpyTempToData?]

private meta def mergeBulkTags : Array Name :=
  #[``MergeMemmoveCallsite.loGallopB,
    ``MergeMemmoveCallsite.loCopyBTail,
    ``MergeMemmoveCallsite.hiGallopA,
    ``MergeMemmoveCallsite.hiCopyATail,
    ``MergeLoMemcpyCallsite.initialDataToTemp,
    ``MergeLoMemcpyCallsite.gallopTempToData,
    ``MergeLoMemcpyCallsite.finalTempToData,
    ``MergeHiMemcpyCallsite.initialDataToTemp,
    ``MergeHiMemcpyCallsite.gallopTempToData,
    ``MergeHiMemcpyCallsite.finalTempToData]

private meta def mergeBulkConstName? (expression : Expr) : Option Name :=
  match expression.getAppFn with
  | .const name _ => some name
  | _ => none

private meta def mergeBulkLiteralTag? (arguments : Array Expr) : Option Name :=
  arguments.foldl (fun found argument => found.orElse fun _ =>
    match mergeBulkConstName? argument with
    | some name => if mergeBulkTags.contains name then some name else none
    | none => none) none

private meta partial def auditMergeBulkExpr (expression : Expr)
    (audit : MergeBulkDirectAudit := {}) : MergeBulkDirectAudit :=
  match expression with
  | .app function argument =>
      match mergeBulkConstName? expression with
      | some wrapper =>
          if mergeBulkWrappers.contains wrapper then
            let audit := { audit with
              taggedUses := audit.taggedUses.push
                (wrapper, mergeBulkLiteralTag? expression.getAppArgs) }
            expression.getAppArgs.foldl
              (fun audit argument => auditMergeBulkExpr argument audit) audit
          else
            auditMergeBulkExpr argument (auditMergeBulkExpr function audit)
      | none =>
          auditMergeBulkExpr argument (auditMergeBulkExpr function audit)
  | .lam _ type body _ | .forallE _ type body _ =>
      auditMergeBulkExpr body (auditMergeBulkExpr type audit)
  | .letE _ type value body _ =>
      auditMergeBulkExpr body
        (auditMergeBulkExpr value (auditMergeBulkExpr type audit))
  | .mdata _ body | .proj _ _ body => auditMergeBulkExpr body audit
  | .const name _ =>
      if name = ``SortSlice.memmove? then
        { audit with rawMemmoveRefs := audit.rawMemmoveRefs + 1 }
      else
        audit
  | _ => audit

private meta structure MergeBulkClosureAudit where
  visited : NameSet := {}
  uses : Array MergeBulkTaggedUse := #[]

private meta partial def auditReachableMergeBulkDecl (declaration : Name)
    (path : List Name) (audit : MergeBulkClosureAudit) :
    CommandElabM MergeBulkClosureAudit := do
  if audit.visited.contains declaration then
    return audit
  let audit := { audit with visited := audit.visited.insert declaration }
  let some info := (← getEnv).find? declaration |
    throwError "missing merge evaluator dependency {declaration}"
  let some value := info.value? | return audit
  let direct := auditMergeBulkExpr value
  unless direct.rawMemmoveRefs = 0 do
    throwError "raw SortSlice.memmove? is reachable outside \
      mergeDataMemmove? in {declaration}; path: {repr path.reverse}"
  let mut audit := audit
  for (wrapper, tag?) in direct.taggedUses do
    let some tag := tag? |
      throwError "{declaration} passes a nonliteral or unknown bulk tag to \
        {wrapper}"
    audit := { audit with
      uses := audit.uses.push { owner := declaration, wrapper := wrapper, tag := tag } }
  for dependency in value.getUsedConstants do
    if mergeBulkWrappers.contains dependency then
      continue
    if dependency = ``SortSlice.memmove? then
      throwError "raw SortSlice.memmove? is a dependency outside \
        mergeDataMemmove? of {declaration}"
    if (`CPythonListsort).isPrefixOf (privateToUserName dependency) then
      audit ← auditReachableMergeBulkDecl dependency (declaration :: path) audit
  return audit

/-- State for the all-dependency memmove audit.  It records the exhaustive
same-store tagged-call inventory while also tracking the raw primitive. -/
private meta structure MergeRawMemmoveClosureAudit where
  visited : NameSet := {}
  uses : Array MergeBulkTaggedUse := #[]

/-- Raw-primitive closure walk.  Unlike the general tagged-use walk, this
enters the distinct-backing memcpy wrappers and their helpers.  It also records
every tagged same-store call it sees, so such a call cannot hide behind a
memcpy wrapper boundary.  The tagged memmove wrapper is the sole allowed raw
boundary, and its body must contain exactly one underlying primitive use. -/
private meta partial def auditReachableRawMemmoveDecl (declaration : Name)
    (path : List Name) (audit : MergeRawMemmoveClosureAudit) :
    CommandElabM MergeRawMemmoveClosureAudit := do
  if audit.visited.contains declaration then
    return audit
  let audit := { audit with visited := audit.visited.insert declaration }
  let some info := (← getEnv).find? declaration |
    throwError "missing merge raw-memmove dependency {declaration}"
  let some value := info.value? | return audit
  let direct := auditMergeBulkExpr value
  if declaration = ``mergeDataMemmove? then
    unless direct.rawMemmoveRefs = 1 do
      throwError "mergeDataMemmove? must contain exactly one raw \
        SortSlice.memmove? reference; found {direct.rawMemmoveRefs}"
    return audit
  unless direct.rawMemmoveRefs = 0 do
    throwError "raw SortSlice.memmove? is reachable outside \
      mergeDataMemmove? in {declaration}; path: {repr path.reverse}"
  let mut audit := audit
  for (wrapper, tag?) in direct.taggedUses do
    if wrapper = ``mergeDataMemmove? then
      let some tag := tag? |
        throwError "{declaration} passes a nonliteral or unknown memmove tag"
      audit := { audit with
        uses := audit.uses.push { owner := declaration, wrapper := wrapper, tag := tag } }
  for dependency in value.getUsedConstants do
    if dependency = ``SortSlice.memmove? then
      throwError "raw SortSlice.memmove? is a dependency of {declaration}; \
        path: {repr path.reverse}"
    if (`CPythonListsort).isPrefixOf (privateToUserName dependency) then
      audit ← auditReachableRawMemmoveDecl dependency
        (declaration :: path) audit
  return audit

/-- The ten logical source call-site identities expected in the actual merge
evaluator closure.  The elaborated `mergeHi?` body contains two identical
initial-copy applications because its `.reused | .grown` pattern is compiled
into two alternatives; `mergeBulkExpectedMultiplicity` records that compiler
duplication explicitly. -/
private meta def mergeBulkExpectedUses : Array MergeBulkTaggedUse :=
  #[{ owner := ``mergeLo?, wrapper := ``mergeLoMemcpyDataToTemp?,
      tag := ``MergeLoMemcpyCallsite.initialDataToTemp },
    { owner := ``mergeLoGallopRound?, wrapper := ``mergeLoMemcpyTempToData?,
      tag := ``MergeLoMemcpyCallsite.gallopTempToData },
    { owner := ``mergeLoSucceed?, wrapper := ``mergeLoMemcpyTempToData?,
      tag := ``MergeLoMemcpyCallsite.finalTempToData },
    { owner := ``mergeLoGallopRound?, wrapper := ``mergeDataMemmove?,
      tag := ``MergeMemmoveCallsite.loGallopB },
    { owner := ``mergeLoCopyB?, wrapper := ``mergeDataMemmove?,
      tag := ``MergeMemmoveCallsite.loCopyBTail },
    { owner := ``mergeHi?, wrapper := ``mergeHiMemcpyDataToTemp?,
      tag := ``MergeHiMemcpyCallsite.initialDataToTemp },
    { owner := ``mergeHiGallopRound?, wrapper := ``mergeDataMemmove?,
      tag := ``MergeMemmoveCallsite.hiGallopA },
    { owner := ``mergeHiGallopB?, wrapper := ``mergeHiMemcpyTempToData?,
      tag := ``MergeHiMemcpyCallsite.gallopTempToData },
    { owner := ``mergeHiSucceed?, wrapper := ``mergeHiMemcpyTempToData?,
      tag := ``MergeHiMemcpyCallsite.finalTempToData },
    { owner := ``mergeHiCopyA?, wrapper := ``mergeDataMemmove?,
      tag := ``MergeMemmoveCallsite.hiCopyATail }]

/-- The four same-store calls are also checked directly in their immediate
owners.  This prevents transitive-closure bookkeeping from making a correct
aggregate count accidentally hide a moved, duplicated, or retagged call. -/
private meta def mergeMemmoveExpectedOwnerUses : Array MergeBulkTaggedUse :=
  #[{ owner := ``mergeLoGallopRound?, wrapper := ``mergeDataMemmove?,
      tag := ``MergeMemmoveCallsite.loGallopB },
    { owner := ``mergeLoCopyB?, wrapper := ``mergeDataMemmove?,
      tag := ``MergeMemmoveCallsite.loCopyBTail },
    { owner := ``mergeHiGallopRound?, wrapper := ``mergeDataMemmove?,
      tag := ``MergeMemmoveCallsite.hiGallopA },
    { owner := ``mergeHiCopyA?, wrapper := ``mergeDataMemmove?,
      tag := ``MergeMemmoveCallsite.hiCopyATail }]

private meta def mergeBulkExpectedMultiplicity
    (use : MergeBulkTaggedUse) : Nat :=
  if use.owner = ``mergeHi? &&
      use.wrapper = ``mergeHiMemcpyDataToTemp? &&
      use.tag = ``MergeHiMemcpyCallsite.initialDataToTemp then
    2
  else
    1

private meta def auditMergeBulkEvaluatorBodies : CommandElabM Unit := do
  let mut audit : MergeBulkClosureAudit := {}
  audit ← auditReachableMergeBulkDecl ``mergeLo? [] audit
  audit ← auditReachableMergeBulkDecl ``mergeHi? [] audit
  let mut rawAudit : MergeRawMemmoveClosureAudit := {}
  rawAudit ← auditReachableRawMemmoveDecl ``mergeLo? [] rawAudit
  rawAudit ← auditReachableRawMemmoveDecl ``mergeHi? [] rawAudit
  let expectedBodyUses := mergeBulkExpectedUses.foldl
    (fun total use => total + mergeBulkExpectedMultiplicity use) 0
  unless audit.uses.size = expectedBodyUses do
    throwError "found {audit.uses.size} classified bulk applications; expected \
      {expectedBodyUses}: {repr audit.uses}"
  for expected in mergeBulkExpectedUses do
    let actualCount :=
      (audit.uses.filter fun actual => actual == expected).size
    let expectedCount := mergeBulkExpectedMultiplicity expected
    unless actualCount = expectedCount do
      throwError "expected {expectedCount} body use(s) of {repr expected}; found \
        {actualCount}: {repr audit.uses}"
  for actual in audit.uses do
    unless mergeBulkExpectedUses.contains actual do
      throwError "unexpected classified bulk application {repr actual}"
  -- The all-dependency walk must see exactly the four same-store calls too;
  -- this closes the hole where a new call could otherwise be hidden in a
  -- helper reachable only through one of the tagged memcpy wrappers.
  unless rawAudit.uses.size = mergeMemmoveExpectedOwnerUses.size do
    throwError "found {rawAudit.uses.size} same-store calls in the full merge \
      closure; expected {mergeMemmoveExpectedOwnerUses.size}: \
      {repr rawAudit.uses}"
  for expected in mergeMemmoveExpectedOwnerUses do
    unless (rawAudit.uses.filter fun actual => actual == expected).size = 1 do
      throwError "full merge closure does not contain exactly one use of \
        {repr expected}: {repr rawAudit.uses}"
  for actual in rawAudit.uses do
    unless mergeMemmoveExpectedOwnerUses.contains actual do
      throwError "unexpected same-store call in full merge closure: \
        {repr actual}"
  -- Pin every same-store wrapper/tag pair to the body that actually owns it,
  -- independently of the aggregate closure inventory above.
  for expected in mergeMemmoveExpectedOwnerUses do
    let some ownerInfo := (← getEnv).find? expected.owner |
      throwError "missing same-store bulk owner {expected.owner}"
    let some ownerValue := ownerInfo.value? |
      throwError "same-store bulk owner {expected.owner} has no inspectable body"
    let ownerUses := (auditMergeBulkExpr ownerValue).taggedUses.filter
      (fun actual => actual.1 == ``mergeDataMemmove?)
    unless ownerUses == #[(expected.wrapper, some expected.tag)] do
      throwError "{expected.owner} must directly contain exactly the expected \
        memmove wrapper/tag pair {repr expected}; found {repr ownerUses}"
  -- The four distinct-backing wrappers must remain raw-memmove-free even
  -- though the evaluator-closure walk treats wrapper implementations as
  -- boundaries.  Only `mergeDataMemmove?` may expose the raw primitive.
  for wrapper in mergeMemcpyWrappers do
    let some wrapperInfo := (← getEnv).find? wrapper |
      throwError "missing merge memcpy wrapper {wrapper}"
    let some wrapperValue := wrapperInfo.value? |
      throwError "merge memcpy wrapper {wrapper} has no inspectable body"
    let wrapperAudit := auditMergeBulkExpr wrapperValue
    unless wrapperAudit.rawMemmoveRefs = 0 do
      throwError "merge memcpy wrapper {wrapper} must not reference \
        SortSlice.memmove? directly"
  let some wrapperInfo := (← getEnv).find? ``mergeDataMemmove? |
    throwError "missing mergeDataMemmove?"
  let some wrapperValue := wrapperInfo.value? |
    throwError "mergeDataMemmove? has no inspectable body"
  let wrapperAudit := auditMergeBulkExpr wrapperValue
  unless wrapperAudit.rawMemmoveRefs = 1 && wrapperAudit.taggedUses.isEmpty do
    throwError "mergeDataMemmove? must be the unique one-step raw memmove boundary"

/- Executable compilation tripwire connecting the classification above to
the actual transitive declaration bodies of `mergeLo?` and `mergeHi?`. -/
run_cmd auditMergeBulkEvaluatorBodies

end CPythonListsort
