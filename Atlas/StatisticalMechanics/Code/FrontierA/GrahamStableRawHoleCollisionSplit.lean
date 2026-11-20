/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierA.GrahamStableRawTokenCutReroute










open Finset

namespace StatMech.GrahamGHS.FourColor

variable {I W : Type*} [Fintype I] [DecidableEq I]
  [Fintype W] [DecidableEq W]

private theorem canonicalStableRawLeftSurplusToken_eq_of_source_target_eq
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    {x y : CanonicalStableRawLeftSurplusToken
      ends m j k l zero hloop hjk hkl hk0 p}
    (hsource : x.1 = y.1) (htarget : x.2.1 = y.2.1) : x = y := by
  classical
  rcases x with ⟨xsource, xtarget, hx⟩
  rcases y with ⟨ysource, ytarget, hy⟩
  simp only at hsource htarget
  subst ysource
  subst ytarget
  rfl


noncomputable def canonicalStableRawLeftTokenKey
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (token : CanonicalStableRawLeftSurplusToken
      ends m j k l zero hloop hjk hkl hk0 p) :
    ↑(canonicalRawCommonClosure ends m j k l zero p) ×
      leftSourceMaskFiber ends m j k l zero p :=
  (token.1, token.2.1)



noncomputable def canonicalStableRawComponentTokenKeyEmbedding
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)) :
    CanonicalStableRawComponentToken
        ends m j k l zero hloop hjk hkl hk0 p hno component ↪
      (↑(canonicalRawCommonClosure ends m j k l zero p) ×
        leftSourceMaskFiber ends m j k l zero p) := by
  classical
  let f : CanonicalStableRawComponentToken
        ends m j k l zero hloop hjk hkl hk0 p hno component →
      (↑(canonicalRawCommonClosure ends m j k l zero p) ×
        leftSourceMaskFiber ends m j k l zero p) :=
    fun token => canonicalStableRawLeftTokenKey
      ends m j k l zero hloop hjk hkl hk0 p token.1
  refine ⟨f, ?_⟩
  intro x y hxy
  apply Subtype.ext
  apply canonicalStableRawLeftSurplusToken_eq_of_source_target_eq
    ends m j k l zero hloop hjk hkl hk0 p
  · exact congrArg Prod.fst hxy
  · exact congrArg Prod.snd hxy


noncomputable def canonicalStableRawComponentDirectKeyEmbedding
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)) :
    CanonicalStableRawComponentDirectState
        ends m j k l zero hloop hjk hkl hk0 p hno component ↪
      (↑(canonicalRawCommonClosure ends m j k l zero p) ×
        leftSourceMaskFiber ends m j k l zero p) :=
  (canonicalStableRawComponentDirectEmbedding
    ends m j k l zero hloop hjk hkl hk0 p hno component).trans
      (canonicalStableRawComponentTokenKeyEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component)


noncomputable def canonicalStableRawComponentReferenceOwnerKeyEmbedding
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)) :
    StatMech.FrontierA.crossCollision
        (canonicalStableRawComponentSelfEmbedding
          ends m j k l zero hloop hjk hkl hk0 p hno component)
        (canonicalStableRawComponentDirectEmbedding
          ends m j k l zero hloop hjk hkl hk0 p hno component) ↪
      (↑(canonicalRawCommonClosure ends m j k l zero p) ×
        leftSourceMaskFiber ends m j k l zero p) :=
  (canonicalStableRawComponentReferenceOwnerCollisionEmbedding
    ends m j k l zero hloop hjk hkl hk0 p hno component).trans
      (canonicalStableRawComponentTokenKeyEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component)


noncomputable def canonicalStableRawComponentReferenceSourceFirstKeyEmbedding
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)) :
    StatMech.FrontierA.crossCollision
        (canonicalStableRawComponentSelfEmbedding
          ends m j k l zero hloop hjk hkl hk0 p hno component)
        (canonicalStableRawComponentDirectEmbedding
          ends m j k l zero hloop hjk hkl hk0 p hno component) ↪
      (↑(canonicalRawCommonClosure ends m j k l zero p) ×
        leftSourceMaskFiber ends m j k l zero p) :=
  (canonicalStableRawComponentReferenceSourceFirstCollisionEmbedding
    ends m j k l zero hloop hjk hkl hk0 p hno component).trans
      (canonicalStableRawComponentTokenKeyEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component)

private theorem canonicalStableRawDirectLeftToken_source
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (s : CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)
    (hdirect : s.target.1 ≠ canonicalStableRawSelfBase
      ends m j k l zero hloop hjk hkl hk0 p s.source) :
    (canonicalStableRawDirectLeftToken
      ends m j k l zero hloop hjk hkl hk0 p s hdirect).1 = s.source := rfl

private theorem canonicalStableRawDirectLeftToken_target
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (s : CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)
    (hdirect : s.target.1 ≠ canonicalStableRawSelfBase
      ends m j k l zero hloop hjk hkl hk0 p s.source) :
    (canonicalStableRawDirectLeftToken
      ends m j k l zero hloop hjk hkl hk0 p s hdirect).2.1 = s.target.1 := rfl

private theorem canonicalStableRawLeftTokenTarget_val
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (token : CanonicalStableRawLeftSurplusToken
      ends m j k l zero hloop hjk hkl hk0 p) :
    (canonicalStableRawLeftTokenTarget
      ends m j k l zero hloop hjk hkl hk0 p token).1 = token.2.1 := rfl

private theorem canonicalStableRawLeftSurplusToken_target_ne_self
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (token : CanonicalStableRawLeftSurplusToken
      ends m j k l zero hloop hjk hkl hk0 p) :
    token.2.1 ≠ canonicalStableRawSelfBase
      ends m j k l zero hloop hjk hkl hk0 p token.1 := by
  classical
  exact Finset.ne_of_mem_erase token.2.2



theorem canonicalStableRawOwnerStableOutput_directKey_eq_referenceSource
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (s u : CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)
    (hself : s.target.1 = canonicalStableRawSelfBase
      ends m j k l zero hloop hjk hkl hk0 p s.source)
    (huTargetRaw : u.target.1 =
      (canonicalStableRawReferenceOwnerAlternateData
        ends m j k l zero hloop hjk hkl hk0 p s hself).target)
    (huStable : CanonicalStableRawOwnerStableOutput
      ends m j k l zero hloop hjk hkl hk0 p s u) :
    ∃ huDirect : u.target.1 ≠ canonicalStableRawSelfBase
        ends m j k l zero hloop hjk hkl hk0 p u.source,
      (s.source, (canonicalStableRawReferenceOwnerAlternateData
          ends m j k l zero hloop hjk hkl hk0 p s hself).target) =
        (u.source, u.target.1) := by
  classical
  let data := canonicalStableRawReferenceOwnerAlternateData
    ends m j k l zero hloop hjk hkl hk0 p s hself
  have hsourceNe : data.target ≠ canonicalStableRawSelfBase
      ends m j k l zero hloop hjk hkl hk0 p s.source := by
    intro heq
    apply data.target_ne_referenceSelf
    exact heq.trans (canonicalStableRawReferenceOwner_sourceBase
      ends m j k l zero hloop hjk hkl hk0 p s hself)
  have hbase : canonicalStableRawSelfBase
        ends m j k l zero hloop hjk hkl hk0 p u.source =
      canonicalStableRawSelfBase
        ends m j k l zero hloop hjk hkl hk0 p s.source :=
    congrArg (canonicalStableRawSelfBase
      ends m j k l zero hloop hjk hkl hk0 p) huStable.1
  have huDirect : u.target.1 ≠ canonicalStableRawSelfBase
      ends m j k l zero hloop hjk hkl hk0 p u.source := by
    intro heq
    apply hsourceNe
    calc
      data.target = u.target.1 := huTargetRaw.symm
      _ = canonicalStableRawSelfBase
          ends m j k l zero hloop hjk hkl hk0 p u.source := heq
      _ = canonicalStableRawSelfBase
          ends m j k l zero hloop hjk hkl hk0 p s.source := hbase
  refine ⟨huDirect, Prod.ext huStable.1.symm ?_⟩
  exact huTargetRaw.symm



theorem canonicalStableRawOwnerAdvancingOutput_directKey_eq_referenceOwner
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (s u : CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)
    (hself : s.target.1 = canonicalStableRawSelfBase
      ends m j k l zero hloop hjk hkl hk0 p s.source)
    (huTargetRaw : u.target.1 =
      (canonicalStableRawReferenceOwnerAlternateData
        ends m j k l zero hloop hjk hkl hk0 p s hself).target)
    (huAdvancing : CanonicalStableRawOwnerAdvancingOutput
      ends m j k l zero hloop hjk hkl hk0 p s u) :
    ∃ huDirect : u.target.1 ≠ canonicalStableRawSelfBase
        ends m j k l zero hloop hjk hkl hk0 p u.source,
      (canonicalStableRawReferenceOwner
          ends m j k l zero hloop hjk hkl hk0 p s,
        (canonicalStableRawReferenceOwnerAlternateData
          ends m j k l zero hloop hjk hkl hk0 p s hself).target) =
        (u.source, u.target.1) := by
  classical
  let owner := canonicalStableRawReferenceOwner
    ends m j k l zero hloop hjk hkl hk0 p s
  let data := canonicalStableRawReferenceOwnerAlternateData
    ends m j k l zero hloop hjk hkl hk0 p s hself
  have huSource : u.source = owner := Subtype.ext huAdvancing
  have hownerNe : data.target ≠ canonicalStableRawSelfBase
      ends m j k l zero hloop hjk hkl hk0 p owner :=
    data.target_ne_referenceSelf
  have hbase : canonicalStableRawSelfBase
        ends m j k l zero hloop hjk hkl hk0 p u.source =
      canonicalStableRawSelfBase
        ends m j k l zero hloop hjk hkl hk0 p owner :=
    congrArg (canonicalStableRawSelfBase
      ends m j k l zero hloop hjk hkl hk0 p) huSource
  have huDirect : u.target.1 ≠ canonicalStableRawSelfBase
      ends m j k l zero hloop hjk hkl hk0 p u.source := by
    intro heq
    apply hownerNe
    calc
      data.target = u.target.1 := huTargetRaw.symm
      _ = canonicalStableRawSelfBase
          ends m j k l zero hloop hjk hkl hk0 p u.source := heq
      _ = canonicalStableRawSelfBase
          ends m j k l zero hloop hjk hkl hk0 p owner := hbase
  refine ⟨huDirect, Prod.ext huSource.symm ?_⟩
  exact huTargetRaw.symm



theorem canonicalStableRawReferenceOwnerLeftToken_not_exceptional_of_stableOutput
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (s u : CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)
    (hself : s.target.1 = canonicalStableRawSelfBase
      ends m j k l zero hloop hjk hkl hk0 p s.source)
    (huTarget : u.target = canonicalStableRawLeftTokenTarget
      ends m j k l zero hloop hjk hkl hk0 p
        (canonicalStableRawReferenceOwnerLeftToken
          ends m j k l zero hloop hjk hkl hk0 p s hself))
    (huStable : CanonicalStableRawOwnerStableOutput
      ends m j k l zero hloop hjk hkl hk0 p s u) :
    ¬ CanonicalStableRawLeftTokenIsExceptional
      ends m j k l zero hloop hjk hkl hk0 p
        (canonicalStableRawReferenceOwnerLeftToken
          ends m j k l zero hloop hjk hkl hk0 p s hself) := by
  intro hexceptional
  apply hexceptional
  calc
    (canonicalStableRawReferenceOwnerLeftToken
        ends m j k l zero hloop hjk hkl hk0 p s hself).1.1 =
        canonicalStableRawPreferredRightBase ends m j k l zero
          hloop hjk hkl hk0 p s.target := rfl
    _ = canonicalStableRawPreferredRightBase ends m j k l zero
          hloop hjk hkl hk0 p u.target := huStable.2.symm
    _ = canonicalStableRawPreferredRightBase ends m j k l zero
          hloop hjk hkl hk0 p
            (canonicalStableRawLeftTokenTarget
              ends m j k l zero hloop hjk hkl hk0 p
                (canonicalStableRawReferenceOwnerLeftToken
                  ends m j k l zero hloop hjk hkl hk0 p s hself)) := by
      rw [← huTarget]



theorem canonicalStableRawComponentReferenceOwnerCollisionEmbedding_ne_direct_of_stableOutput
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p))
    (collision : StatMech.FrontierA.crossCollision
      (canonicalStableRawComponentSelfEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component)
      (canonicalStableRawComponentDirectEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component))
    (u : CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)
    (huTarget : u.target = canonicalStableRawLeftTokenTarget
      ends m j k l zero hloop hjk hkl hk0 p
        (canonicalStableRawComponentReferenceOwnerCollisionEmbedding
          ends m j k l zero hloop hjk hkl hk0 p hno component collision).1)
    (huStable : CanonicalStableRawOwnerStableOutput
      ends m j k l zero hloop hjk hkl hk0 p collision.1.1.1 u)
    (direct : CanonicalStableRawComponentDirectState
      ends m j k l zero hloop hjk hkl hk0 p hno component) :
    canonicalStableRawComponentReferenceOwnerCollisionEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component collision ≠
      canonicalStableRawComponentDirectEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component direct := by
  intro heq
  have hraw := congrArg Subtype.val heq
  have htoken : canonicalStableRawReferenceOwnerLeftToken
        ends m j k l zero hloop hjk hkl hk0 p
          collision.1.1.1 collision.1.1.2.2 =
      canonicalStableRawDirectLeftToken
        ends m j k l zero hloop hjk hkl hk0 p direct.1 direct.2.2 := by
    change canonicalStableRawReferenceOwnerLeftToken
        ends m j k l zero hloop hjk hkl hk0 p
          collision.1.1.1 collision.1.1.2.2 =
      canonicalStableRawStateLeftToken
        ends m j k l zero hloop hjk hkl hk0 p hno direct.1 at hraw
    unfold canonicalStableRawStateLeftToken at hraw
    rw [dif_neg direct.2.2] at hraw
    exact hraw
  apply canonicalStableRawReferenceOwnerLeftToken_not_exceptional_of_stableOutput
    ends m j k l zero hloop hjk hkl hk0 p collision.1.1.1 u
      collision.1.1.2.2 huTarget huStable
  rw [htoken]
  exact canonicalStableRawDirectLeftToken_isExceptional
    ends m j k l zero hloop hjk hkl hk0 p direct.1 direct.2.2



theorem canonicalStableRawComponentCollisionCharge_of_referenceOwnerStableOutputs
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p))
    (hstable : ∀ collision : StatMech.FrontierA.crossCollision
      (canonicalStableRawComponentSelfEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component)
      (canonicalStableRawComponentDirectEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component),
      ∃ u : CanonicalStableRawExceptionalEdge
          ends m j k l zero hloop hjk hkl hk0 p,
        u.target = canonicalStableRawLeftTokenTarget
          ends m j k l zero hloop hjk hkl hk0 p
            (canonicalStableRawComponentReferenceOwnerCollisionEmbedding
              ends m j k l zero hloop hjk hkl hk0 p hno component collision).1 ∧
        CanonicalStableRawOwnerStableOutput
          ends m j k l zero hloop hjk hkl hk0 p collision.1.1.1 u) :
    CanonicalStableRawComponentCollisionCharge
      ends m j k l zero hloop hjk hkl hk0 p hno component := by
  let first := canonicalStableRawComponentReferenceOwnerCollisionEmbedding
    ends m j k l zero hloop hjk hkl hk0 p hno component
  refine ⟨first, ?_, ?_⟩
  · exact canonicalStableRawComponentReferenceOwnerCollisionEmbedding_ne_self
      ends m j k l zero hloop hjk hkl hk0 p hno component
  · intro collision direct
    obtain ⟨u, huTarget, huStable⟩ := hstable collision
    exact canonicalStableRawComponentReferenceOwnerCollisionEmbedding_ne_direct_of_stableOutput
      ends m j k l zero hloop hjk hkl hk0 p hno component collision u
        huTarget huStable direct




theorem exists_canonicalStableRawComponentReferenceOwnerAdvancingOutput_of_card_lt
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p))
    (hcard : Fintype.card (CanonicalStableRawComponentToken
          ends m j k l zero hloop hjk hkl hk0 p hno component) <
        Fintype.card (CanonicalStableRawComponentState
          ends m j k l zero hloop hjk hkl hk0 p hno component)) :
    ∃ collision : StatMech.FrontierA.crossCollision
        (canonicalStableRawComponentSelfEmbedding
          ends m j k l zero hloop hjk hkl hk0 p hno component)
        (canonicalStableRawComponentDirectEmbedding
          ends m j k l zero hloop hjk hkl hk0 p hno component),
      ∃ u : CanonicalStableRawExceptionalEdge
          ends m j k l zero hloop hjk hkl hk0 p,
        u.target = canonicalStableRawLeftTokenTarget
          ends m j k l zero hloop hjk hkl hk0 p
            (canonicalStableRawComponentReferenceOwnerCollisionEmbedding
              ends m j k l zero hloop hjk hkl hk0 p hno component collision).1 ∧
        CanonicalStableRawOwnerAdvancingOutput
          ends m j k l zero hloop hjk hkl hk0 p collision.1.1.1 u := by
  classical
  by_contra hnoAdvancing
  have hstable : ∀ collision : StatMech.FrontierA.crossCollision
      (canonicalStableRawComponentSelfEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component)
      (canonicalStableRawComponentDirectEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component),
      ∃ u : CanonicalStableRawExceptionalEdge
          ends m j k l zero hloop hjk hkl hk0 p,
        u.target = canonicalStableRawLeftTokenTarget
          ends m j k l zero hloop hjk hkl hk0 p
            (canonicalStableRawComponentReferenceOwnerCollisionEmbedding
              ends m j k l zero hloop hjk hkl hk0 p hno component collision).1 ∧
        CanonicalStableRawOwnerStableOutput
          ends m j k l zero hloop hjk hkl hk0 p collision.1.1.1 u := by
    intro collision
    let token := canonicalStableRawReferenceOwnerLeftToken
      ends m j k l zero hloop hjk hkl hk0 p
        collision.1.1.1 collision.1.1.2.2
    obtain ⟨u, huTarget, huKind, _⟩ :=
      canonicalStableRawStateTokenIncidence_outputDichotomy
        ends m j k l zero hloop hjk hkl hk0 p hno token collision.1.1.1
          (canonicalStableRawReferenceOwnerLeftToken_stateTokenIncidence
            ends m j k l zero hloop hjk hkl hk0 p
              collision.1.1.1 collision.1.1.2.2)
    have huTarget' : u.target = canonicalStableRawLeftTokenTarget
        ends m j k l zero hloop hjk hkl hk0 p
          (canonicalStableRawComponentReferenceOwnerCollisionEmbedding
            ends m j k l zero hloop hjk hkl hk0 p hno component collision).1 := by
      exact huTarget
    rcases huKind with huStable | huAdvancing
    · exact ⟨u, huTarget', huStable⟩
    · exact False.elim (hnoAdvancing ⟨collision, u, huTarget', huAdvancing⟩)
  have hcharge :=
    canonicalStableRawComponentCollisionCharge_of_referenceOwnerStableOutputs
      ends m j k l zero hloop hjk hkl hk0 p hno component hstable
  obtain ⟨embedding⟩ :=
    canonicalStableRawTokenComponent_embedding_of_collisionCharge
      ends m j k l zero hloop hjk hkl hk0 p hno component hcharge
  exact (Nat.not_lt_of_ge
    (Fintype.card_le_of_injective embedding embedding.injective)) hcard





theorem exists_canonicalStableRawComponentFirstChargeKeyCollisionSplit_of_card_lt
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p))
    (hcard : Fintype.card (CanonicalStableRawComponentToken
          ends m j k l zero hloop hjk hkl hk0 p hno component) <
        Fintype.card (CanonicalStableRawComponentState
          ends m j k l zero hloop hjk hkl hk0 p hno component)) :
    let directKey := canonicalStableRawComponentDirectKeyEmbedding
      ends m j k l zero hloop hjk hkl hk0 p hno component
    let firstKey := canonicalStableRawComponentReferenceOwnerKeyEmbedding
      ends m j k l zero hloop hjk hkl hk0 p hno component
    let sourceFirstKey :=
      canonicalStableRawComponentReferenceSourceFirstKeyEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component
    Nonempty (StatMech.FrontierA.crossCollision sourceFirstKey directKey) ∨
      Nonempty (StatMech.FrontierA.crossCollision firstKey directKey) := by
  classical
  dsimp only
  obtain ⟨state, collision, third, hself, hdirect, hthird,
      hthirdNeHole, hthirdNeDirect, u, huTarget, hclass, huComponent⟩ :=
    exists_canonicalStableRawComponentFirstChargeOccupant_of_card_lt
      ends m j k l zero hloop hjk hkl hk0 p hno component hcard
  have huTargetRaw : u.target.1 =
      (canonicalStableRawReferenceOwnerAlternateData
        ends m j k l zero hloop hjk hkl hk0 p
          collision.1.1.1 collision.1.1.2.2).target :=
    (congrArg Subtype.val huTarget).trans
      ((canonicalStableRawLeftTokenTarget_val
        ends m j k l zero hloop hjk hkl hk0 p
          (canonicalStableRawComponentReferenceOwnerCollisionEmbedding
            ends m j k l zero hloop hjk hkl hk0 p hno component collision).1).trans
        (canonicalStableRawReferenceOwnerLeftToken_target
          ends m j k l zero hloop hjk hkl hk0 p
            collision.1.1.1 collision.1.1.2.2))
  rw [hself] at hclass
  rcases hclass with hstable | hadvancing
  · obtain ⟨huDirect, hkey⟩ :=
      canonicalStableRawOwnerStableOutput_directKey_eq_referenceSource
        ends m j k l zero hloop hjk hkl hk0 p
          collision.1.1.1 u collision.1.1.2.2 huTargetRaw hstable
    let direct : CanonicalStableRawComponentDirectState
        ends m j k l zero hloop hjk hkl hk0 p hno component :=
      ⟨u, huComponent, huDirect⟩
    refine Or.inl ⟨⟨(collision, direct), ?_⟩⟩
    change canonicalStableRawLeftTokenKey
        ends m j k l zero hloop hjk hkl hk0 p
          (canonicalStableRawReferenceSourceLeftToken
            ends m j k l zero hloop hjk hkl hk0 p
              collision.1.1.1 collision.1.1.2.2) =
      canonicalStableRawLeftTokenKey
        ends m j k l zero hloop hjk hkl hk0 p
          (canonicalStableRawStateLeftToken
            ends m j k l zero hloop hjk hkl hk0 p hno u)
    unfold canonicalStableRawStateLeftToken
    rw [dif_neg huDirect]
    change (collision.1.1.1.source,
        (canonicalStableRawReferenceOwnerAlternateData
          ends m j k l zero hloop hjk hkl hk0 p
            collision.1.1.1 collision.1.1.2.2).target) =
      (u.source, u.target.1)
    exact hkey
  · obtain ⟨huDirect, hkey⟩ :=
      canonicalStableRawOwnerAdvancingOutput_directKey_eq_referenceOwner
        ends m j k l zero hloop hjk hkl hk0 p
          collision.1.1.1 u collision.1.1.2.2 huTargetRaw hadvancing
    let direct : CanonicalStableRawComponentDirectState
        ends m j k l zero hloop hjk hkl hk0 p hno component :=
      ⟨u, huComponent, huDirect⟩
    refine Or.inr ⟨⟨(collision, direct), ?_⟩⟩
    change canonicalStableRawLeftTokenKey
        ends m j k l zero hloop hjk hkl hk0 p
          (canonicalStableRawReferenceOwnerLeftToken
            ends m j k l zero hloop hjk hkl hk0 p
              collision.1.1.1 collision.1.1.2.2) =
      canonicalStableRawLeftTokenKey
        ends m j k l zero hloop hjk hkl hk0 p
          (canonicalStableRawStateLeftToken
            ends m j k l zero hloop hjk hkl hk0 p hno u)
    unfold canonicalStableRawStateLeftToken
    rw [dif_neg huDirect]
    change (canonicalStableRawReferenceOwner
          ends m j k l zero hloop hjk hkl hk0 p collision.1.1.1,
        (canonicalStableRawReferenceOwnerAlternateData
          ends m j k l zero hloop hjk hkl hk0 p
            collision.1.1.1 collision.1.1.2.2).target) =
      (u.source, u.target.1)
    exact hkey




theorem canonicalStableRawComponentCrossCollision_stablePair_or_advancing
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p))
    (collision : StatMech.FrontierA.crossCollision
      (canonicalStableRawComponentSelfEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component)
      (canonicalStableRawComponentDirectEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component)) :
    Nonempty (Fin 2 ↪ CanonicalStableRawComponentToken
        ends m j k l zero hloop hjk hkl hk0 p hno component) ∨
      CanonicalStableRawOwnerAdvancingStep
        ends m j k l zero hloop hjk hkl hk0 p hno collision.1.1.1 := by
  rcases canonicalStableRawComponentCrossCollision_stable_or_advancing
      ends m j k l zero hloop hjk hkl hk0 p hno component collision with
    hstable | hadvancing
  · left
    obtain ⟨embedding⟩ :=
      canonicalStableRawOwnerStableSelfPair_componentEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno collision.1.1.1
          collision.1.1.2.2 hstable
    refine ⟨⟨fun i => ⟨(embedding i).1, ?_⟩, ?_⟩⟩
    · exact (embedding i).2.trans collision.1.1.2.1
    · intro a b hab
      apply embedding.injective
      apply Subtype.ext
      exact congrArg
        (fun token : CanonicalStableRawComponentToken
          ends m j k l zero hloop hjk hkl hk0 p hno component => token.1) hab
  · exact Or.inr hadvancing




theorem canonicalStableRawStableCrossCollision_selfBase_eq_of_nextTarget_eq
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p))
    (x y : StatMech.FrontierA.crossCollision
      (canonicalStableRawComponentSelfEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component)
      (canonicalStableRawComponentDirectEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component))
    (hx : CanonicalStableRawOwnerStableStep
      ends m j k l zero hloop hjk hkl hk0 p hno x.1.1.1)
    (hy : CanonicalStableRawOwnerStableStep
      ends m j k l zero hloop hjk hkl hk0 p hno y.1.1.1)
    (htarget : (canonicalStableRawExceptionalEdgeNext
        ends m j k l zero hloop hjk hkl hk0 p hno x.1.1.1).target =
      (canonicalStableRawExceptionalEdgeNext
        ends m j k l zero hloop hjk hkl hk0 p hno y.1.1.1).target) :
    canonicalStableRawSelfBase ends m j k l zero hloop hjk hkl hk0 p
        x.1.1.1.source =
      canonicalStableRawSelfBase ends m j k l zero hloop hjk hkl hk0 p
        y.1.1.1.source := by
  let ownerX := canonicalStableRawReferenceOwner
    ends m j k l zero hloop hjk hkl hk0 p x.1.1.1
  let ownerY := canonicalStableRawReferenceOwner
    ends m j k l zero hloop hjk hkl hk0 p y.1.1.1
  have howner : ownerX = ownerY := by
    apply Subtype.ext
    calc
      ownerX.1 = canonicalStableRawPreferredRightBase ends m j k l zero
          hloop hjk hkl hk0 p
            (canonicalStableRawExceptionalEdgeNext
              ends m j k l zero hloop hjk hkl hk0 p hno x.1.1.1).target :=
        hx.2.symm
      _ = canonicalStableRawPreferredRightBase ends m j k l zero
          hloop hjk hkl hk0 p
            (canonicalStableRawExceptionalEdgeNext
              ends m j k l zero hloop hjk hkl hk0 p hno y.1.1.1).target := by
        rw [htarget]
      _ = ownerY.1 := hy.2
  calc
    canonicalStableRawSelfBase ends m j k l zero hloop hjk hkl hk0 p
        x.1.1.1.source =
      canonicalStableRawSelfBase ends m j k l zero hloop hjk hkl hk0 p
        ownerX :=
      canonicalStableRawReferenceOwner_sourceBase
        ends m j k l zero hloop hjk hkl hk0 p x.1.1.1 x.1.1.2.2
    _ = canonicalStableRawSelfBase ends m j k l zero hloop hjk hkl hk0 p
        ownerY := congrArg _ howner
    _ = canonicalStableRawSelfBase ends m j k l zero hloop hjk hkl hk0 p
        y.1.1.1.source :=
      (canonicalStableRawReferenceOwner_sourceBase
        ends m j k l zero hloop hjk hkl hk0 p y.1.1.1 y.1.1.2.2).symm




theorem card_le_canonicalRawRelationNeighborhood_of_stableCollisionTargetBlock
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p))
    (A : Finset (StatMech.FrontierA.crossCollision
      (canonicalStableRawComponentSelfEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component)
      (canonicalStableRawComponentDirectEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component)))
    (x₀ : StatMech.FrontierA.crossCollision
      (canonicalStableRawComponentSelfEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component)
      (canonicalStableRawComponentDirectEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component))
    (hx₀ : x₀ ∈ A)
    (hstable : ∀ x ∈ A, CanonicalStableRawOwnerStableStep
      ends m j k l zero hloop hjk hkl hk0 p hno x.1.1.1)
    (htarget : ∀ x ∈ A,
      (canonicalStableRawExceptionalEdgeNext
          ends m j k l zero hloop hjk hkl hk0 p hno x.1.1.1).target =
        (canonicalStableRawExceptionalEdgeNext
          ends m j k l zero hloop hjk hkl hk0 p hno x₀.1.1.1).target) :
    ∃ sources : Finset ↑(canonicalRawCommonClosure ends m j k l zero p),
      (∀ c, c ∈ sources ↔ ∃ x ∈ A, x.1.1.1.source = c) ∧
      sources.card = A.card ∧
      A.card ≤
        (StatMech.FrontierA.finiteRelationNeighborhood
          (CanonicalRawGateRelated ends m j k l zero p)
          (sources.map ⟨Subtype.val, Subtype.val_injective⟩)).card := by
  classical
  let collisionSource := fun x : StatMech.FrontierA.crossCollision
        (canonicalStableRawComponentSelfEmbedding
          ends m j k l zero hloop hjk hkl hk0 p hno component)
        (canonicalStableRawComponentDirectEmbedding
          ends m j k l zero hloop hjk hkl hk0 p hno component) =>
      x.1.1.1.source
  let sources := A.image collisionSource
  have hsourceInjective : Function.Injective collisionSource :=
    canonicalStableRawComponentCrossCollision_source_injective
      ends m j k l zero hloop hjk hkl hk0 p hno component
  have hsourcesCard : sources.card = A.card :=
    Finset.card_image_of_injective A hsourceInjective
  have hfiber : ∀ c ∈ sources,
      canonicalStableRawSelfBase ends m j k l zero
          hloop hjk hkl hk0 p c =
        canonicalStableRawSelfBase ends m j k l zero
          hloop hjk hkl hk0 p (collisionSource x₀) := by
    intro c hc
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hc
    exact canonicalStableRawStableCrossCollision_selfBase_eq_of_nextTarget_eq
      ends m j k l zero hloop hjk hkl hk0 p hno component x x₀
        (hstable x hx) (hstable x₀ hx₀) (htarget x hx)
  refine ⟨sources, ?_, hsourcesCard, ?_⟩
  · intro c
    simp only [sources, collisionSource, Finset.mem_image]
  · rw [← hsourcesCard]
    exact card_le_canonicalRawRelationNeighborhood_of_selfBaseFiber
      ends m j k l zero hloop hjk hkl hk0 p sources
        (collisionSource x₀) hfiber


theorem exists_canonicalRawRelationNeighborhoodEmbedding_of_stableCollisionTargetBlock
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p))
    (A : Finset (StatMech.FrontierA.crossCollision
      (canonicalStableRawComponentSelfEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component)
      (canonicalStableRawComponentDirectEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component)))
    (x₀ : StatMech.FrontierA.crossCollision
      (canonicalStableRawComponentSelfEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component)
      (canonicalStableRawComponentDirectEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component))
    (hx₀ : x₀ ∈ A)
    (hstable : ∀ x ∈ A, CanonicalStableRawOwnerStableStep
      ends m j k l zero hloop hjk hkl hk0 p hno x.1.1.1)
    (htarget : ∀ x ∈ A,
      (canonicalStableRawExceptionalEdgeNext
          ends m j k l zero hloop hjk hkl hk0 p hno x.1.1.1).target =
        (canonicalStableRawExceptionalEdgeNext
          ends m j k l zero hloop hjk hkl hk0 p hno x₀.1.1.1).target) :
    ∃ sources : Finset ↑(canonicalRawCommonClosure ends m j k l zero p),
      (∀ c, c ∈ sources ↔ ∃ x ∈ A, x.1.1.1.source = c) ∧
      Nonempty (↑A ↪
        ↑(StatMech.FrontierA.finiteRelationNeighborhood
          (CanonicalRawGateRelated ends m j k l zero p)
          (sources.map ⟨Subtype.val, Subtype.val_injective⟩))) := by
  classical
  obtain ⟨sources, hsources, _, hcard⟩ :=
    card_le_canonicalRawRelationNeighborhood_of_stableCollisionTargetBlock
      ends m j k l zero hloop hjk hkl hk0 p hno component A x₀ hx₀
        hstable htarget
  refine ⟨sources, hsources, ?_⟩
  apply Function.Embedding.nonempty_of_card_le
  simpa only [Fintype.card_coe] using hcard

end StatMech.GrahamGHS.FourColor
