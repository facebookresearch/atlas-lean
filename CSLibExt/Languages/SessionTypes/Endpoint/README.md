# Polarized endpoint continuation over canonical π

This directory is a project-authored continuation of the same-repository
finite session development in [`SessionTypes/Basic.lean`](../Basic.lean),
[`Communication.lean`](../Communication.lean) and [`Progress.lean`](../Progress.lean),
with its [public PR #946 source lineage](https://github.com/facebookresearch/atlas-lean/pull/946).
It builds on [`PiCalculus/Basic.lean`](../../PiCalculus/Basic.lean) and
[`PiCalculus/Scoping.lean`](../../PiCalculus/Scoping.lean), without introducing
another process execution relation or name-scoping predicate. The finite
passive-name APIs remain unchanged.

## Mathematical sources and adaptation boundary

* Kohei Honda, Vasco T. Vasconcelos and Makoto Kubo, **Language Primitives and
  Type Discipline for Structured Communication-Based Programming**, ESOP 1998,
  LNCS 1381, pp. 122–138. [Primary paper](https://filipendule.github.io/mgs/honda.vasconcelos.kubo.pdf).
  Section 4.2 motivates unbounded sessions; Section 4.3 describes delegation
  using throw/catch; Definition 5.1 and Section 5 give dual protocols and finite
  partial typing maps. The paper explicitly interprets recursive type equality
  as equality of regular trees. These are conceptual sources, not a claim that
  Atlas ports the paper's complete calculus or metatheorems.
* Ornela Dardha and Simon J. Gay, **A New Linear Logic for Deadlock-Free
  Session-Typed Processes**, FoSSaCS 2018, LNCS 10803, pp. 91–109,
  [doi:10.1007/978-3-319-89366-2_5](https://link.springer.com/chapter/10.1007/978-3-319-89366-2_5).
  The abstract and Sections 1–2 distinguish cyclic process connectivity from
  cyclic communication dependencies and motivate priority annotations. Atlas's
  current `GuardMin` is a project-specific natural-number ordering predicate,
  not a port of PLL/PCP or its cycle-elimination/deadlock-freedom theorem.
* The runtime substrate cites Milner, Parrow and Walker, **A Calculus of Mobile
  Processes**, Information and Computation 100 (1992), in the canonical π
  module. That module owns `Name`, `Proc`, `Cong`, `Select` and `Step`.

The primary paper passages above were checked before citing them. No Lean
proof here is represented as a transcription of a published full-session
metatheorem. The custom model below differs from the papers in runtime
binders, payload annotations and static priorities; this is not a completed
port of their full calculi.

## Model differences

* A runtime restriction binds **one physical π name**, represented by the
  existing de Bruijn binder. A linear key adds a positive or negative role;
  both opposite roles can refer to that same physical name. This is different
  from a runtime calculus allocating two separately named endpoints `νab`.
* Ownership is Mathlib `Finmap`, with unique polarized keys and disjoint
  parallel splitting. Unrestricted passive-name scope is the ambient binder
  depth. Unrestricted shared-service typing is a separate unfinished extension.
* Messages are unary existing π names. Protocol constructors distinguish
  passive-name data from a linear endpoint payload, whose role, rank and
  protocol accompany the capability in typing, not runtime syntax. Sending
  erases the payload key; linear input adds one receive-bound role. Passive
  input adds no subject capability.
* Protocols include explicit finite constructors and closed finite graph
  cursors. Every graph edge follows a communication node; no silent recursive
  edge exists. Unfolding is total and duality reverses the subject and its
  continuation while retaining the payload capability's orientation.
* **The original typing, balance and payload checks still use syntactic protocol equality.**
  `Protocol.TreeEquiv` gives actual guarded regular-tree equivalence through
  canonical CSLib strong bisimilarity over a type-observation LTS. Its labels
  distinguish input/output, endpoint role/rank and payload/continuation branches.
  It equates different graph presentations and finite/graph presentations of
  the same tree, with exact head characterization and duality laws. This LTS
  observes type codes only; it is not another process execution calculus.
  Conversion-enabled typing, balance and payload checks are a separate layer;
  the original syntactic checks have not silently become semantic checks.
  Actual recursive process preservation/progress is not claimed.
* `GuardMin` orders every other active owned key after a guard using natural
  numbers. Repeated use of the **same endpoint key** is exempt; its **opposite
  role** is not exempt even when the physical name is identical. An active
  endpoint being transferred is still owned before transfer and is included.
  `RankedType` adds this order to every communication guard. Its Step
  preservation at compatible interfaces and global completed-or-Step theorem
  for balanced interfaces are proved below.
* The initial typing fragment excludes `sum` and `repl` by a proved invariant
  under every existing `Cong`/`Step` constructor. This exclusion does not
  implement recursive processes. Recursive services must separately justify
  actual `repl_unfold`, no captured linear capabilities and a syntactic offered
  trigger invariant.

## Semantic regular-tree equality boundary

Honda, Vasconcelos and Kubo's Definition 5.1 regards recursive types as regular
trees and defines equality through that representation, rather than recursive
syntax identity. `Protocol.TreeEquiv` implements this convention for our
existing guarded finite graph codes. The canonical substrate is CSLib's
`LTS.HomBisimilarity`, with checked head/branch correspondence as the proof
interface. No new axiom or graph-pointer equality defines the relation.

The annotation extension is project-specific: endpoint payload role and
natural rank must match literally, while payload protocol and continuation
protocol are compared as separate trees. Subject duality flips direction and
only dualizes the continuation; the payload's independent orientation and
role/rank metadata are preserved. These unary payloads, annotations and
finite graph cursor representation are not a claimed literal port of the
source's richer sort, choice and recursive syntax. Semantic equivalence is
proved independently of the unchanged syntactic typing judgements. The
`Conversion.HasType` layer below adds semantic payload comparison and
full canonical congruence invariance and reduction preservation at initially
semantically compatible interfaces. Ranked conversion progress
is also proved; actual recursive process runtime remains unfinished.

## Conversion typing and safety

`Conversion.HasType` has seven syntax-directed rules over the existing raw
`Context`, `Capability` and canonical π syntax. It reads actual unfolded heads,
retains disjoint parallel ownership and exact dual-pair restriction binding,
and requires actual completion at nil. Endpoint output permits regular-tree
equivalence between the advertised payload and the actual owned slot, but
keeps the slot's role and capability rank literal. Input installs the code
advertised by its head. `Capability.Equivalent` separately requires equal
capability ranks; protocol equivalence does not imply that equality.
`Conversion.Compatible` compares actual peer ranks and dual protocol trees.

`Conversion.HasType.of_raw` is a proved seven-rule embedding, not inheritance
of the old substitution or progress theorems. `Conversion.one_action_tail`
proves local conversion for a one-send/completed-tail receiver. Tests transfer
an owned graph code equivalent but unequal to the advertised finite code,
retain its raw value and rank, and use the received name as a subject in an
actual second canonical Step with a third thread. Both payload orientations,
raw rejection at the same interface, and wrong role/rank/tree/peer cases are
checked. The general preservation theorems also consume congruence-framed
transfer and received-subject Steps, including actual nested restrictions.

`Conversion.HasType.retype` transports arbitrary seven-rule derivations
across `ContextEquivalent` at the same process and ambient depth, in both
directions. Matching lookups retain the exact domain and capability ranks,
while protocol codes may change by tree equivalence. The target parallel split
is derived by filtering actual target bindings to the source child domains;
it is not a caller premise. Lift, bind, completion, scope and semantic peer
compatibility are preserved.

`Conversion.HasType.rename`, `lift` and `swap` have separate seven-rule
transport proofs, using canonical key/name equations rather than applying raw
typing theorems to the new judgement. General endpoint substitution retypes
only the expected received capability and then transports its physical name;
it inserts the actual owned payload code and rank. Split ownership derives
freshness for the exact key and permits its opposite-role physical alias.
Passive substitution adds no capability.

For an initially semantically compatible disjoint typed interface, literal
passive/endpoint head preservation returns typed residuals at exactly two
subject insertions. The receiver's actual continuation code is
retained, with semantic dual-tail equivalence rather than syntactic equality.
Both payload branches, roles and ranks are exposed. Tests use unequal sender
and receiver codes and refute the old literal peer-lookup premise at that
semantic source, so the raw `DualAdvance` relation is not silently reused.

`Conversion.HasType.cong_iff` preserves the exact context and depth across
all sixteen canonical Cong constructors. Completed-resource weakening and
absence-based erasure support both scope directions; completion is actual
unfolded done, not literal code equality. The unchanged seven-rule judgement
still excludes choice and replication by derived finite syntax.

`Conversion.SemanticAdvance` records actual old sender/peer lookups, literal
capability-rank agreement, semantic duality and actual matching send/receive
heads. Payload branches are independently equivalent. The target is exactly
two insertions with the actual sender and receiver continuation codes. It
preserves domain, ranks, scope and frames. An initially semantically compatible
interface retains compatibility; an initially semantically balanced interface
retains balance.
It has no process, Step, typing or progress fields and does not require an
externally owned payload slot: the payload may be private behind a binder.

`Conversion.HasType.subject_reduction` takes typing and initial semantic
compatibility and covers all five canonical Step constructors. Its residual
is typed and compatible at the unchanged map or one exact semantic advance.
The balanced corollary supplies compatibility from `Conversion.Balanced`.
Private projection distinguishes an internal chosen pair from an external
advance with unchanged private pair. Original literal duality of the chosen
private pair forces literal continuation duality; semantic source duality
alone cannot justify the raw `DualAdvance` peer premise. Empty-interface and
finite-reachability safety corollaries retain exact empty ownership, not a
progress, termination or fair-liveness claim.

`Conversion.RankedType` mirrors all seven conversion rules, adding the same
static `GuardMin` check to each input/output. The actual active payload is
checked before transfer; same-name opposite roles count as other keys, and
only an actual unfolded terminal is ignored. Erasure to conversion typing
and the raw-ranked bridge are explicit seven-case proofs, not inherited
preservation theorems. General equivalent-context retyping derives domain,
cap-rank and active/terminal invariance and retains every guard.

New ranked proofs cover name transport, actual-value substitution, completed
resources, bidirectional scope, all sixteen Cong cases and all five Step
cases. Ranked reduction requires initial semantic compatibility and returns
the same faithful actual-code `SemanticAdvance`, including exact private
projection, frames and semantic balance.

`Conversion.RankedType.progress_balanced` proves genuine global progress at
arbitrary passive-name depth and semantic-balanced interfaces, including
disconnected networks. It derives normalization internally, selects among
all active owned keys, proves the equal-rank semantic peer belongs to a
different guard leaf, and derives an actual canonical Step or process
congruence to nil. It assumes no caller frontier, ready pair, normal form,
Step or consistent raw representative. Empty-interface and finite-reachable
progress use the new full ranked preservation theorem.

Consumers have different advertised/owned/peer codes with carrier5/payload11,
explicit guard proofs, actual delegation and received-subject steps, nested
private scope/swap, disconnected completed frames, and a genuinely sequential
central actor on rank2 then rank4. Cyclic waits and same-physical opposite-role
self-waits are rejected by the unchanged static rank discipline.

Actual recursive processes/shared services, recursive preservation and
qualified recursive progress remain open. Regular type graphs do not make
these finite π processes recursive, and no termination or fairness is claimed.

## Proof lineage and integration

The original finite development and its cyclic-wait fixture are available in
[Atlas PR #946](https://github.com/facebookresearch/atlas-lean/pull/946) at the
same-repository path
[`CSLibExtTest/Languages/SessionTypes/CyclicTests.lean`](../../../../CSLibExtTest/Languages/SessionTypes/CyclicTests.lean).
Its Lean test declarations are private, but the source is public. The
continuation's cyclic fixture preserves that mathematical example and cites
this lineage; it does not replace or edit the finite APIs. `FiniteBridge`,
`FiniteContext`, `FiniteTyping` and `BinaryBridge` embed the public finite
protocols and derivations, including both endpoint orientations.

Generic binder algebra is provided in this endpoint subtree and uses the
existing canonical π scoping definitions. No namespace aliases or competing
scoping definitions are introduced.

## Syntax-directed priority refinement

`RankedType` refines exactly the current seven `HasType` rules. Each input or
output guard requires `GuardMin` in its pre-action ownership context: its rank
is strictly below every **other active polarized key**. An active delegated
payload is still owned there and is checked. The opposite role of the same
physical name is a different key, not an exemption. A completed capability is
ignored only when its protocol actually unfolds to `done`. Sequential reuse of
exactly the same key is permitted at the same static rank.

`RankedType.hasType` forgets only the guard inequalities. `RankedType.rename`
and `RankedType.lift` preserve the whole refinement under capture-safe physical
name maps, with injectivity on owned keys and all binder/payload positions.
Neither the judgement nor its premises stores a reduction, enabled edge,
progress result or preservation result.

The Dardha–Gay primary source above motivates checking genuine inter-channel
dependencies with priorities (Section 2, priority laws). This is a **custom
project guard model**, not PCP/PLL or an asynchronous calculus port: we retain
canonical synchronous one-name π binders with role keys, static natural ranks,
the same-key reuse exemption, passive-name actions and the existing finite
protocol/ownership representation. In particular, the source's action-level
priority discipline and two-endpoint restriction syntax are not identified
with this refinement. `RankedType.cong_iff` preserves the refinement under
all canonical congruences, including completed-role scope reallocation and
all four roles in nested restriction swapping. For an initially compatible
interface (`Compatible Δ`), `RankedType.subject_reduction` preserves this
refinement and compatibility across every canonical Step, with zero or one
actual external dual-subject advancement. The balanced corollary derives
compatibility from `Balanced Δ`; the empty-interface corollary derives it
from `balanced_empty`. The private projection retains a real old-to-new
bound-pair `DualAdvance`, not merely an arbitrary equal-rank capability.
Global ranked process-level progress is proved by `RankedType.progress_empty`:
a closed finite ranked network is congruent to nil or has an actual canonical
Step, at arbitrary ambient passive-name depth. The stronger
`RankedType.progress_balanced` covers arbitrary balanced interfaces, including
disconnected networks. A derived normalization
(`RankedType.frontier_normal`) exposes every unguarded restriction in an outer
binder tower around a parallel input/output frontier, retaining ranked typing
and exact ownership. Its frontier predicates contain syntax only, not an
enabled-pair or progress witness. `GuardFrontier.progress` proves that ANY
balanced ranked guard frontier is congruent to nil or has an actual canonical
Step. Its minimum ranges over all active owned roles; opposite same-rank keys
are derived to be distinct guard leaves. It admits disconnected frontiers too.
All private channels are tracked while lifting that result through the derived
outer restriction tower. An empty external context is never used as process
completion. `RankedType.reachable_progress` gives the same progress alternative
at every finitely reachable canonical state; this is not a termination or
fair eventual-liveness theorem.

The static rank discipline is deliberately narrower than per-action priority
systems. For example, the safe interleaving “send on e; send on d; receive on e”
while both sessions remain live would require both `rank e < rank d` and
`rank d < rank e`, so this refinement rejects it. The same ownership process
may still be admitted by plain `HasType`. Progress here is
for the `RankedType` fragment, not a classification of all deadlock-free
processes or all PCP/Kobayashi-typable processes.

## Checked capabilities and unproved extensions

The checked prerequisites include role/key identity, unique finite ownership,
binder-aware typing transport, literal linear subject substitution with
freshness derived from splitting, finite API bridges, graph unfolding/duality,
and exact head-communication preservation for both message kinds at compatible
interfaces. Consumers
exercise actual ν-bound synchronization and a connected three-thread delegated
subject, nested capture, opposite-role aliases, the two-channel wait and a
same-name opposite-role self-wait.

The current seven-rule `HasType` has full canonical `Cong` typing invariance
(`HasType.cong_iff`), including exact bidirectional scope and nested restriction
swap. Choice and replication are excluded by a property derived from this
judgement; congruence for a future recursive-service judgement remains open.
Faithful head results record the actual send head, payload kind and continuation;
dual subject advancement preserves the key domain, initial compatibility and
initial balance.
`HasType.subject_reduction` requires a typed source and an initially compatible
interface (`Compatible Δ`). For every canonical `Step`, it returns a typed
residual with a compatible interface, unchanged or advanced by one actual
`DualAdvance`, never an arbitrary map or a sequence of unobserved updates.
The balanced corollary obtains compatibility from `Balanced Δ`; the
empty-interface corollary uses `balanced_empty.compatible`. Internal communication may advance a
ν-bound pair without changing the external interface. This is not subject
reduction for a future recursive-service judgement.

Compatibility is an additional interface hypothesis, not a consequence of
plain or ranked typing. For example, singleton threads on opposite roles of
one free physical name can have matching send/receive heads at ranks one and
two. They are plain- and ranked-typable and can communicate, but their combined
interface is incompatible because dual capabilities must have equal ranks.

The following are **not established by those prerequisites**:

1. Subject reduction and congruence for an actual recursive-service extension
   of the current finite-process judgement.
2. Finite termination or fair eventual completion. The proved completion branch
   is `Cong p nil`, with an actual Step otherwise; it is not a scheduler theorem.
3. Guarded recursive process/shared-service representation in existing π
   replication/trigger code, no captured linear resources, recursive subject
   reduction and qualified recursive progress.

No progress premise contains an enabled-edge witness or a preproved progress
field. No fair eventual liveness or recursive termination is claimed. Logical
finite-map/proof infrastructure uses `propext`, `Quot.sound` and
`Classical.choice`; no constructive typechecker or scheduler is claimed.
