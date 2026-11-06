# FLM Monster milestone statements: gap inventory

Skeleton with T1–T6 `sorry` proof bodies (no endpoint is proved), proved
subgroup framework laws, and a genuine coordinate extraspecial model whose
FLM comparison is pending. This file enumerates every hole so future work
cannot silently prove degenerate formulations.

Lean files (namespace `FormalizedTextbooks.FrenkelLepowskyMeurmanMonster`):

* [Definitions.lean](Definitions.lean) — shared construction interfaces.
* [Milestones.lean](Milestones.lean) — the six endpoint theorem statements.

Module style follows the repository convention (`module` header, `public
import`, `@[expose] public section`). Theorem names are mathematical
snake_case; the T1–T6 labels appear in docstrings, not in declaration names.

## Six proof holes (all in `Milestones.lean`)

| Theorem name | Milestone | Statement | Status |
| --- | --- | --- | --- |
| `local_subgroup_structure` | T1 | extraspecial `Q`, bijective raw `centerMap`, exactness, faithful product/form-preserving action | `sorry`, unproved |
| `extra_symmetry_preserves_griess` | T2 | `sExtra` preserves product/form; `G ≤ griessAutSubgroup` | `sorry`, unproved |
| `generated_group_finite` | T3 | `Finite ↥G`, no finiteness hypothesis | `sorry`, unproved |
| `generated_group_order` | T4 | `Nat.card ↥G` equals the Monster numeral | `sorry`, unproved |
| `generated_group_simple` | T5 | `IsSimpleGroup ↥G` (includes nontriviality) | `sorry`, unproved |
| `generated_group_iso_classical_monster` | T6 | `Nonempty (classicalMonster ≃* ↥G)` | `sorry`, unproved |

`#print axioms` on all six reports `sorryAx` (plus the repository-permitted
`propext`, `Classical.choice`, `Quot.sound`). No proof is complete.

## Source-binding holes (all in `Definitions.lean`)

Each must be fixed to the audited FLM formula/passage before endpoint proofs
are meaningful. No source excerpts have been read for this PR; the FLM
passage checklist is at [blueprint/sources/flm.md](blueprint/sources/flm.md).
These signatures alone do NOT fix FLM: while the entries below are holes,
proving the six theorems would prove nothing about the Monster.

| Label | Definition name(s) | What is missing |
| --- | --- | --- |
| S-GriessProd | `griessProd` | FLM Griess product formula + normalization |
| S-GriessForm | `griessForm` | FLM invariant bilinear form + normalization |
| S-Leech | `LeechLattice` | WHICH `ℤ` submodule of `Fin 24 → ℝ` (ambient type fixed). Rank 24, integrality, evenness, unimodularity, minimum norm are unresolved properties, not settled by the bare submodule type |
| S-Q | `Q`, `instGroupQ` (model genuine; FLM comparison pending) | Concrete plus-type coordinate model (`qBeta`/`qBilin`/`qCocycle`/`Q`/`instGroupQ`) is genuine with proved group laws via `NormalizedCocycleExtension`. PENDING: the comparison isomorphism between this model and the FLM extraspecial group |
| S-H | `H`, `instGroupH` | FLM extension group type + laws |
| S-inclQ | `inclQ` | FLM inclusion formula (raw map only) |
| S-projH | `projH` | FLM projection formula (raw map only) |
| S-rho | `rhoLocal` | FLM local action formulas (raw map into ambient GL) |
| S-sExtra | `sExtra` | FLM extra symmetry + inverse (raw ambient-GL element) |
| S-qQuotHom | `qQuotHom` (model projection genuine; FLM identification pending) | Coordinate projection (`projHom` of the model) is genuine. PENDING: identifying the FLM quotient with this projection (kernel/range are T1 conclusions) |
| S-centerMap | `centerMap` | FLM `Z(Q) → F₂` identification (raw hom only; bijectivity is a T1 conclusion) |
| S-squareQuad | `squareQuad` (model diagonal genuine; squares link pending) | Coordinate diagonal `v ↦ β(v,v)` via `BilinMap.toQuadraticMap` is genuine. PENDING: the proof that this form is the squares-induced form via S-centerMap (see T1 link) |
| S-classicalMonster | `classicalMonster`, `instGroupClassical` | independent classical model + comparison route (UNRESOLVED; must not become `G`) |

Former hole labels S-LeechIsom, S-signs, and S-centerIso are retired: the
isometry/signs carriers and the center map shape are now genuine or raw
definitions (see below). Their values still depend on S-Leech and S-centerMap
binding respectively.

## Framework-law holes: all discharged (in `Definitions.lean`)

Former holes F-Aut*, F-LeechIsom*, F-signs*, F-signsNormal, F-centerNormal
are now proved, with no `sorry`:

* F-Aut* (`griessAutSubgroup`): `one_mem'`, `mul_mem'`, `inv_mem'` proved
  from the specified product/form, ahead of S-GriessProd/S-GriessForm binding.
* F-LeechIsom* (`leechIsomSubgroup`): `one_mem'`, `mul_mem'`, `inv_mem'`
  proved for any `LeechLattice`, ahead of S-Leech binding.
* F-signs* (`signsSubgroup`): `one_mem'`, `mul_mem'`, `inv_mem'` proved for
  `{±1}` by identity/negative-identity computation.
* F-signsNormal (`signsNormal`): normality proved by direct conjugation
  computation.
* F-centerNormal (`centerQNormal`): via the Mathlib normal-center instance
  (`Subgroup.instNormalCenter`); fixes the name used by `Q ⧸ centerQ`.

## Explicit definitions and completed supporting laws

The entries below have no local proof or data holes. Some still depend on
unfinished source data, such as `LeechLattice` or the Griess product/form;
they are not all transitively free of `sorryAx`.

* `GriessSpace` (carrier `Fin 196884 → ℝ`), `IsGriessAuto`.
* `stdPairingFun` (explicit `Σᵢ xᵢ * yᵢ` on `Fin 24 → ℝ`), `IsLeechIsom`
  (pairing preservation plus onto-`LeechLattice` membership equivalence),
  `leechIsomSubgroup` (carrier plus proved closure laws).
* `IsSign` (identity or pointwise negative identity), `signsSubgroup`
  (carrier plus proved closure laws), `signsNormal`, `centerQNormal`.
* `Co1` (quotient shape `Isom(Λ)/{±1}`), `centerQ`,
  `G` (`Subgroup.closure`, no conclusions
  built in), `hyperbolicFun` (explicit `Σᵢ aᵢ * bᵢ`).
* Coordinate extraspecial model: `qBeta` (explicit `Σᵢ vᵢ * w_{i+12}`),
  `qBeta_*` bilinearity lemmas, `qBilin`, `qCocycle` (proved normalized
  cocycle), `Q` (cocycle extension, nonabelian twisted model — not a direct
  product), `instGroupQ` (proved via `NormalizedCocycleExtension`),
  `qQuotHom` (proved projection), `squareQuad` (diagonal `v ↦ β(v,v)`).
  These coordinate definitions have no `sorryAx` dependency. The
  model-to-FLM comparison is NOT proved (pending S-Q).

The raw `centerMap` is still a source-binding hole, not a hole-free
definition. Its bijectivity is a conclusion of T1.

## Semantic omissions and faithfulness risks

* No splitting of `1 → Q → H → Co1 → 1` is asserted (matches review scope).
* Plus type is stated via a `ZMod 2`-linear iso preserving values against the
  explicit sum formula; the squares link is the T1 equation tying
  `squareQuad` to `g * g` through the raw `centerMap` (whose bijectivity T1
  also concludes). If S-squareQuad were bound to a free form ignoring
  squares, T1's link equation would fail — that is the intended
  non-degeneracy guard. No record or definition assumes `centerMap` is an
  isomorphism before T1.
* T2's first conjunct is a genuine preservation property of the raw element
  `sExtra`, not a typing tautology; T1's preservation conjuncts play the same
  role for `rhoLocal` (which targets ambient GL, not `griessAutSubgroup`).
* The Leech-lattice type fixes only the ambient space. Rank, integrality,
  evenness, unimodularity, and minimum norm remain source-binding work under
  S-Leech; the genuine isometry/signs carriers cannot supply them.
* Provisional real-form convention: only the carrier `Fin 196884 → ℝ` is
  fixed. Basis, complexification, and product/form normalizations are open
  source-audit items shared across workstreams.
* No T7/VOA content is included. The completed infrastructure consists of
  subgroup laws and the coordinate cocycle model; no endpoint is proved.
