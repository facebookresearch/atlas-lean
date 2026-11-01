# FLM Monster milestone statements: gap inventory

Skeleton with T1–T6 `sorry` proof bodies (no endpoint is proved), proved
subgroup framework laws, and a genuine coordinate extraspecial model whose
FLM comparison is pending. This file enumerates every hole so future work
cannot silently prove degenerate formulations.

Lean files (namespace `FormalizedTextbooks.FrenkelLepowskyMeurmanMonster`):

* [Definitions.lean](Definitions.lean) — shared construction interfaces.
* [Milestones.lean](Milestones.lean) — the six endpoint theorem statements.
* [Triality.lean](Triality.lean) — the explicit dictionary-coordinate symmetry and its inverse.
* [LeechBasisData.lean](LeechBasisData.lean) — explicit integral and binary matrix data, with kernel-checked identities.

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

## Remaining source bindings and model comparisons

The remaining placeholders must be fixed to audited FLM formulas/passages,
and the coordinate model must be compared with the FLM construction, before
endpoint proofs establish the intended Monster results. No FLM source excerpts
have been read for this follow-up. Supplementary formulas have been inspected
in Seysen §6.1, §7.4, §8.1, and §9.1, Conway §9–12,
and Basak §1.1; see
[the source record](blueprint/sources/concrete-coordinates.md). The FLM
passage checklist is at [blueprint/sources/flm.md](blueprint/sources/flm.md).
These signatures alone do NOT fix FLM: while the entries below are holes,
proving the six theorems would prove nothing about the Monster.

| Label | Definition name(s) | What is missing |
| --- | --- | --- |
| S-GriessProd | `griessProd` (coordinate construction complete) | Conway §12’s six rules in the fixed dictionary, with bilinearity proved; primary FLM comparison remains pending |
| C-GriessForm | `griessForm` (definition complete) | Explicit diagonal pairing in the Seysen dictionary basis; bilinearity proved. FLM normalization comparison and invariance under the local action remain |
| C-Leech | `LeechLattice` (definition complete) | Explicit Golay congruences and `1 / sqrt 8` embedding, with module laws and exact source-membership equivalence proved. Rank 24 and an actual integer basis and lattice quotient are proved. Evenness, unimodularity, minimum norm, and compatible quadratic coordinates remain theorem obligations |
| S-Q | `Q`, `instGroupQ` (model genuine; FLM comparison pending) | Concrete plus-type coordinate model (`qBeta`/`qBilin`/`qCocycle`/`Q`/`instGroupQ`) is genuine with proved group laws via `NormalizedCocycleExtension`. PENDING: the comparison isomorphism between this model and the FLM extraspecial group |
| S-H | `H`, `instGroupH` (coordinate construction complete) | Explicit orthogonal-normalizer/Co₀ fiber product modulo simultaneous signs; primary FLM comparison remains pending |
| S-inclQ | `inclQ` (coordinate construction complete) | Natural quotient inclusion; injectivity and exactness remain endpoint proofs |
| S-projH | `projH` (coordinate construction complete) | Projection to Co₁ kills simultaneous signs; surjectivity remains an endpoint proof |
| S-rho | `rhoLocal` | FLM local action formulas (raw map into ambient GL) |
| C-sExtra | `sExtra` (definition complete) | Explicit source triality with proved linearity and inverse. Its FLM comparison and product/form preservation remain |
| S-qQuotHom | `qQuotHom`, `qQuotientEquiv` (coordinate data complete; FLM identification pending) | Kernel/range and the induced quotient isomorphism are proved for the coordinate model. PENDING: identifying the FLM quotient with this projection |
| S-centerMap | `centerMap` (coordinate definition complete) | The central coefficient is now a genuine homomorphism with an explicit inverse and proved bijectivity. PENDING: compatibility with FLM through S-Q; no local `sorry` remains here |
| S-squareQuad | `squareQuad` (coordinate diagonal and squares link complete) | `squareQuad_eq_centerMap_square` proves the group-squares link, and `qHyperbolicEquiv_form` proves compatibility with the explicit hyperbolic form. PENDING: transporting these identifications through the FLM comparison S-Q |
| C-classicalMonster | `classicalMonster`, `instGroupClassical` (definitions complete) | Independent Ivanov–Norton presentation reference: centralize the central tree generator in the presented bimonster, then quotient by its cyclic subgroup. Historical recognition requires the presentation theorem and the wreath-product centralizer argument; no recognition axiom or isomorphism to `G` is assumed |

Former hole labels S-LeechIsom, S-signs, and S-centerIso are retired: the
isometry/signs carriers and the center map shape are now genuine or raw
definitions (see below). The isometry/signs definitions now use the explicit coordinate lattice.
The lattice/FLM comparison remains C-Leech. The coordinate center identification is now complete; its FLM
comparison remains under S-Q.

### One remaining construction placeholder

`rhoLocal` still has a `sorry` body. `griessProd` now uses Conway’s six
multiplication rules, transported to the explicit dictionary basis and
extended bilinearly through concrete structure constants.
`H`, `instGroupH`, `inclQ`, and `projH` now use the explicit source fiber product
and its simultaneous-sign quotient, with their laws proved. They are the remaining data/group-law holes;
all six milestone proofs are also unproved. Removing these bodies by using
arbitrary replacements would not formalize the intended construction.

The full Conway article is now available through the public Göttingen scan,
and its multiplication formulas in §12 have been visually inspected. Tits's
public Bourbaki account supplies a second formulation. These formulas still
need to be implemented with compatible lattice quotient, short-vector, and
Schrödinger basis labels. The source record documents the normalization.
The Griess product, local extension, and its two natural maps are constructed.
The local action and its supporting short-label invariance proof remain unfinished.

The local prerequisites now include the explicit Schrödinger representation,
proved faithful and orthogonal, its orthogonal normalizer and actual
conjugation action, and the actual quotient Λ/2Λ with a proved coordinate
linear equivalence. The explicit integer matrix is now proved to be a basis.
The binary frame uses the published cocode and Parker cocycle tables; its
inverse and source Gram identities are checked in the kernel. General
half-norm compatibility and the dictionary representation are still being completed.

## Framework-law holes: all discharged (in `Definitions.lean`)

Former holes F-Aut*, F-LeechIsom*, F-signs*, F-signsNormal, F-centerNormal
are now proved, with no `sorry`:

* F-Aut* (`griessAutSubgroup`): `one_mem'`, `mul_mem'`, `inv_mem'` proved
  from the specified product/form; only the product remains a placeholder.
* F-LeechIsom* (`leechIsomSubgroup`): `one_mem'`, `mul_mem'`, `inv_mem'`
  proved by general submodule laws and now applied to the explicit lattice.
* F-signs* (`signsSubgroup`): `one_mem'`, `mul_mem'`, `inv_mem'` proved for
  `{±1}` by identity/negative-identity computation.
* F-signsNormal (`signsNormal`): normality proved by direct conjugation
  computation.
* F-centerNormal (`centerQNormal`): via the Mathlib normal-center instance
  (`Subgroup.instNormalCenter`); fixes the name used by `Q ⧸ centerQ`.

## Explicit definitions and completed supporting laws

The entries below have no local proof or data holes. Some still depend on
unfinished source data, such as the Griess product;
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

The coordinate `centerMap` is now defined as the central coefficient. Its
homomorphism law uses the proved center characterization, and
`qCenterHom` supplies an explicit inverse. `centerMap_bijective`,
`qQuotHom_ker`, `qQuotHom_surjective`, and `qQuotHom_range` are proved.
`qQuotientEquiv` constructs the actual quotient isomorphism;
`q_square_mem_center` and `squareQuad_eq_centerMap_square` establish the
squares link; `qHyperbolicEquiv` explicitly splits the coordinates and
`qHyperbolicEquiv_form` proves form preservation. All these definitions and
supporting theorems have no `sorryAx` dependency. They concern the coordinate
model, not an audited FLM comparison.

### Exact remaining Lean placeholders

There is **one** `sorry` body in `Definitions.lean`: `rhoLocal`.
The six milestone proof bodies remain unchanged. The model-comparison gaps
above are additional unfinished mathematics, even where the coordinate
objects no longer contain a placeholder.

## Semantic omissions and faithfulness risks

* No splitting of `1 → Q → H → Co1 → 1` is asserted (matches review scope).
* Plus type is stated via a `ZMod 2`-linear iso preserving values against the
  explicit sum formula; the squares link is the T1 equation tying
  `squareQuad` to `g * g` through the raw `centerMap` (whose bijectivity T1
  also concludes). If S-squareQuad were bound to a free form ignoring
  squares, T1's link equation would fail — that is the intended
  non-degeneracy guard. No record or definition assumes `centerMap` is an
  isomorphism as input. Bijectivity is independently proved for the coordinate
  model by constructing an inverse.
* T2's first conjunct is a genuine preservation property of the raw element
  `sExtra`, not a typing tautology; T1's preservation conjuncts play the same
  role for `rhoLocal` (which targets ambient GL, not `griessAutSubgroup`).
* The Leech lattice is now defined by the explicit Golay congruences, and its
  rank is proved to be 24. Integrality, evenness, unimodularity, minimum norm, and the compatible FLM
  quotient identification remain theorem obligations; the isometry/signs
  carriers do not prove them.
* The real carrier, dictionary basis, pairing weights, and triality are
  fixed in Seysen coordinates. The eventual product and local-action formulas
  must use the same basis; their FLM comparison and complexification remain
  source-audit obligations.
* No T7/VOA content is included. The completed infrastructure consists of
  subgroup laws, the coordinate cocycle model and its center/quotient/squares
  identifications, the Golay lattice, dictionary form and triality, and the
  presentation reference; no endpoint is proved.

## Additional complete coordinate and presentation definitions

The Golay generators, `golayEncoder`, and `golayCode` are explicit.
`LeechCongruences`, `leechIntegral`, `leechCoordinateEmbedding`, and
`LeechLattice` have no `sorryAx` dependency.
`leechCongruences_normalize` proves that the common residue can be chosen
as 0 or 1, and `mem_leechIntegral_iff_source` proves equivalence with the
published binary-code membership condition.

`griessForm` uses squared norm 2 on dictionary blocks A/B/C, and squared
norm 1 on diagonals, octad blocks, and signed X/Y/Z blocks.
`Triality.lean` implements the two three-cycles and the octad Fourier/sign
operation. The matrix inverse is certified using the Sylvester Hadamard
construction and a kernel-checked finite row-permutation equality.
Neither `griessForm` nor `sExtra` depends on `sorryAx`.

The classical reference is specified by the Y555 tree, its involution and
Coxeter relators, and `(a b1 c1 a b2 c2 a b3 c3)^10`. The quotient group laws
are supplied by `PresentedGroup` and the proved normality of the cyclic
subgroup inside the chosen centralizer. This construction does not refer to
`G`, the Griess product, or any local-action placeholder. Its identification
with the historical Monster remains a recognition proof, not an assumed axiom.

## Further completed local prerequisites

- `spinRepresentation` explicitly acts by `(-1)^(c+b·t) f(t+a)` on 4096
  binary labels. Its multiplication, inverses, faithfulness, and pairing
  invariance are proved; no local-group or Griess-product hole is used.
- `spinHolomorphSubgroup` is the orthogonal normalizer of the actual Q image.
  `spinConjugation` is induced by conjugation, not supplied as an assumed action.
- `leechIntegral_finrank` proves rank 24. `LeechModTwo` is the actual quotient
  by doubles inside the lattice. `leechModTwoLinearEquiv` is a proved
  equivalence using an integer lattice basis; quadratic compatibility is pending.
- `leechBasisMatrix_gram`, `leechHyperbolicMatrix_inverse`, and
  `leechBasisMatrix_congruences` are finite kernel checks of concrete data.
  They do not yet assert that the matrix columns span the lattice or that
  the binary change of basis preserves the lattice quadratic form.
