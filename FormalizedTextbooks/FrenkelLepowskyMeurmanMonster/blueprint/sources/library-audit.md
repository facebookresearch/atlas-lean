# Pinned library audit

## Revision and evidence standard

The audit was performed with the Lean 4.34.1 toolchain. The pinned Mathlib revision is
[d13f23b723b8a846827a245b89c10fc7d3f11612](https://github.com/leanprover-community/mathlib4/tree/d13f23b723b8a846827a245b89c10fc7d3f11612),
as recorded in the repository's lake-manifest.json.

"Inspected" below means the definition or theorem signature and relevant source
were read. It does not claim a new compiled bridge, a full transitive proof audit,
or suitability for every FLM convention. No roadmap article asserts formalized
status or upstream completion on the strength of these searches.

## Inspected foundations

| Area | Inspected declaration and source | Application and remaining work |
| --- | --- | --- |
| Group extension | [GroupExtension and GroupExtension.conjAct](https://github.com/leanprover-community/mathlib4/blob/d13f23b723b8a846827a245b89c10fc7d3f11612/Mathlib/GroupTheory/GroupExtension/Defs.lean) | Records an injective inclusion, surjective projection, and image/kernel equality; gives conjugation on the normal subgroup. Use for the intended extension without assuming a splitting. It does not construct the FLM group. |
| Central extension | `GroupExtension.IsCentral` | Centrality means the projection kernel lies in the center. Relevant to the extension defining Q, not a claim that Q is central in H. |
| Commutator descent | `GroupExtension.IsCentral.commutator_eq_of_rightHom_eq` | With central kernel, the commutator depends only on quotient images. This is a candidate foundation for the quotient pairing; its field-valued bilinearity, nondegeneracy, squares, and plus type still need an appropriate bridge. |
| Cocycle construction | `NormalizedCocycleExtension.NormalizedCocycle`, `extension`, and `isCentral` | Builds a central extension from a normalized multiplicative cocycle with trivial action. Candidate infrastructure for Q; not a construction of the larger noncentral extension by Co1. |
| Frattini subgroup | [frattini](https://github.com/leanprover-community/mathlib4/blob/d13f23b723b8a846827a245b89c10fc7d3f11612/Mathlib/GroupTheory/Frattini.lean) | Existing definition as the infimum of maximal subgroups; audit the finite-p-group API before planning extra lemmas. |
| Simple group | [IsSimpleGroup](https://github.com/leanprover-community/mathlib4/blob/d13f23b723b8a846827a245b89c10fc7d3f11612/Mathlib/GroupTheory/Subgroup/Simple.lean) | Includes nontriviality and the normal-subgroup dichotomy. No Monster-specific simplicity proof was found. |
| Characteristic-two forms | [QuadraticMap, polar_add_left, polar_smul_left, and polarBilin](https://github.com/leanprover-community/mathlib4/blob/d13f23b723b8a846827a245b89c10fc7d3f11612/Mathlib/LinearAlgebra/QuadraticForm/Basic.lean) | The inspected polar-bilinearity API works over a commutative ring without assuming two invertible. In contrast, polarBilin_injective requires IsUnit (2 : R), so cannot be used over F2. The FLM quadratic model and plus-type classification still need auditing. |

These APIs can reduce background work. In particular, do not replace the
existing extension definition with an ad hoc tuple of group data.

## Candidate files needing further inspection

The pinned Mathlib tree contains commutator, subgroup-center, index,
dihedral/quaternion-group, quadratic-isometry, and vertex-operator modules.
Their presence is a search lead, not proof that the full extraspecial, lattice,
representation, or VOA infrastructure exists. Exact declarations and assumptions
must be checked when the source proof fixes the needed statements.

The repository also has group-extension homomorphism and pullback modules.
Review those if the construction requires a diagram of extensions.

## Searches and limitations

- Filename searches in the checked-out repository for Monster, Leech, Griess,
  extraspecial, and Golay returned no matching paths.
- Content searches for extraspecial, Griess, Leech lattice, Conway group,
  Monster group, Golay code, and vertex operator algebra in the relevant
  mathematical libraries found a Leech-lattice mention in
  `CKMRVInterpolationWanted`.
  Reading it showed a Fourier-interpolation wishlist, not a construction of
  the Leech lattice or its automorphism group.
- Searches of the pinned Mathlib tree located the generic foundations above;
  no specially named Monster, Leech, Golay, or extraspecial module was found.
- The GitHub directory linked in the original discussion,
  [OpenAI's VertexAlgebra directory](https://github.com/openai/math/tree/main/lean/OAI/RepresentationTheory/VertexAlgebra),
  was listed, but its declarations and transitive imports were not audited.
  Directory names are insufficient evidence for reusable FLM infrastructure.
- A targeted open-PR search for Monster, FLM, extraspecial, and Leech returned
  no results during this audit. This is not an exhaustive search of all branches,
  issues, or external repositories.

These bounded searches do not establish absence from Meta's entire internal
library, an unmerged branch, or code using different names. Further targeted
searches must follow the source audit's exact mathematical requirements.

## Next audit deliverable

For each source prerequisite, record its exact formal statement, the best
existing declaration with compatible assumptions, and either a demonstrated
reuse path or the remaining gap. Freeze any external code revision before
adoption. Do not turn a filename hit into formalization status.
