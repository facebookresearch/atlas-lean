# Frenkel–Lepowsky–Meurman: finite-group foundations of the Monster

This textbook project plans the finite-group part of the FLM construction:
the subgroup of shape $2_+^{1+24}\!\cdot\mathrm{Co}_1$, the extra symmetry,
and the proofs of finiteness, order, simplicity, and Monster identification.

The adopted reference is Igor Frenkel, James Lepowsky, and Arne Meurman,
*Vertex Operator Algebras and the Monster* (1988), Academic Press,
Pure and Applied Mathematics, volume 134, ISBN 978-0-12-267065-7.
The [source notes](blueprint/sources/flm.md) distinguish this reference from
passages that still need to be obtained and checked.

## Read the roadmap

- [Blueprint overview](blueprint/README.md)
- [1. The local subgroup](blueprint/roadmap/local-subgroup/README.md)
- [2. The extra FLM symmetry](blueprint/roadmap/extra-symmetry/README.md)
- [3. Identifying the Monster](blueprint/roadmap/monster-identification/README.md)
- [Coverage contract](blueprint/coverage/README.md)
- [Library audit](blueprint/sources/library-audit.md)
- [Minimal milestone theorem statements for human review](HUMAN_REVIEW.md)

## Current state and boundary

The finite-group statement skeleton exists as Lean declarations:
[Definitions.lean](Definitions.lean) holds the shared construction
interfaces and [Milestones.lean](Milestones.lean) states the six endpoint
theorems (T1–T6, snake_case names with the T-labels in docstrings). Every
endpoint proof body is `sorry`: no endpoint proof is complete and none is
claimed. The subgroup framework laws are proved, and `Q` is a genuine
concrete plus-type coordinate model (its comparison with the FLM group is
pending, not proved). The complete source/framework hole inventory is in
[GAPS.md](GAPS.md); `#print axioms` on all six theorems reports `sorryAx`
as expected.

Repository-generated collection roots contain no new mathematics beyond
importing the construction, triality, and milestone modules. The selected FLM passages and their
finite-group references have not yet been checked, so these signatures
alone do not fix FLM: the remaining `TODO(S-*)` bindings (Griess product, local extension,
and local maps) and the coordinate/FLM comparisons must be completed before
endpoint proofs establish the intended FLM construction. Supplementary source
formulas have now been inspected and implemented; see
[the coordinate source record](blueprint/sources/concrete-coordinates.md).
Chapter outlines are not a source-verified theorem DAG.
Coverage remains MAPPED for the core areas.

The original `Definitions.lean` and the six unchanged milestone statements
were authored by Muse Code. In the follow-up stacked above PR #6477, Codex
authored the coordinate center/quotient definitions and their supporting
proofs, plus the explicit hyperbolic coordinate equivalence. Codex also authored the
Golay-coordinate lattice, dictionary form and triality, and independent
presentation reference in this continuation. Further work adds the faithful
Schrödinger representation and orthogonal normalizer, the actual lattice
quotient by doubles, and checked integer and binary coordinate data. The collection root is updated
by the repository generator to import `Triality.lean`.

### Coordinate definitions completed in the follow-up

- `centerMap`: the central coefficient, with proved homomorphism law.
- `qCenterHom`: its explicit inverse; `centerMap_bijective` proves bijectivity.
- `qQuotientEquiv`: the actual quotient isomorphism to the 24-bit group;
  the projection's kernel, surjectivity, and range are proved.
- `squareQuad_eq_centerMap_square`: the quadratic form is the central bit
  obtained by squaring, with proved center membership for every square.
- `qHyperbolicEquiv`: the explicit split into two 12-bit blocks, with proved
  preservation of the hyperbolic form.

These definitions and supporting proofs have no `sorryAx` dependency. The
FLM comparison is still pending. One construction placeholder remains
in `Definitions.lean`, listed by name in [GAPS.md](GAPS.md); all six
milestone proofs remain `sorry` and their statements are unchanged.

The local action, moonshine VOA, and VOA generator lifts remain
unimplemented workstreams. The Griess multiplication is now explicit. Their interfaces are recorded in the roadmap. Full VOA automorphism
equality, irreducibility of the 196883-dimensional summand, the character formula,
and genus-zero moonshine are deferred.

Future declarations belong to the project's own namespace, normally
FormalizedTextbooks.FrenkelLepowskyMeurmanMonster. Later promotion of general
results into MathlibExt follows the repository's human-review rules.

## Beginner's glossary

- **Generator:** an element in a collection whose products and inverses produce
  every group element. A **relation** is an equality between products.
- **Order:** the number of elements of a finite group. An element's order is
  instead the least positive power giving the identity.
- **Normal subgroup:** a subgroup preserved by conjugation by every group
  element. A **simple group** is nontrivial and has only the identity subgroup
  and the whole group as normal subgroups.
- **Center:** elements commuting with every group element. A **centralizer**
  consists of elements commuting with a specified element or subgroup.
- **Normalizer:** elements whose conjugation preserves a specified subgroup.
- **Quotient:** the group of cosets of a normal subgroup. A **group extension**
  specifies a group, a normal subgroup, a quotient, and the connecting maps.
- **Extraspecial 2-group:** a finite nonabelian 2-group whose center, commutator
  subgroup, and Frattini subgroup coincide and have order two. The Frattini
  subgroup is the intersection of the maximal proper subgroups.
- **Plus type:** one of two types of extraspecial 2-groups of a given order,
  reflected in the quadratic form obtained from element squares.
- **Griess algebra:** the 196884-dimensional commutative, generally
  nonassociative algebra used in the Monster construction. In the moonshine
  VOA it is the weight-two space with one selected VOA product.
- **Faithful action:** different group elements give different transformations;
  the homomorphism into the automorphism group is injective.

## Suggested first contributions

1. **Source audit:** trace the local-subgroup construction in FLM and record
   exact definitions, theorem locations, and every cited prerequisite. Do this
   before choosing detailed formalization units.
2. **Small extraspecial groups:** study the dihedral group of order eight,
   then compare existing extension and commutator APIs with the center,
   quotient, and quadratic-form calculations needed for $Q$.
3. **Characteristic-two audit:** check which quadratic-form results work over
   $\mathbb F_2$; identify assumptions that two is invertible.
4. **Separate VOA contribution:** once the VOA API exists, prove that an
   automorphism fixing weight two pointwise is the identity when weight two
   generates the VOA. This assembles an action after generator lifts exist;
   it does not construct those lifts.

These are entry points, not approved theorem statements or claims that the
corresponding general results are missing from Mathlib.

### Source-coordinate definitions added in the continuation

- The Golay code and Leech lattice are explicit; the integral module laws
  and exact source-membership equivalence are proved.
- The dictionary bilinear form is explicit, with proved bilinearity.
- The minimum lattice norm and all three short-vector families are proved.
  Completeness and uniqueness give a bijection with the actual short classes
  in Λ/2Λ. Co₀ therefore has a proved permutation action on those labels.
- Conjugation in Q gives the signed short-vector representation of the local
  fiber product, with proved central phases, multiplication, and inverses.
- `sExtra` is the source triality, including its Fourier/sign octad blocks
  and a proved inverse.
- `classicalMonster` uses an independent bimonster presentation and
  centralizer quotient, with proved group laws. Historical recognition is
  a separate proof obligation.

All shared construction definitions are implemented without `sorryAx`.
`rhoLocal` is the local matrix, signed-short, and spin-tensor action, transported
through the explicit dictionary linear equivalence and descended to H.
Its linearity, composition, inverses, and diagonal-sign kernel are proved.
`griessProd` is the bilinear extension of Conway’s six explicit rules in the dictionary basis.
The explicit Leech integer basis, lattice quotient action, and local fiber
product modulo simultaneous signs are now constructed.
The six unchanged milestone proofs remain `sorry`.
