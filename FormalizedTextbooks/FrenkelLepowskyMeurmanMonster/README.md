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

All construction definitions in [Definitions.lean](Definitions.lean) are
implemented without `sorryAx` or custom axioms. They use explicit Golay and
Leech coordinates, the concrete extraspecial group, an orthogonal spin
normalizer, the local fiber product and its simultaneous-sign quotient,
Conway's multiplication, and an independent bimonster presentation.

**T1–T3 and T5 are proved in full for the implemented coordinate model. T4 and T6 remain unfinished.**
[Milestones.lean](Milestones.lean) now assembles proved clauses where available
and documents the remaining proof holes. [GAPS.md](GAPS.md) gives the current
inventory. Four independent reviews approved the T1–T3 checkpoint after
the required fixes. Independent T5 review approved the actual centralizer and
normal-generation proof; the primary FLM comparison
and the full global recognition arguments remain unfinished.

### Proved progress toward the six milestones

- [LocalStructure.lean](LocalStructure.lean) proves all ten extraspecial and
  quadratic-form clauses of T1: order, center, commutator, Frattini, actual
  quotient, squares, and plus type.
- [LocalExactness.lean](LocalExactness.lean) proves that `inclQ` and
  `rhoLocal` are injective, and that the inclusion image equals the
  projection kernel, and that `projH` is surjective.
- [LeechQuadratic.lean](LeechQuadratic.lean) proves the actual lattice
  half-norm agrees with the hyperbolic binary form, that Co₀ preserves it,
  and that the preferred short lifts square to the identity.
- [LocalForm.lean](LocalForm.lean) proves orthogonality of the signed-short
  and spin-tensor local action blocks.
- [LocalInvariance.lean](LocalInvariance.lean) and
  [LocalProductInvariance.lean](LocalProductInvariance.lean) prove the full
  local product and form invariance, completing T1.
- [GeneratedForm.lean](GeneratedForm.lean) proves form preservation for every
  element of G. [TrialityOrder.lean](TrialityOrder.lean) proves `sExtra³ = 1`.
- [Finiteness.lean](Finiteness.lean) proves finiteness of the actual Co₀,
  Co₁, spin normalizer, local fiber product, and H.
  [GeneratedFiniteness.lean](GeneratedFiniteness.lean) supplies the analytic
  mechanism used to prove finiteness of G in T3.
- [GeneratedSubgroups.lean](GeneratedSubgroups.lean) embeds H and Q in G
  and proves G nontrivial, independently of the milestone proofs.
- [TrialityInvariance.lean](TrialityInvariance.lean) proves preservation of
  the Griess form by the explicit extra symmetry and checks a source tensor
  square normalization. [TrialityFullProduct.lean](TrialityFullProduct.lean)
  proves full product preservation, completing T2.
- [Presentation.lean](Presentation.lean),
  [WreathCentralizer.lean](WreathCentralizer.lean), and
  [PresentationComparison.lean](PresentationComparison.lean) prove elementary
  reference-model facts and the centralizer quotient argument. The actual
  Y₅₅₅ recognition is still an explicit missing prerequisite.
- [LeechConcreteGeneration.lean](LeechConcreteGeneration.lean) proves that
  the actual Golay signs, Golay permutations, and three-bases isometry
  generate the entire Leech lattice symmetry group, through a constructive
  norm-eight reduction and coordinate-frame reconstruction.
- [GolayAutomorphismOrder.lean](GolayAutomorphismOrder.lean) proves the
  actual Mathieu group order, and its generation module proves completeness
  of the two concrete permutation generators.
- [GeneratedNormalCompletion.lean](GeneratedNormalCompletion.lean) proves
  the full simplicity argument conditional on recognizing the entire
  involution centralizer as the constructed local group.
  [GeneratedCentralizerRecognition.lean](GeneratedCentralizerRecognition.lean)
  now proves that recognition through actual constituent separation, orthogonal
  Leech reconstruction, and residual spin recognition. Together they prove T5.

The proof work corrected the tensor-times-tensor normalization in the earlier
transcription. Conway's Appendix 5, printed page 536, fixes the tensor-square
diagonal entries at `9/8` and `1/8`. The coordinate contractions now include
the required `1/8` factors, used in the complete product invariance proofs.
See [the coordinate source record](blueprint/sources/concrete-coordinates.md).

The original definition and milestone skeleton was authored by Muse Code.
Codex authored the subsequent coordinate implementations and supporting
proofs in the stacks above PR #6477. Statements of the six endpoints retain
the original mathematical conclusions. Generated collection roots only import
modules and are maintained by the repository generator.

The VOA, generator lifts, full VOA automorphism equality, representation
irreducibility, character formula, and genus-zero moonshine remain outside
these six finite-group milestones. Coverage of the broad roadmap remains
MAPPED; chapter outlines are not a source-verified theorem DAG.

Future declarations belong to the project's own namespace,
`FormalizedTextbooks.FrenkelLepowskyMeurmanMonster`. Later promotion of general
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
T1–T3 and T5 are proved. Their audits contain only `propext`,
`Classical.choice`, and `Quot.sound`; the T5 independent review is approved.
T4 and T6 retain documented proof holes.
The independent adversarial review of T1–T3 is complete; work on T4 and T6 continues.

The T4 counting prerequisites now include the full actual norm-eight vector
count, the exact Co₀/Co₁/local orders, the actual global pair-stabilizer
identification, the first local axis orbit count 196560, the actual feasible
local orbit counts 1 and 93150, and the actual triality transition subgroup
index 16584750. Its actual signed-pair orbit has 1104 elements. Both global orbit counts remain
unproved. An [independent review of the pair stabilizer and conditional order
assembly](https://artifacts.internalmeta.com/a/1814400673093555) approved those
five leaves, with its prerequisites and remaining hypotheses explicitly scoped.
The [actual transition subgroup index review](https://artifacts.internalmeta.com/a/2157891354936211)
also approved its nine scoped leaves.
The [pair and secondary feasible orbit review](https://artifacts.internalmeta.com/a/1658609605982919)
approved the new actual orbit counts and stabilizers.
The actual first axis transition column is complete with three proved destinations.
The first feasible transition column also is complete; all inputs reach the
proved secondary feasible local orbit. Full classification and both global counts
remain open. The [destination and Ω transport review](https://artifacts.internalmeta.com/a/1128903889576659)
approved its six scoped leaves.
The [first-column classification review](https://artifacts.internalmeta.com/a/945880241514491)
approved its nine scoped leaves, with global coverage and Atlas label assignments
outside its scope. Twenty-four coordinate lifts together with the central
involution now provably generate actual Q, giving a finite commutation test
for actual group identity.
The actual octad-image axis has a Q stabilizer of order 2¹⁷. Every coordinate
E8 section now has proved internal norm-eight transitivity, 2160 actual
norm-eight lattice vectors, and 135 actual lattice classes with sixteen vectors
in each nonempty reduction fiber. The [octad counting and Q identity review](https://artifacts.internalmeta.com/a/2390724688434621)
approved seventeen scoped leaves with no blocking findings, excluding disclosed
upstream authorship. Rooted section classification gives exactly
759 coordinate octads through the distinguished frame class. Actual incidence
counting now proves that the full Co₀ orbit has 46621575 E8 sections. The
[section-count and saturation review](https://artifacts.internalmeta.com/a/1666526895149276)
approved all seven scoped leaves with no blocking findings. Actual sign coherence
and Q correction now identify the projected octad-axis stabilizer. The actual
local stabilizer has order 11689182992793600, and its actual H orbit contains
11935123200 axes. The [independent complete second-orbit review](https://artifacts.internalmeta.com/a/2129702950992604)
approved its twenty-one scoped leaves with no blocking findings. Counting the other local orbits and proving full coverage remain open.
T6 has 84 of 120 Coxeter pairs proved; its full relations, actual local diagonal
generation, and independent presentation kernel recognition remain open.
The actual Norton U element now has proved order thirteen, including its positive
thirteenth-power spin sign. A nonzero actual invariant integer spin vector also
gives unconditional forward and inverse compact spin formulas with one 64-term
integer numerator. These do not prove the remaining line–line squares.

The [independent physical projection recognition review](https://artifacts.internalmeta.com/a/1133521452695039)
approved its three scoped leaves after fresh isolated replay, all seventeen
constants under standard axioms, fifteen linters, and four semantic probes.

The next actual odd-image orbit has a proved Q stabilizer of order 2¹² and an
actual full-axis Q orbit of 8192 points. Genuine norm-eight lines are counted
as physical outer matrices, with equality equivalent to equality of real
spans; there are 199017000 lines. Actual matching spatial and spin signs now
provide every projected stabilizer lift. The actual H stabilizer has order
85571854663680, and the third H orbit has exactly 1630347264000 axes. Its actual
matrix fiber consists of exactly 8192 axes. Independent review is approved. The
second orbit's actual matrix fiber is proved to consist of exactly 256 axes.
The corrected F12 = F13 relation is now proved in the original C322 presentation
and its restricted Y555 image by replaying 28530 actual chronological word
equations. Exact coset index certification and independent local recognition
are proved; the full global kernel remains open.


The fourth axis now has its full actual H stabilizer and orbit counted in Lean.
The four genuine permutation words generate the entire code14 and unordered
pair stabilizer of order 11520. Sixty-three actual frame classes and all 2048
equal-pair Golay signs force full physical flag generation. The genuine H
stabilizer has order 95126814720 and its orbit has 1466587938816000 full axes.
Its entire physical matrix fiber equals the 262144-axis Q orbit. The first four
counted actual H orbits are proved mutually disjoint and contained in the global
axis orbit; full global classification, coverage and transitions remain open.

The original C322 presentation now has exact order 9170703360, a faithful
characteristic-three representation and exact E7 index 3159. Its commutator
is isomorphic to the derived subgroup of the independent full finite Cartan
isometry group. Original C431 cubics and terminal elimination are proved,
including both maps to the independent 13-generator Coxeter/spider presentation.
The full Monster/wreath kernel and all 36 line–line relations remain open.
The first line square fixes the tensor and two full short units. All twelve
non-tensor forward-half packets are now bound in every Griess block, with their
actual inverse-packet pairings. The square is not yet proved identity. The C422 index and full projective recognition are unfinished.

Independent [U13 review](https://artifacts.internalmeta.com/a/1097903456386921)
and [third-orbit review](https://artifacts.internalmeta.com/a/977331758752417)
are approved with no blocking findings. The new local recognition bundle is
undergoing independent review; full T4/T6 and primary FLM comparison remain open.


The [independent fourth-orbit assembly review](https://artifacts.internalmeta.com/a/1835071391027554)
approved seven root-authored modules with no blocking findings: fresh isolated
source replay, all 45 private/generated constants under the three standard
axioms, and fifteen linters on 34 authored plus 11 generated declarations with
zero errors. It explicitly excludes independent certification of that
reviewer’s affine Q128, short-fixation and 63-frame prerequisites, and excludes
Atlas labels and full global orbit coverage.


The completed fourth-orbit checkpoint builds the canonical collection in
6862 jobs with 3460 imports. Its strict recursive audit checks all 59321
private/generated collection constants under only `propext`, `Classical.choice`
and `Quot.sound`, excluding exactly the unfinished T4 and T6 endpoint values.
All 32 changed leaf modules pass fifteen linters on 443 declarations
(226 authored plus 217 generated), with zero errors. Repository preflight and
cached diff checks pass. New transition-reciprocity, C422, geometry and binary
irreducibility investigations remain excluded until fully proved and gated.

### Actual binary irreducibility, transition reciprocity, and fifth-axis coordinates

The actual binary Co1 action is now proved irreducible. The proof uses only the
five actual lattice isometries, checked original matrix products, a nonzero
rank-one operator, and two complete cyclic bases. Consequently every normal
2-subgroup of actual Co1 is trivial, without a recognition assumption.
The [independent binary review](https://artifacts.internalmeta.com/a/1477997121060276)
approved all seven irreducibility leaves after isolated forced replay, a recursive
92-constant standard-axiom audit, and fifteen linters with zero errors.
The reviewer authored the separate normal-2-subgroup consequence and does not
independently certify that consequence.

Actual E8-section/frame incidence is counted and transitive: 135 frame classes
per section, 6293912625 flags, full Co0 stabilizer 1321205760 and Co1 image
660602880. The full frame-zero stabilizer is identified with actual Golay signs
and octad-fixing permutations. The
[independent frame-flags review](https://artifacts.internalmeta.com/a/3938607539614506)
approved these four leaves after isolated forced replay, all 32 private/generated
constants using only standard axioms, and fifteen linters with zero errors.
This does not identify the fifth axis stabilizer.

Actual H transitions and feasible transitions now satisfy weighted reciprocity
for arbitrary actual local orbits. The explicit original odd-cocode reflector
fixes every first pair axis and reverses the original triality transitions.
The actual reverse H entries into the first orbit are 135 from the second,
1 from the third, and 0 from the fourth. The reverse feasible entry from the
93150-vector secondary orbit into the singleton orbit is exactly 1.
No orbit-table classification or global coverage is assumed. The [independent feasible-transition review](https://artifacts.internalmeta.com/a/2308666636341233)
approved all four leaves after isolated forced replay, a recursive 53-constant
standard-axiom audit, and fifteen linters with zero errors.

The literal fifth candidate is an actual original six-factor generated-group
word. Its matrix is proved diagonal, with value 1/2 on the actual octad of
code label 2052 and 1/4 elsewhere, and square trace 3. Thus it cannot be in any
of the first four counted H orbits. All 552 middle pair-short coefficients are
proved zero. The later fifth-Q checkpoint below closes its full Q stabilizer and
identifies the actual fifteen-frame system. Full projection generation and
H orbit size remain open.

The actual norm-eight frame-class point set has 8292375 points, is invariant
under the genuine Conway action, and spans the whole 24-dimensional binary
module. This proves the spanning component of Ivanov II Lemma 5.1.2. The
source excludes some zero-sum triples from its line set; no universal geometry
presentation, universal-module upper bound, or all-triples line identification
is claimed here.

The literal first-line square now fixes eleven whole preferred short units,
namely basis indices 0 through 9 and 11, using all 1552 actual preferred-Q
transport inputs with their central phases. Twelve whole short returns remain.
The count of verified Coxeter pairs remains 84/120, with all 36 line-line
relations open. C422 replay and geometry/presentation-kernel work remain
unfinished and excluded from this checkpoint. Both T4 and T6 endpoints,
global axis and feasible-axis coverage/counts, and primary FLM comparison remain open.

The binary/transition checkpoint builds the canonical collection in 6913 jobs
with 3511 imports. Strict recursive auditing checks all 59888 private/generated
collection constants under only `propext`, `Classical.choice`, and `Quot.sound`,
excluding exactly the unfinished T4 and T6 endpoint values. All 51 new leaves
pass fifteen linters on 565 declarations (292 authored and 273 generated), with
zero errors. Repository preflight and cached diff checks pass.

The [independent Conway points/span review](https://artifacts.internalmeta.com/a/2064643920881930)
approved the two point/action/cardinality/spanning leaves after isolated forced
replay, a recursive 20-constant standard-axiom audit, and fifteen linters with
zero errors. Its scope excludes the line predicate, universal representation,
and dimension upper bound.


## Fifth-Q and frame-system checkpoint

The fifth representative's entire Q stabilizer is proved to have order 32,
with Q orbit size 1048576. This uses the original matrix, all middle short
coordinates, and all tensor coordinates, including the actual central phases.
Its binary image is exactly the displayed 32 translation/modulation classes;
every actual full-axis stabilizer element preserves this image.

The actual selected octad section has a complete integral eight-root basis,
with a verified rank-eight binary matrix. Its intersection with the fifth Q
image is a sixteen-element binary subspace whose fifteen nonzero classes
have explicit genuine norm-eight lattice representatives. Every actual
full-axis stabilizer lift preserves this fifteen-frame system. Neither
uniqueness of the original frame class nor identification with the previously
counted single-frame flag is used: both uniqueness claims are false for this
representative. Full spatial stabilizer generation, its projection order,
and the fifth H orbit size remain open. Independent review of these fourteen
intersection leaves is queued after the current C322 review.

The first-line square now fixes twelve whole preferred short units: basis
indices 0 through 9, 11, and 12. Eleven returns remain (index 10 and indices
13 through 22). The verified Coxeter-pair count is still 84/120, with the
36 line-line relations open.

A generic theorem proves that the commutator subgroup of a group satisfying
Ivanov II Proposition 2.3.7's explicit point/line and connectivity hypotheses
is finite of order at most two. This is not yet applied to the actual Conway
geometry; the genuine line predicate, connectivity, universal-module upper
bound, and abelianization remain to be proved.

Seventeen further C422 prerequisites construct the independent split
quadratic form, actual reflections and conjugation, and the 1080 distinct
norm-two projective lines. They do not yet prove full source faithfulness or
Monster recognition. The original C422 coset replay and actual Monster
geometry/kernel developments remain outside this checkpoint.

T4 and T6 are still unfinished. The twelve-axis and ten-feasible-orbit
coverage, final global counts/order, presentation kernel, and primary FLM
comparison remain open.

The canonical collection builds in 7001 jobs with 3595 imports. The strict
collection audit checks 60658 private/generated declarations using only
`propext`, `Classical.choice`, and `Quot.sound`, excluding exactly the two
unfinished T4/T6 endpoint values. All 84 new leaf modules pass fifteen linters
on 758 declarations (442 authored and 316 generated), with zero errors.
Repository preflight and the cached diff check pass.


## Local C422 recognition and fifth generators checkpoint (2026-10-14)

The original nine-generator C422/S/Q presentation from Soicher (1985), Table 3,
and Ivanov I, §8.4, is now proved finite of exact order 9,904,359,628,800.
The literal original-source coset equations give index at most 1080 over the
proved faithful C322 parabolic. The independent projective norm-two reflections
of the split eight-dimensional form over F₃ give the matching lower bound and
prove the actual presentation map injective. The generator-preserving
`y422ClassicalReflectionEquiv` identifies that source presentation with the
independently defined group generated by **all** norm-two projective reflections.
Its 1216-leaf dependency bundle passes a recursive audit of all 3192 private and
generated constants under only `propext`, `Classical.choice`, and `Quot.sound`,
and all fifteen linters. Conventional Ω₈⁺(3):2 comparison through spinor and
determinant definitions, global parabolic inclusion faithfulness, and the
Monster presentation kernel remain open.

For the fifth actual axis, the restricted local projection kernel has exact
order 32. Its full local stabilizer cardinal is therefore 32 times the cardinal
of its actual Co1 projection range; that range has not yet been identified in
full. Six genuine original permutation words preserve the selected integral E8
section and its actual sixteen-element frame system, with all ninety nonzero
frame-class images verified through genuine integer lattice coordinates. Five
actual source permutation words generate the full source-octad permutation
stabilizer, of order 322560, and their original transport gives the full actual
selected-octad permutation group of the same order.

The corrected Xi and twelve corrected original source sign words now fix the
entire original tensor and matrix blocks. Their whole short-block proofs, the
six corrected permutation whole-axis lifts, full projected stabilizer
generation, and fifth H-orbit cardinal remain open. The generic Xi short
physical/Q caches and executable final-axis coefficient numerators are proved;
the remaining bounded short-coordinate packets are outside this checkpoint.

Additional actual geometry leaves identify Q-incidence with the two-core of the
actual involution centralizer, identify the actual Conway base-point two-core
with 2048 Golay sign classes, construct a genuine original two-orbit tetrad
line, and define the universal binary module using exactly the genuine line
relations. The universal-module dimension bound and global geometry kernels
remain open. Norton proof counts remain twelve of twenty-three preferred-short
returns and eighty-four of one hundred twenty Coxeter pairs.

T4 and T6 still have their original documented endpoint proof holes. The full
twelve-axis and ten-feasible-orbit classifications, global count assembly,
presentation kernels, and primary FLM comparison remain open. The newly added
scopes have not yet received a complete independent adversarial review.

Canonical collection build: 8312 jobs, 4906 imports. Strict recursive audit: 64724 declarations, including private and generated declarations, use only the standard three axioms; exactly the unfinished T4 and T6 endpoint values were excluded. The 1311 new leaf modules passed all 15 linters: 4066 declarations (1756 authored and 2310 generated), zero errors. Repository preflight and cached diff checks passed.


## Full fifth Xi and actual system stabilizer checkpoint (2026-10-14)

The genuine Q-corrected Xi now fixes the entire original fifth axis: matrix,
short, and tensor blocks. All 3856 actual nonzero short coordinates have their
original transport, preferred-Q phase, and coefficient equality checked;
orthogonality proves equality at the remaining coordinates. The 186-leaf
bundle passed canonical build (4122 jobs), recursive standard-three-axiom
audit (1236 private/generated constants), and all fifteen linters (564 authored
and 672 generated declarations, zero errors).

The full original Co0 group preserving both the selected integral E8 section
and the entire actual sixteen-element binary frame system is now identified
and counted: 1321205760 in Co0, 660602880 in the actual quotient Co1. It acts
transitively on the fifteen genuine nonzero frame classes. The first-frame
stabilizer has exactly 4096 signs times 21504 actual permutations. The twelve
original Golay signs, six original spatial permutation words, and original Xi
generate this full simultaneous stabilizer. The actual selected-octad
permutation orbit of the whole system contains exactly fifteen systems.

This does not yet identify the full fifth-axis stabilizer projection: the
twelve corrected sign and six corrected permutation whole-axis lifts remain
in progress. Its H-orbit cardinal therefore remains open. Seven further
local classes, twelve-axis and ten-feasible coverage, actual transition
equations, and the global Monster order remain open.

Additional genuine E8 finite-core and maximality results, actual Co1 universal
binary-module prerequisites and relation transport semantics, and original
Norton Gaussian packet certificates are included. The unconditional270-system
coverage and exact universal-module dimension/kernel are still in replay.
The Norton counts remain12/23 preferred-short returns and84/120 Coxeter pairs.
T6 global geometry, presentation kernels, and Monster recognition remain open.
Independent adversarial review of these new scopes and the final primary FLM
comparison remain pending.

Canonical collection build: 8590 jobs, 5183 imports. Strict recursive audit: 68400 private/generated declarations use only `propext`, `Classical.choice`, and `Quot.sound`; exactly the unfinished T4/T6 endpoint values were excluded. All277 new leaf modules passed all15 linters:3673 declarations (1929 authored,1744 generated), zero errors. Repository preflight and cached diff checks passed.


## Twelve fifth signs, complete E8 systems, and universal source bridge (2026-10-14)

All twelve genuine corrected source Golay signs now fix the whole original
fifth axis, including the complete short block. They give the original
twelve encoder-basis signs in its actual Co1 stabilizer projection; source
generation proves every original Golay sign also lies in that image. The
corrected Xi is already a whole-axis lift. The remaining six corrected
permutation lifts, actual full image equality, and fifth H orbit remain open.
The staged assembly proves the full stabilizer order21139292160 and orbit
6599645724672000 conditional on that actual image equality.

The actual selected E8 section has exactly270 genuine sixteen-element totally
singular frame systems. An unconditional Fin270 parametrization, completeness,
and maximality are proved. A proved first-label pigeonhole bound reduces the
finite coverage to labels0–31. Classification of their two full actual spatial
orbits is in progress and remains outside this checkpoint.

The actual Conway geometry now has an independent nonabelian universal
presentation using precisely point squares and genuine source line products.
Its actual commutator quotient is proved isomorphic to the independent binary
module defined by those genuine line equations, preserving every point
generator. The natural group-to-module kernel is exactly the commutator. The
whole actual Conway group acts faithfully on the source presentation by
automorphisms. This does not prove the source group abelian. The binary
module's dimension24 and natural map injectivity, actual geometry commutator
bound, abelianity, and global Monster kernels remain open. New exact binary
mask decoders retain the literal full matrix and original genuine-line tests.

The literal preferred-basis13 Norton first-line square return is proved. Its
whole forward/inverse packets and complete actual U transport are identified
with all256 short phases and both tensor factors retained. Counts are now
13/23 preferred-short returns and84/120 Coxeter pairs. Remaining returns are
basis10 and14–22; all36 line–line Coxeter relations remain open.

T4 and T6 remain unfinished. Seven further local axis classes, twelve-axis
and ten-feasible coverage, all required transition equations, global counts,
presentation and geometry kernels, final recognition, independent review of
these new scopes, and primary FLM comparison remain open.

Canonical collection build:8683 jobs,5276 imports. Strict recursive audit:68938 private/generated declarations use only `propext`, `Classical.choice`, and `Quot.sound`, excluding exactly the unfinished T4/T6 endpoint values. All93 new leaf modules passed all15 linters:535 declarations (286 authored,249 generated), zero errors. Repository preflight and cached diff checks passed.


## Two E8 orbits, invariant forms, and Norton basis15 (2026-10-14)

The 270 actual maximal singular frame systems of the selected E8 section
now split into exactly two disjoint full actual spatial orbits of 135 each.
Original generator words cover both families. The second representative has
actual stabilizer order 1321205760 in Co0 and 660602880 in Co1. These are
orbits of frame systems within a section; they do not establish the global
axis or feasible-axis classifications.

Every linear endomorphism commuting with the actual Conway action on the
24-dimensional binary space is zero or identity. The actual polar form gives
an explicit linear equivalence with its dual. The invariant bilinear forms
are zero and polar; invariant quadratic forms are zero and the actual
squares form. These unconditional statements concern the existing binary
space. The independent genuine-line universal module's dimension 24 and
natural map injectivity, and the nonabelian universal group's commutator
bound and abelianity, remain open.

The whole original Norton returns at preferred basis14 and basis15 are
proved, including all short-vector phases and both tensor factors.
Counts are 15/23 preferred-short returns and 84/120 Coxeter pairs.
The remaining returns are basis10 and basis16–22. All 36 line–line pairs
remain open. Six corrected fifth-axis permutation lifts have complete
original tensor certificates checked in work outside this checkpoint;
their full short block and final stabilizer image equality remain open.
This checkpoint includes 16 proved generic/source helpers for those lifts.

T4 and T6 remain unfinished. Seven further local axis classes, global
12-axis and 10-feasible coverage, the required transition equations and
counts, source presentation and geometry kernels, and final Monster
recognition and primary FLM comparison remain open.

Canonical collection build: 8759 jobs and 5352 imports. Strict recursive audit:
69902 private/generated declarations use only `propext`, `Classical.choice`,
and `Quot.sound`, excluding exactly the unfinished T4/T6 endpoint values.
All 76 new leaf modules passed 15 linters: 960 declarations (410 authored,
550 generated), zero errors. Repository preflight and cached diff checks
passed.

Independent adversarial review approved the preceding 22-leaf genuine Co1
universal-presentation and whole Norton basis13 bundle, with no blocking
findings. The isolated replay checked all 194 private/generated constants
with only the standard three axioms, and all 191 lint declarations (102
authored, 89 generated) with 15 linters and zero errors. Its source comparison
preserves genuine line semantics and does not infer source abelianity or
module dimension 24. Report:
https://artifacts.internalmeta.com/a/881633951609451

Independent adversarial review of the eight invariant-form and CodeNine
transport leaves is approved: isolated replay, all 82 private/generated constants
using only standard axioms, 36 authored plus 46 generated lint declarations,
15 linters and zero errors. Report:
https://artifacts.internalmeta.com/a/1665853261640576

The new E8 orbit bundle and other new scopes still require independent
review; final endpoint review remains open.

## Actual fifth orbit, nonsplitting, and six Norton returns (2026-10-14)

The fifth axis now has an unconditional full local stabilizer and orbit count.
All six original corrected Golay permutation lifts fix the complete axis,
including all 3856 short coordinates and the whole tensor part. Together
with the proved signs and Xi these establish the actual projected stabilizer,
full H stabilizer order 21139292160, and H orbit size 6599645724672000.
The first five local axis orbits are complete; seven further classes and
all global twelve-class coverage, remaining transitions, anchors and total
axis count remain open. Eight further feasible classes and global ten-class
coverage/counting remain open. The global pair-stabilizer identification
and its order are already proved.

For the existing actual binary Conway action, there is no homomorphism
Co1 → Aut(Q) lifting that action. The proof uses fourteen literal original
source-word powers and a contradictory affine correction system, with all
central phases bound to the genuine cocycle. Mathematical evidence report:
https://artifacts.internalmeta.com/a/1127139053333300
This does not establish the universal source group's commutator bound,
abelianity, local kernel, or its independent universal module dimension.
The actual polar point graph is connected and genuine adjacent source point
involutions commute. The commutator bound still explicitly requires local
polar-neighbor connectivity and polar-zero source commutation.

Whole original Norton returns at preferred bases16–21 are now included,
with complete signed short transport and full tensor transport. This
checkpoint contains 21/23 preferred-basis returns and 84/120 Coxeter pairs.
Basis10 is separately gated outside this checkpoint; basis22 is still in
assembly. All 36 line–line relations and the spider relation remain open.
The full generator and presentation-kernel recognition steps remain open.

The independent universal-module replay has checked all 171 initial point
bindings and all 147 genuine-line certificates in work outside this
checkpoint. Remaining action/image replay, chronological equations,
spanning targets and final injectivity/dimension24 are not asserted here.
No replay candidates are included in this checkpoint. Only two small
unconditional action/polar-line helpers from that work are included.

Independent review approved the earlier eight invariant-form/CodeNine
leaves (report above). Review of the new polar/commutator and basis18 scope
found only comment-count errors, now corrected and rechecked: all 330
private/generated constants use standard axioms, and 159 authored plus
171 generated declarations passed all 15 linters. That independent review
and review of the full fifth orbit are still underway. T4 and T6 remain open.

Canonical collection build: 9147 jobs and 5740 imports. Strict recursive
audit: 73396 private/generated declarations use only propext,
Classical.choice and Quot.sound, excluding exactly the unfinished T4/T6
endpoint values. All 388 new leaf modules passed 15 linters: 3489
declarations (1755 authored, 1734 generated), zero errors. Repository
preflight and cached diff checks passed.

## All Norton returns, sixth-axis geometry, and local connectivity (2026-10-14)

All 23 original preferred-basis Norton returns are now proved. Their assembly
proves the first literal line-difference square is the identity in the actual G,
and transports it to the six selected consecutive line pairs. The verified
Coxeter pair count is 90/120; the remaining 30 line-line pairs and the spider
relation are open. The actual Singer lift now conjugates U to U cubed and
commutes with V, with all central phases and the spin scalar sign verified.
Its triality compatibility and the second seed relation remain open; no
additional Coxeter relations are inferred from the normalizer alone.

The sixth actual axis has a complete matrix formula. All 549 excluded middle
pair rows vanish and the three remaining signed coefficients are verified.
Its matrix stabilizer is exactly the subgroup preserving the actual real
plane spanned by the two short roots at coordinates 16–17 and 16–19 and fixing
the specified short-vector line. Both roots have integral square 32 and
pairing 16. The full sixth H stabilizer projects into the genuine Co1 flag
stabilizer. Full Q stabilization, projection surjectivity and the sixth orbit
count remain open. The first five actual H orbits are complete; seven further
classes, global twelve-class coverage/transitions/anchors and the total axis
count remain open. The remaining eight feasible classes and global ten-class
counting also remain open.

For the standard root 4(e0+e1), the original catalogue neighbor families have
88 pair, 2464 octad and 2048 odd short classes. Their faithful actual catalogue
identifications prove the full 4600 count. A sign-normalization equivalence
also proves exactly 4600 actual lattice vectors of integral square 32 with
positive root pairing 16. The A2 plane count 2300 and flag transitivity are not
asserted by these leaves and remain under construction.

The actual polar-neighbor sets are connected by genuine original source
lines, unconditionally. The thirteen-leaf proof normalizes both odd norm-eight
shapes, proves actual monomial transitivity/generation, and binds all nine
source-word line transports. Author proof report:
https://artifacts.internalmeta.com/a/1603338647942399
The separate polar-zero commutation hypothesis is still open. Neither local
connectivity nor the already proved nonsplitting obstruction establishes the
universal source group's commutator bound or abelianity without that input.

Outside this checkpoint, all 867 point bindings, 147 genuine lines, 946 actual
images and 833 chronological source equations now compile. Twelve of 88
spanning targets are checked at this checkpoint's documentation update.
The remaining targets, spanning assembly, natural equivariant equivalence,
dimension 24 and full replay gates are not asserted here. Replay candidates
remain untracked and are excluded from the generated collection.

Independent adversarial review approved the 28 polar/basis18 leaves, with no
remaining findings after the earlier comment-only corrections:
https://artifacts.internalmeta.com/a/1625672549058188
Independent review also approved all 23 CodeTwentyTwo/tensor-row leaves with
no findings: isolated forced replay, 471 standard-axiom constants, 470 lint
declarations, genuine source indices and full sixteen-column Gram checks.
https://artifacts.internalmeta.com/a/1126644969904051
New sixth geometry, local connectivity and final endpoints still require
independent review. T4 and T6 remain unfinished.

Canonical collection build: 9254 jobs, 5847 imports. Strict recursive audit:
75236 private/generated declarations use only propext, Classical.choice and
Quot.sound, excluding exactly the unfinished T4/T6 endpoint values. All 107
new leaves pass all 15 linters: 1828 declarations (626 authored, 1202 generated),
zero errors. Frozen disk/index hashes and indexed import closure, repository
preflight and cached diff checks pass.

## Natural Conway module identification and rooted A2 planes (2026-10-14)

The independently defined original genuine-line universal Conway module is
now naturally isomorphic to the actual binary 24 module. The equivalence
preserves every original point generator and intertwines the exact existing
Co1 action; its dimension is 24. This closes the universal-module replay:
867 actual point bindings, 147 genuine source lines, 946 actual image bindings,
833 chronological source equations, 88 spanning targets and 120 five-generator
basis images, followed by full span and natural-map injectivity. All 1980
replay leaves are frozen and included. The subgroup R itself is not proved
abelian by this module identification; its source commutator/recognition
argument and the global presentation kernel remain open.

The actual standard-root neighbor catalogue and oriented lattice vectors
have 4600 elements. Their real-span map has exactly two neighbors in every
fiber, so the actual rooted A2 plane set has 2300 elements. Independent
adversarial review approved all six count/plane leaves with no findings:
isolated replay, 122 standard-axiom constants, 64 authored plus 58 generated
lint declarations, 15 linters and zero errors. No transitivity or abstract
Co2/U6 stabilizer identification was assumed. Report:
https://artifacts.internalmeta.com/a/1452299556800507

Five further actual monomial leaves normalize the pair and octad neighbor
families while preserving the root line. The octad permutation uses genuine
Mathieu five-transitivity and fixes both root coordinates; the sign extension
and pair normalization preserve the actual signed root line. The remaining
odd-family and cross-family transitions are outside this checkpoint, so full
rooted-flag transitivity/stabilizer counting is still open. Full sixth-axis Q
stabilization, projected-stabilizer surjectivity and orbit count also remain
open. Two actual eight-factor spin-circuit/middle-tensor helpers are included,
without treating the pending complete tensor cache as a proof input.

Eight genuine residue helpers construct the actual local source quotient,
its point generators and genuine induced line relations, and prove the
two-distinct-common-neighbor commutation bridge with residue abelianity
explicit. Actual equivariance reduces that abelianity input to the base
residue. A six-element hexad representation is abelian under its exact
involution and perfect-matching triple relations. The comparison with the
actual Mathieu sextet/residue and the needed Co2 subgeometry arguments
remain open; these helpers do not discharge polar-zero commutation.

Seven further Singer triality helpers are included, including its exact
commutator tensor coefficient and the original signed-coordinate identity
criterion. Triality compatibility, the remaining 30 line-line Coxeter pairs,
the spider relation and the full presentation recognition remain open.
The verified Coxeter pair count stays 90/120. T4 and T6 remain unfinished.

Canonical collection build: 11258 jobs, 7851 imports. Strict recursive audit:
91680 private/generated declarations use only propext, Classical.choice and
Quot.sound, excluding exactly the unfinished T4/T6 endpoint values. All 2004
new leaves pass all 15 linters: 16305 declarations (4899 authored, 11406 generated),
zero errors. Frozen disk/index hashes and indexed dependency closure,
repository preflight and cached diff checks pass. The 1980 module replay and
new residue/monomial scopes still require independent review; the six rooted
A2 count leaves have the independent approval linked above.


### Singer relations and sixth-axis Q bounds (2026-10-14)

The actual verified Coxeter-pair count is now **103/120**. Eleven new Norton
leaves prove the original Singer short/tensor covariance, source triality
commutation, seeds 3, 9, 4, and all 19 selected line pairs in those Singer distance
classes. Thirteen of these pairs are new; six overlap the already proved
consecutive pairs. Three further actual distance-two local transport helpers
are included, but their square relation is not yet proved. The remaining 17
pairs are the distance-two Singer class. The spider relation and global
presentation recognition remain open.

Twenty-eight sixth-axis leaves bind the complete initial spin sign decoder
and source tensor formula, prove three actual preferred-short Q elements fix
the whole axis, and derive **4 ≤ Nat.card(genuine sixth-axis Q stabilizer)**.
Twelve genuine transported Pauli fixers, translation rank 9, squared norm 2,
and the actual odd-modulation fixer prove actual spin and Omega-difference
coordinate squares at most 1/256. A separate generic coordinate-orbit norm
lemma supplies the elementary 512-coordinate inequality. This checkpoint
does not claim Q card 4: the high tensor-column uniqueness and resulting upper
bound, projected-stabilizer surjectivity, whole-axis lifts and orbit count
remain open. Global twelve-class and feasible ten-class coverage and totals
also remain open.

Four root-neighbor leaves close odd-family monomial normalization and prove
all three original neighboring short families are individually transitive
under the genuine root-line-preserving monomial subgroup. Coordinate squares
prove exact catalogue-family preservation, and the integer-pairing proof
shows the actual root-line stabilizer preserves the original neighbor
predicate. Cross-family Xi transitions and full rooted-flag transitivity are
outside this checkpoint. The independently reviewed 4600-neighbor/2300-plane
count remains unchanged.

Seven actual source-group leaves identify its binary abelianization with the
already proved natural F2^24 module and exact Co1 action, and develop central
commutator, square-representative and square-coefficient invariance helpers.
Their finite commutator/card≤2 assumptions remain explicit. No actual source
abelianity, extraspecial Q identification or global presentation kernel is
inferred. Four actual auxiliary M22/Golay residue helpers bind genuine pair
points, rooted octads, hexad representations and nearby commutation; finite
catalogue connectivity, module and quadratic certificates remain outside
this checkpoint.

Canonical collection build passes 11316 jobs with 7909 imports. The strict
recursive audit checks 93272 private/generated declarations with only
propext, Classical.choice and Quot.sound, excluding exactly the two unfinished
T4/T6 endpoint values. All 58 new leaves pass all 15 linters: 1592 declarations
(246 authored, 1346 generated), zero errors. Frozen disk/index hashes and
indexed import closure, repository preflight and cached diff checks pass.
These new scopes still need independent review. T4 and T6 remain unfinished.


### Exact sixth-axis Q and rooted spatial stabilizers (2026-10-14)

The genuine sixth-axis Q stabilizer now has exactly **four** elements.
Fourteen support/tensor leaves exhaust the actual cocodes 0, 1504, 1648 and
912, proving fixation of the complete axis and the matching upper bound.

Actual Xi transitions connect all three rooted-neighbor families; the genuine
root-line subgroup acts transitively on 4600 neighbors and 2300 planes.
Actual stabilizer transport proves the original sixth spatial Co1 stabilizer
has order **18393661440**. The full H axis stabilizer has projection kernel
four, order four times its actual projection range and upper bound
**73574645760**. Spatial surjectivity and whole-axis lifts remain open.
Two further leaves prove the actual Mathieu flag-permutation order **40320**.

Independent adversarial reviews approved the 13 rooted transitivity leaves
and eight rooted stabilizer/projection leaves, with fresh replays, recursive
standard-axiom audits, zero lint errors and no findings:
https://artifacts.internalmeta.com/a/2931330043919117
https://artifacts.internalmeta.com/a/28810231631927141

Fourteen Norton leaves prove the actual U squared Gaussian action, its exact
spin sign, all 24 Q images and full forward/inverse tensor dictionaries. Five
distance-two helpers bind the first four literal states. The verified pair
count remains **103/120**; the remaining 17 pairs, spider relation and global
presentation recognition remain open.

Seventeen source-group leaves construct the actual extraspecial Q
identification and exact Co1 action under explicit finite central commutator
and card-at-most-two assumptions. Actual automorphism nonsplitting then
forces source abelianity under those assumptions. The actual geometric
commutator bound remains open. Eleven auxiliary M22 residue leaves prove
genuine global/local connectivity and the universal commutator bound; new
module/quadratic certificates and source-residue comparison are outside this
checkpoint. Global twelve-class and feasible ten-class coverage, transitions
and totals remain open. T4 and T6 are unfinished.

Canonical collection: **11391 jobs, 7984 imports**. Recursive strict audit:
**94271** private/generated declarations use only propext, Classical.choice
and Quot.sound, excluding exactly unfinished T4/T6 endpoint values. All
**75** new leaves pass 15 linters: **999 declarations** (463 authored,
536 generated), zero errors. Frozen disk/index hashes, indexed import closure,
preflight and cached diff checks pass. Other new scopes await independent
review beyond the two approved rooted scopes above.


### Full sign lifts, actual monomial generation and auxiliary residue abelianity (2026-10-14)

All genuine Golay signs with equal bits on coordinates 16,17,19 now belong
to the actual full sixth-axis projected stabilizer. Ten structural full-axis
lifts are proved; the generic forward-triality locality and matrix projection
formula applies to every actual Q input with even modulation. No tensor-only
fixation or unproved scalar anchor is used for these sign lifts.

Three original full permutation fibers generate the actual ordered-triple
Mathieu stabilizer. Explicit original two-generator words bind its transport
to 16,17,19, an actual root-pair swap, and the transport to the original Xi
fixed coordinate triple. The three transported permutations and swap generate
all **40320** actual flag permutations. The constructed equal-sign monomial
subgroup has **41287680** elements in Co0 and **20643840** in Co1; its fourteen
source generators genuinely generate this counted subgroup. Full sixth-axis
permutation/Xi lifts and the actual 891-frame orbit lower bound remain open.
The earlier exact Q card four and spatial Co1 order 18393661440 stand; the
full H stabilizer order 73574645760 is still only a conditional consequence
of spatial surjectivity. The root's fifteen new leaves await independent review.

Seventeen auxiliary M22 leaves now prove abelianity for every group generated
by the original 231 pair-point involutions satisfying the actual 77 rooted
Golay hexad matching line products. Original point-product reductions, eleven
source coordinates and all 66 quadratic coefficients are kernel-checked.
No abstract Todd-module classification or assumed invariant form is used.
Author verification (not independent approval):
https://artifacts.internalmeta.com/a/961280483702884
The genuine Co1/M24/M22 residue comparison remains open.

Sixteen actual source-geometry leaves construct phase-independent genuine
Monster lines through z for every original Conway frame point, a central
source-local subgroup mapping onto actual Q, its central generator of exact
order two, and the explicit residual kernel decomposition. Four of these
leaves prove actual squareQuad(v)=0 exactly when v is zero, an original short
class, or an original norm-eight frame point; the singular count is 8390656.
The trace distinction, converse 2B classification, source local injectivity,
geometric commutator premise and global kernel are outside this checkpoint.

Twenty-six Norton leaves extend the literal distance-two forward/inverse
packet states, certify 512 full preferred-Q images and actual parity transport,
and bind exact denominator-four physical U squared/inverse matrices. Whole
forward seven-step and inverse six-step packets are proved for inputs 2–9.
The exact packet pairing/returns remain open; the verified pair count stays
**103/120**. The remaining seventeen relations, spider and global presentation
recognition are unfinished.

Independent review approved all 560 C322 local-order leaves, with fresh
replays, 15680 recursive standard-axiom checks and zero unresolved findings:
https://artifacts.internalmeta.com/a/1438369844914843
The fourteen fifth-axis intersection leaves were also independently approved:
https://artifacts.internalmeta.com/a/1086890394220512
The complete fifth spatial/full-lift reviews remain in progress.

Canonical collection: **11475 jobs, 8068 imports**. Strict recursive audit:
**95829** private/generated declarations use only propext, Classical.choice
and Quot.sound, excluding exactly unfinished T4/T6 endpoint values. All
**84** new leaves pass 15 linters: **1557 declarations** (821 authored,
736 generated), zero errors. A generated-name collision in two new Norton
helpers was repaired and the combined build and all gates rerun. Frozen
disk/index hashes, indexed import closure, preflight and cached diff checks
pass. T4/T6, global twelve-class and feasible ten-class coverage, transitions
and totals remain open. Other new scopes await independent review.

## T4 priority: exact eighth coordinates and coverage reductions (2026-10-14)

The team is now assigned entirely to T4. T1–T3 and T5 remain proved and
reviewed; additional T6 work is paused. This checkpoint contains 43 new Lean
leaves and six narrow fifth-orbit API repairs, together with the regenerated
collection root.

The actual eighth prototype is a seven-factor original local word between two
actual triality factors. All 24 spatial frame columns and inverse coordinates
are checked. All 552 inverse signed-pair labels are outside the actual pair
family, so every original off-diagonal matrix entry is zero. Its diagonal is
3/4 at coordinate 20, 3/8 at coordinates 0,1,2,3,5,6,9,10,16,18,22,23, and 1/4
elsewhere. These are coordinates of the actual generated vector, without an
assumed source class, extraspecial kernel, or local orbit order.

Six actual sixth-phase leaves establish the nine-stage Pauli models and the
signed terminal spin value +1/16. Eight new global reduction leaves establish
all-vector transition destinations, genuine orbit/coset counting, both source
signs, and reduction of real triality coverage to finite binary orbit forests
and verified full-vector transports. The concrete later-family forests,
whole-axis transports, twelve-class coverage, ten-feasible coverage, and final
orbit counts remain open. The separately checked 891-point discovery tree is
not included here; its actual stabilizer-generator binding is still being
proved. No sixth full projection or order is asserted by this checkpoint.

Previously completed T6 work is preserved: the actual local 2B criterion for
Q elements is central z or a genuine norm-eight frame class. Genuine 2B points
have full trace 276; both central phases over every actual short class have
trace 4372. The full local point-generated source subgroup is identified with
the verified frame-generated subgroup, and source z is central there. The
residual source-to-Q kernel and global recognition remain open. Three rooted
auxiliary M22 star-generation helpers are also preserved.

Independent reviews completed since the previous checkpoint:

- The fifteen original even-Q, permutation-generation, and monomial leaves:
  https://artifacts.internalmeta.com/a/1116464044415485 (approved).
- The fifth system and corrected-Xi scope of 203 leaves:
  https://artifacts.internalmeta.com/a/2237411990154857 (approved).

The fifth full-lift/local-order review identified six copies of a private
inverse-coordinate lemma already supplied by `Equiv.symm_apply_eq`. Exactly
those six copies were removed and replaced by the standard API; all public
statements are unchanged. The revised 150-leaf independent review remains
pending its final fresh replay and audit gates. The new eighth and sixth
phase scopes also await independent review.

Verification: the canonical collection build passed 11,518 jobs. The strict
recursive audit passed 96,183 private/generated declarations with the three
standard Lean axioms, excluding only the existing T4 and T6 endpoint values.
All 49 changed Lean modules passed 15 linters: 426 declarations, consisting of
238 authored and 188 generated declarations, with zero errors. Frozen source
and index hashes and the indexed import closure match.

## T4 priority: genuine frame orbits and seventh kernel (2026-10-14)

This checkpoint adds 81 Lean leaves devoted to T4. All five workers and the
primary agent are assigned to T4; T6 remains paused.

- Sixth local class: all 891 distinct genuine frames and all 890 actual
  transition equations are proved. The actual counted monomial subgroup fixes
  the base frame. The projection and local-order conclusions retain precisely
  the five corrected full-axis generator membership premises; those full
  fixation proofs remain open. New original-Q basis-image formulas determine
  the full images and phases of all 552 signed source pairs.
- Seventh local prototype: the whole actual matrix and the full extraspecial
  axis stabilizer are identified. The extraspecial stabilizer has exactly four
  elements. Its full local stabilizer cardinality is four times the actual
  projection-range cardinality; that range and its order remain open.
- Eighth local prototype: polynomial identities recover its actual dodecad
  and distinguished coordinate-line projections from its matrix. Every actual
  spatial isometry fixing the matrix belongs to the genuine Golay monomial
  subgroup. The full-axis kernel, projection range and local order remain open.
- Global coverage: the entire genuine 8,292,375-element binary Omega orbit
  is covered for the first local family by three actual roots, using genuine
  monomial transitivity and phase lifts. Later-family forests and real triality
  transports, all twelve axis classes, all ten feasible classes and both global
  orbit totals remain open.

The revised 150-leaf fifth full-lift/local-order review is independently
approved: https://artifacts.internalmeta.com/a/2164026557848918 . All 150 fresh
leaf logs and semantic probes pass; all 1,017 private/generated declarations
use the three standard axioms; all 15 linters pass. The six standard inverse-API
repairs are resolved and independently replayed. The fifth actual local
stabilizer order 21,139,292,160 and local orbit size 6,599,645,724,672,000 are
reviewed. The new sixth, seventh and eighth scopes await independent review.

Verification: the canonical FLM collection build passed 11,599 jobs. All 81
new Lean modules passed 15 linters: 1,314 declarations, consisting of 392
authored and 922 generated declarations, with zero errors. The strict recursive
audit passed all 97,497 private/generated declarations with only the three
standard axioms, excluding exactly the existing T4 and T6 endpoint values.
Frozen disk/index hashes, indexed import closure, preflight and whitespace
checks pass. T4 and T6 remain open.

## T4 priority: eighth spatial order and actual fifth binary orbit (2026-10-14)

This checkpoint adds 47 Lean leaves and repairs one seventh-prototype
mathematical docstring (the source pair is zero/twelve). T4 remains open;
five of twelve planned local axis-orbit counts are closed. That fraction
measures this subtask, not the entire T4 proof.

- Sixth: the actual spatial frame orbit has 891 elements unconditionally,
  and its actual spatial base stabilizer has order 20,643,840. All 276 middle
  odd images, their coefficient phases, and the full final tensor integer
  formula are formalized. The five corrected full-axis fixation proofs and
  the resulting full projection and local order remain open.
- Seventh: the genuine E8 section and its A2 plane are recognized. The
  complete 120-root catalogue, all eighteen actual signed actions and the
  real root spans are proved. The 1,120-plane orbit, its coverage and the
  resulting spatial and full-axis stabilizer orders remain open.
- Eighth: all 2,576 genuine Golay dodecads, the 1,288-element point-stabilizer
  orbit and its original-generator transition forest are proved. The actual
  permutation flag stabilizer has order 7,920. The full actual matrix
  stabilizer has order 32,440,320 in Co0 and 16,220,160 in Co1. Full-axis
  projection containment and exact kernel/range factorization are proved;
  the numeric extraspecial kernel, projection surjectivity and local orbit
  count remain open.
- Global coverage: nineteen genuine fifth-family generators are proved to
  generate the entire projected stabilizer, and fourteen candidate roots
  are certified as actual norm-eight roots. The first actual projected
  binary orbit has 120 elements. Complete fourteen-orbit coverage, real
  triality transports, all twelve axis classes, all ten feasible classes
  and both global orbit totals remain open.

Independent approvals:

- Fifth full lifts and local order:
  https://artifacts.internalmeta.com/a/2164026557848918
- Sixth phase scope:
  https://artifacts.internalmeta.com/a/1110012125334638
- Seventh full tensor/kernel and spatial recognition, including the docstring repair:
  https://artifacts.internalmeta.com/a/1457989573059091
- Eighth coordinate and matrix-recognition scopes:
  https://artifacts.internalmeta.com/a/1479217804051026
- Eighth actual dodecad orbit and flag order:
  https://artifacts.internalmeta.com/a/2036299670408744
- Eighth full spatial stabilizer and projection containment:
  https://artifacts.internalmeta.com/a/1118151963929009

Verification: the canonical FLM collection build passed 11,646 jobs. All
48 changed Lean modules passed fifteen linters: 406 declarations, consisting
of 232 authored and 174 generated declarations, with zero errors. The strict
recursive audit passed 97,896 private/generated declarations using only the
three standard axioms, excluding exactly the existing T4 and T6 endpoint
values. Preflight passed. No new proof gaps were introduced.


## Working progress toward T4 (2026-10-19)

T4 remains open. Eight of the twelve actual local axis orbit counts are proved;
this fraction measures that component, not completion of the order theorem.
T1–T3 and T5 remain proved for the implemented coordinate model. T6 is open.
All six active agents are assigned to T4.

- Sixth: the actual full-axis stabilizer has order 73,574,645,760 and its
  actual H orbit has 1,896,194,506,752,000 elements.
- Seventh: the actual full-axis stabilizer has order 318,504,960 and its
  actual H orbit has 438,020,931,059,712,000 elements.
- Eighth: the actual full-axis stabilizer has order 16,220,160 and its
  actual H orbit has 8,601,138,282,627,072,000 elements.
- Source position 9 (the Ninth prototype): all 4,136 original signed-short
  source rows, the complete 960-state spread certificates, and actual binary
  E8 root-range preservation are proved. Eleven compact lifts have genuine
  local-fiber compatibility and the intended original Conway projections.
  All eleven original candidate projections are now exact words in
  candidates 0, 9, and 10. A checked lower-bound assembly requires exactly
  those three genuine full-axis fixers. The unconditional actual projected and
  full H stabilizer upper bounds are now proved; the full H bound is 92,897,280.
  Complete C/T fixation, remaining short source bindings, and the attained
  matching lower bound remain open.
- Candidate for source position 10 (the actual FifthRoot8 positive-triality prototype):
  the original positive-root Co0 subgroup has order 42,305,421,312,000.
  The entire actual paired norm-six catalogue has 953,856 elements and is
  proved to be one orbit, with point stabilizer order 44,352,000. Four
  genuine matrix-flag orientations give the complete original Co0 matrix
  stabilizer order 177,408,000. Independent adversarial review approved
  all 34 new norm-six and matrix-extension modules. The actual full-axis
  extraspecial kernel now has exactly two elements. Its genuine nonidentity
  fixer is obtained from an original complete Fifth fixer by the actual Q word
  and triality relation. The whole H stabilizer is at most 177,408,000;
  independent adversarial review approved that upper bound. The complete actual
  incoming C cache and eight-factor incoming T formula are proved. Every genuine
  norm-four/norm-six flag of pairing sixteen also has an exact 100-point lattice
  catalogue, action, and transport. A literal original local word transports
  the root-eight flag to canonical coordinates. The actual Mathieu point stabilizer has
  orbits of sizes 1, 77, and 22 and is maximal in the actual flag group.
  A literal original Conway element moves its pair point and generates the full
  flag group together with that point stabilizer. These are lattice/group results;
  complete axis fixation for those generators remains open. Full Q comparison
  also binds the compact original incoming spin operator to a genuine local
  fiber; its positive-triality destination lies in the actual root-eight H orbit
  by a transporter with trivial Conway projection. The original central sign
  is retained throughout this comparison.
  The complete 135-letter canonical Q replay is now proved, retaining
  all central phases. The original Mathieu point subgroup is now generated
  by two explicitly checked original words. The full positive canonical spatial
  matrix, the complete incoming tensor address map, its source initialization,
  and all four incoming Fourier pairs are checked. Every actual positive incoming
  and final triality tensor coordinate now has its proved integer formula. Both
  reduced Mathieu generators have genuine full-Q actions, exact projections,
  and matrix fixation. Their complete short and tensor fixation remains open.
  The original mover and mate also have fully proved compact full-Q source actions
  and complete actual canonical matrix fixation. The entire positive canonical
  tensor now has its unconditional exact integer formula: the original full
  source, four Fourier pairs, post action and spatial action are all proved.
  Its complete 98,304-coordinate integer cache is also proved. Every actual
  final short coordinate has its exact integer formula, and all 759 by 64
  packed original incoming octad coefficients are bound to their actual source.
  Full short cache binding and actual C/T fixation of the generators remain open.
  Attaining all 88,704,000 matrix-quotient
  values by full-axis fixers, and the resulting exact local orbit count, remain open.
- Candidate for source position 11 (the Twelfth prototype): the complete original Co0
  matrix stabilizer has order 7,372,800; the actual Q stabilizer is trivial.
  The actual H stabilizer is therefore at most 3,686,400. The entire genuine
  incoming C cache is proved, including all zero coefficients. Every one of the
  twelve actual candidate projections is a literal positive word in the first
  three. A checked assembly derives the matching actual H order from exactly
  three genuine full-axis fixers. Complete C/T fixation of those three
  candidates and the attained matching lower bound remain open.
- Candidate for source position 12 (the Tenth prototype): the actual Q stabilizer is
  trivial. A complete certified original Leech isometry now transports the
  seven-pair eigenspace to its genuine octad E7 hyperplane; the exact projector
  and distinguished-line transport are proved. Every actual original matrix
  fixer now preserves the transported full octad E8 section and the outside
  norm-twelve unsigned line, using the genuine E7 slice and orthogonality.
  The entire actual pointwise E8 subgroup has order 512; its full unsigned-line
  kernel is exactly two elements and its full actual unsigned-line orbit has
  256 elements. Its sign subgroup separately has order 32. The complete actual
  E7 preferred root-line set has 63 elements and is one orbit of the entire
  actual matrix group. All original integral edge actions, positive-normal
  witnesses, whole-set preservation and original matrix transport are proved.
  The full matrix count is reduced to 63 times its actual root stabilizer.
  The monomial anchor count, attained projected stabilizer order and complete
  actual local axis count remain open.
- The older Eleventh prototype at root 3 has original Co0 matrix stabilizer
  order 159,252,480. It is not the missing source-position-10 candidate;
  source-position-10 work uses the actual root-8 prototype above.
- Odd global coverage: all 128 finite forest batches and their unconditional
  actual coverage join are proved. All eighteen actual signed Odd transition
  destinations are proved, including the final root 3 negative endpoint.
- Feasible axes: five of ten local classes are proved. The secondary return
  count is 925; its full local orbit has 93,150 elements. The genuine secondary
  nonpair catalogue is partitioned into signed sectors of sizes 4,928,
  42,240, and 45,056, with actual binary independence proved. The entire actual
  45,056-element, 4,928-element, and 42,240-element sectors are each complete
  genuine local orbits, and their triality destinations are proved. The actual
  disjoint-pair sector is also a complete 924-element orbit with its original
  triality destination proved. Each signed mate is an actual singleton orbit.
  The six orbits are pairwise disjoint and cover all 93,150 secondary inputs.
  Their source triality destinations are proved, including both mates. Exactly five
  distinct actual A destinations occur, with both coverage and attainment proved.
  The three nonpair transition fibers have exact vector and coset counts
  4,928, 42,240, and 45,056, with genuine reverse orbit-balance equations.
  The containing-octad actual A stabilizer has order 97,409,858,273,280;
  its actual orbit has 7,286,400 elements, and the reverse transition count is 63.
  These conclusions use the genuine simultaneous axis transport and complete
  original Q kernel. The outside-octad actual A stabilizer has order
  2,705,829,396,480; its actual orbit has 262,310,400 elements, and its
  reverse transition count is 15. The entire original orthogonal flag and
  its full extraspecial kernel are identified. The odd-destination actual
  A stabilizer has order 169,114,337,280; its actual orbit has 4,196,966,400
  elements, and the reverse transition count is 1. All five destinations
  from the secondary column now have actual A counts. The containing class
  now maps surjectively onto its complete 56,925-element actual section orbit,
  with exactly 128 actual axes in every fiber; the original spatial lift and
  simultaneous source conjugation are bound explicitly. The complete 77 by 128
  coordinate phase catalogue is proved. The entire containing self-return has
  4,928 vectors and 63 original cosets, with actual mate recognition proved.
  A genuine sixth feasible destination is distinct from all five previous ones;
  its first coefficient is 1/8. The full original residual containing-input
  coefficient fibers 0, 1/8 and 1/4 have exact counts 4,320, 64,512 and 24,192.
  These are coefficient fibers; their full class recognition and transitivity
  remain obligations. The complete original E7 projection catalogue and
  genuine positive-normal transport are being used for that recognition.
  Classification of the later
  classes, complete transition equations,
  global coverage,
  and the global feasible-axis count remain open.

The final global axis count, feasible-axis count, Monster-order assembly,
and independent review of the completed T4 proof are still required.
Candidate matrix counts and numerical discoveries are not actual-axis
stabilizer proofs. Comparison with the primary FLM construction also remains
unproved, as described in the source and coverage notes above.

Verification boundary: this summary includes frozen working-tree results
beyond the integrated checkpoint. The integrated frozen checkpoint passes
its canonical collection build (14,162 jobs), a recursive audit of 133,267
private/generated declarations using only the three standard axioms with
exactly the existing T4/T6 endpoint values excluded, and all fifteen linters
on 35,332 declarations in 2,515 changed Lean modules with zero errors.
Collection consistency, whitespace, and disk/index source hashes also pass.
Later working-tree results are integrated only after their own canonical,
private/generated axiom, fifteen-linter, and source-hash gates close.

The independent norm-six and original matrix review separately verified
327 declarations with only the three standard axioms and all fifteen linters
with zero errors; it approved the exact stated scope without supplying the
remaining full-axis recognition hypotheses. Its report is at
https://artifacts.internalmeta.com/a/1844388163425133 .
Independent review also approved nineteen secondary feasible-orbit modules and
three canonical root-eight transport modules: fresh isolated compilation,
308 private/generated declarations with only the three standard axioms, all
fifteen linters with zero errors, and unchanged source hashes. The report is at
https://artifacts.internalmeta.com/a/2192680081319518 . Its scope excludes
full-axis C/T fixation and the final global counts.
The complete new checkpoint has not yet been independently reviewed.
A broader legacy transition-dependency lint run found 164 existing missing
source-documentation flags and three simplifier-normal-form flags; the
newly gated transition scopes have zero lint errors. T4 and T6 remain open.
