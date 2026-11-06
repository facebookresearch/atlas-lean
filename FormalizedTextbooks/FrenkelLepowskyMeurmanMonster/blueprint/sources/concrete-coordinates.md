# Supplementary coordinate and presentation sources

The primary project reference remains FLM (1988). Its relevant construction
chapters have not been read in this follow-up. These supplementary sources
supply explicit definitions; comparison with FLM remains an obligation.

## Seysen: coordinate lattice, representation, and triality

Martin Seysen, *A computer-friendly construction of the monster*,
[arXiv:2002.10921v3](https://arxiv.org/html/2002.10921v3), version 3,
13 May 2020. The complete HTML text was inspected through the supported
MASE CLI reader.

### Section 6.1: the Leech lattice

Let C be the binary Golay code on 24 coordinates. Integral coordinates u
satisfy the lattice condition exactly when there are m in {0,1} and c in C
with

- u_i = m + 2 c_i modulo 4 for every i;
- the sum of the u_i equals 4m modulo 8.

The actual vectors in standard Euclidean coordinates are u divided by
sqrt(8). This makes the Euclidean pairing the coordinate dot product
divided by 8, matching the source normalization.

`LeechCongruences` uses integer coefficients for the Golay generators.
Their residues modulo 2 encode the binary word. Allowing any integer m
makes closure under addition and integer scaling immediate. Generator 11
is the all-one word, so a shift of m by 2 is absorbed into that generator.
`leechCongruences_normalize` proves the restriction to m = 0 or 1, and
`mem_leechIntegral_iff_source` proves equivalence with the exact binary-code
source condition. `LeechLattice` is the image of this integral module under
the normalized real embedding.

The integral rank is now proved to be 24 by bounding it between the ambient
module and its copy obtained by multiplication by 8. The actual quotient
Λ/2Λ and its 24-dimensional binary linear coordinates are also constructed.
The minimum integral squared norm 32 (real squared norm 4) is now proved
from the Golay code weights. Unimodularity, evenness, and historical comparison
with the primary FLM lattice remain separate theorem obligations.

### Golay generator data

The twelve explicit generators are from Martin Seysen's mmgroup repository,
[`docs/source/golay_basis_data.inc`](https://github.com/Martin-Seysen/mmgroup/blob/728688938a1c9fd27f3aee9b63464ea6b8d17965/docs/source/golay_basis_data.inc),
commit `728688938a1c9fd27f3aee9b63464ea6b8d17965`. Coordinates use the
column-major MOG convention, with coordinate 0 the least significant bit.
The implementation includes the masks, binary linear encoder, and its range.
No claim of a proved minimum-distance or dimension theorem is made here.

### Section 7.4 and Section 8.1, Table 5: dictionary basis and form

The 196884-space decomposes into:

- 24 diagonal symmetric-square coordinates;
- three blocks of 276 coordinates, named A, B, C in the dictionary;
- 759 octad blocks, each with 64 coordinates;
- three signed dictionary blocks, each of dimension 2048 times 24.

The A/B/C dictionary vectors are `(ij)_1`, `X_ij - X_ij^+`, and
`X_ij + X_ij^+`. Section 7.4 gives squared norms 2 for `(ij)_1`, and 1
for each of the mutually orthogonal X vectors. Thus the dictionary A/B/C
vectors all have squared norm 2 and remain mutually orthogonal. Diagonal,
octad, and signed X/Y/Z dictionary vectors have squared norm 1.

`griessForm` is the diagonal pairing with these weights, using the explicit
block indexing of `Triality.lean`. Bilinearity is proved. Compatibility with
the FLM form and the eventual product normalization is not assumed.

### Section 8.1, equations (8.1.1)–(8.1.4): triality

The triality fixes the diagonal block and cycles A/B/C and the signed X/Y/Z
blocks in the order specified in equations (8.1.2) and (8.1.3).

For an octad, even subsets are identified with their complements. Choose
the representative with last bit zero. The first six bits are arbitrary,
and bit six is their parity. These are the 64 explicit representatives
`trialityEvenMask`.

The Fourier matrix has coefficient
`(-1)^(size(delta intersection epsilon))`, scaled by 1/8.
The diagonal sign is `(-1)^(size(delta)/2)`. The implemented octad operation
applies the Fourier transform followed by the signs, using the source's
right-action convention `tau = y_tau x_tau` in Section 8.1.

The matrix is a row permutation of the sixfold Sylvester Hadamard matrix.
This equality and the row permutation's inverse are kernel-checked finite
statements. The orthogonality proof then uses Mathlib's Kronecker Hadamard
theorem, rather than a large multiplication check or `native_decide`.
The resulting real linear equivalence has a proved inverse.

The octad blocks have identical formulas, so ordering the 759 octads does
not affect the block operator. The matching of their coordinate labels to
the eventual FLM product must nevertheless be recorded in the full source
comparison. The triality definition does not assume product preservation.

### Remaining product and extension work

This version of Seysen's paper gives the representation and triality but
not a complete Griess multiplication table. The mmgroup documentation,
[`guide_math_implement.inc`](https://github.com/Martin-Seysen/mmgroup/blob/728688938a1c9fd27f3aee9b63464ea6b8d17965/docs/source/guide_math_implement.inc),
explicitly states that general Griess multiplication is not implemented.
It also notes sign and scaling differences between constructions.

Section 9.3 describes the actual local group as a central quotient of a
fiber product of the 4096-dimensional Clifford group and the Leech lattice
isometry group over Co1. The Clifford group alone is not isomorphic to the
local group. The local definitions must include that compatibility and the
comparison with the current plus-type coordinate model Q.

The primary FLM construction chapters, or a readable complete multiplication
source with an audited comparison route, remain necessary.

## Basak: independent classical presentation reference

Tathagata Basak, *The complex Lorentzian Leech lattice and the bimonster (II)*,
[arXiv:0811.0062v2](https://arxiv.org/html/0811.0062v2), 14 November 2008,
Section 1.1, the Ivanov–Norton presentation theorem. This passage was read
through the supported MASE CLI reader.

The tree has sixteen vertices: a and three arms
`b_i, c_i, d_i, e_i, f_i`. Basak calls it M666, counting the central
vertex in each arm; the usual name Y555 counts the five remaining vertices.
All generators are involutions. Adjacent generators braid, equivalently
have product cubed equal to 1; nonadjacent generators commute, equivalently
have product squared equal to 1. The additional relator is

`(a b_1 c_1 a b_2 c_2 a b_3 c_3)^10 = 1`.

The source identifies this presentation with the bimonster M wreath C2.
The Lean definition `BimonsterPresentation` imposes exactly these relators
using `PresentedGroup`; it does not assume the identification theorem.

The reference `classicalMonster` centralizes a in the presented group and
quotients by its cyclic subgroup. This subgroup is central in its own
centralizer, and its normality is proved in Lean.

The following recognition arguments remain to be formalized:

1. Prove the Ivanov–Norton presentation theorem, following the references
   cited in Basak Section 1.1.
2. In the wreath-product model, show a is an outer involution. Since the
   diagram is connected, all generator images in the C2 quotient have the
   same parity; surjectivity forces that parity to be nonzero.
3. An outer involution in M wreath C2 is conjugate to the factor swap. Its
   centralizer is the diagonal M times C2, and quotienting by the swap gives M.
4. Prove T6's comparison with the FLM-generated group G.

This reference construction has no dependency on G, the incomplete Griess
product, or the local-action placeholders. No recognition statement or
isomorphism is introduced as an axiom.

## Explicit Schrödinger realization (Seysen §9.1)

In the coordinate model write a group element as `(a,b,c)`, where a and b
are twelve binary coordinates and c is its central bit. On functions of
`t ∈ F₂^12`, define

`R(a,b,c) f(t) = (-1)^(c + b·t) f(t+a)`.

Composing two such operators introduces `a·b′`, exactly the implemented
cocycle `qBeta`. The homomorphism and inverse laws are proved. Applying an
operator to the constant function recovers c and b; applying it to the
indicator of zero recovers a. This proves faithfulness. Translation
permutations and signs prove preservation of the Euclidean pairing.

The orthogonal normalizer of its image defines `spinHolomorphSubgroup`.
The conjugation homomorphism on Q is obtained using Mathlib's subgroup
normalizer action and the proved equivalence of Q with its image.
Identifying this basis with the Parker-loop basis is still required.

## Conway: complete multiplication source recovered

J. H. Conway, *A simple construction for the Fischer-Griess monster group*,
Inventiones Mathematicae 79 (1985), 513–540,
[DOI 10.1007/BF01388521](https://doi.org/10.1007/BF01388521).
The public Göttingen scan is
[GDZ article record](http://gdz.sub.uni-goettingen.de/dms/resolveppn/?PPN=GDZPPN002101394).
The viewer's public IIIF manifest for volume 79 is
[PPN356556735_0079](https://manifests.sub.uni-goettingen.de/iiif/presentation/PPN356556735_0079/manifest).
Printed pages 513–540 correspond to scan images 519–546. The article images
were inspected directly after the text reader returned only the viewer shell.

Section 9, page 524, constructs the local covering group as the fiber product
of the 4096-dimensional group and the lattice isometry group over Co1.
Section 11 quotients by the common diagonal central sign to obtain the
local group acting on 196884-space. These are the required ingredients of H.

Section 10 fixes the orthogonal decomposition
`300 + 98280 + 98304`: symmetric matrices A, signed short-vector basis X_r,
and tensors q⊗λ. Section 11's dictionary is the same dictionary underlying
Seysen's Table 5 and the current `Triality.lean`.

Section 12, page 526, gives all six multiplication cases in its source
inner-product and tensor conventions (these displayed rules precede the
conversion to the implemented unit dictionary coordinates):

- `A * A′ = 2(AA′ + A′A)`.
- `A * X_r = (A, λ_r⊗λ_r) X_r`.
- `X_r * X_s` is `±λ_r⊗λ_r` if the label product is ±1, the basis vector
  `X_(r·s)` if that label is short, and zero otherwise.
- `A * (q⊗λ) = q⊗(λA) + (tr A)/8 · (q⊗λ)`.
- `X_r * (q⊗λ) = q′⊗[λ - 2(λ,λ_r)λ_r]/8`, where q′ is the action of x_r on q.
- Tensor times tensor has symmetric-matrix component
  `(q,q′)[(λ,λ′)I + 4λ⊗λ′ + 4λ′⊗λ]` and short-vector component
  `Σ_r (q^r,q′)[(λ,λ′)-2(λ,λ_r)(λ′,λ_r)] X_r / 2`.

The matrix of an integral-coordinate tensor λ⊗λ is `λ_i λ_j / 8`,
as explained on page 525. The integral lattice coordinate frame has basis
norm `1/√8` (Seysen §6.1); the monomial 24-space basis of §7.3 and the
dictionary tensor basis of §7.4 are declared orthonormal. These coordinate
conventions must be distinguished when transcribing the displayed tensor rule.
In the implemented unit dictionary coordinates, both tensor-times-tensor
contractions carry `1/8`, as checked against Conway Appendix 5 below.
The identity of the algebra is `I/4` (page 528).

The six rules are implemented in `conwayRawProduct`. `griessConwayEncode`
and `griessConwayDecode` use the explicit dictionary, preferred short labels,
and partial Fourier transform in the all-one code coefficient. The resulting
structure constants define `griessProd`, with bilinearity proved. These
construction declarations have no `sorryAx` dependency. Both dictionary
conversion inverse laws and linearity are proved. `rhoLocal` combines the
symmetric-matrix pullback, signed short-vector permutation, and spin-tensor
actions, transported through this equivalence. Its composition and inverse
laws, and its descent through simultaneous signs, are proved.

## Tits: a second multiplication formulation

Jacques Tits, *Le monstre*, Séminaire Bourbaki, exposé 620,
Astérisque 121–122 (1985), 105–122,
[public PDF](https://www.numdam.org/article/SB_1983-1984__26__105_0.pdf).
The full public PDF was retrieved; pages 112 and 119 were inspected visually
because the text extraction omits the displayed multiplication table.

Page 112 defines six symmetric cubic components on
`B = Sym²_0(L) ⊕ B₂ ⊕ (L⊗V)`. Its linear combination is
`τ = 4τ₁ + τ₂/8 + τ₃/128 + τ₄ + 24τ₅/64 - τ₆/64`.
Page 119 extends to `B ⊕ ℚ·1` with product
`(b+q1)(b′+q′1) = τ(b,b′)/8 + qb′ + q′b + (b+q1,b′+q′1)/3 ·1`.
Its extended pairing restricts to `1/128` of the pairing on B and has
`(1,1)=3`. This differs from Conway's basis scale; no equivalence is assumed.

## Explicit integer basis and source hyperbolic frame

`LeechBasisData.lean` supplies a column Hermite matrix derived from
8e₀, 4(eᵢ−e₀), twice each published Golay generator, and (-3,1,…,1).
Each of its 24 columns is independently checked against the exact Leech
congruences using explicit Golay coefficient masks. Its scaled Gram matrix
and the source's invertible binary matrix are checked by Lean's kernel.
The 37 natural generators have verified integer coordinates, and the general
spanning argument and independence prove that this is an integer basis.

The binary frame is determined by the published cocode basis and Parker
cocycle rows in `golay_basis_data.inc`: first x̃_b = x_b x_θ(b), then x_c.
Their physical coordinates, integer-basis coordinates, Gram matrix,
binary reduction, and inverse are verified in the kernel. Its diagonal
Gram entries are divisible by four, and its polar matrix modulo two is the
standard twelve-pair hyperbolic matrix. The minimum norm and the complete,
unique catalog of short vectors modulo global sign are now proved. Their
actual classes modulo 2Λ define the preferred short lifts and give the Co₀
permutation action. `LeechQuadratic.lean` proves the general lattice
half-norm comparison with the fixed hyperbolic binary form.

`H` is the source fiber product of the actual orthogonal Schrödinger
normalizer with the actual Leech isometry group, over their binary actions,
modulo simultaneous scalar signs. The diagonal subgroup's normality and
its containment in the projection kernel are proved. The resulting type,
group laws, `inclQ`, and `projH` have no `sorryAx` dependency.

## Proof-stage normalization audit: Conway Appendix 5

Conway, printed page 536, Calculation (1), expands the square of a unit
signed dictionary tensor. Its matrix contribution has diagonal coefficients
`9/8` at the selected coordinate and `1/8` at every other coordinate. This
exposed an error in the earlier transcription, which used unit tensor
coordinates while omitting the `1/8` factor on that matrix contraction.

The coordinate tensor-times-tensor matrix term is therefore

`[dot(v,w) I + 4 v⊗w + 4 w⊗v] / 8`,

summed over the unit spin basis. The short-vector contraction also carries
`1/8` in this coordinate normalization, rather than the earlier `1/2`.
This agrees with the appendix's pair-short coefficients `-3/8` and `1/8`
and with pairing the tensor/short rule against unit tensor vectors.
The tensor/short and matrix/tensor input rules retain their original factors.

`conwayPureTensor_unit_square_diagonal` in `TrialityInvariance.lean`
proves the diagonal normalization for every unit spin vector. This focused
check by itself does not establish all triality multiplication cases.
`TrialityFullProduct.lean` now proves every product case for the implemented
coordinate model, including the actual dictionary signs and Q selectors.
The comparison with the primary FLM construction remains a separate proof
obligation, as recorded in `GAPS.md`.


## Subsequent order and simplicity source

Gerald Höhn and Martin Seysen, *The Order of the Monster Finite Simple Group*,
[arXiv:2508.01037v1](https://arxiv.org/pdf/2508.01037), 1 August 2025.
The source concerns the same local-group-plus-triality coordinate construction.
Tables 2 and 4 give integer transition matrices of degrees 16584750 and 93150.
Their stationary count vectors, anchored at 196560 and 1, have totals
97239461142009186000 and 11707448673375. The present Lean modules transcribe
these mathematical tables and verify independently computed rational inverse
certificates. This checks the numerical counting step, not its application
or the source's computational certificates against the actual G.

Theorem 5.1 multiplies those two orbit counts by the common stabilizer order
`2^24 * |Co₂|`, with `|Co₂| = 42305421312000`. The needed Conway-group facts,
actual orbit coverage and transitions, and common-stabilizer identification
remain proof obligations. Section 5's simplicity proof uses the fusion of
three involutions and the local centralizer's normal-subgroup structure.
The generic fixed-point-free involution result used here is already in the
pinned Mathlib, and the fused-involution argument is instantiated in actual G.

The public companion repository was inspected at commit
`9d954ec8bd94c977e72e56d11d48dd8979e1014f`. Its source code and certificate
files have not been incorporated: no license file was found. The mathematical
tables above are attributed to the paper, and the rational inverses were
computed independently.
