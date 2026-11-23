# Classical algebraic K-theory

Exact-category and Waldhausen constructions, comparison maps and field
computations retain their actual objects, morphisms, basepoints, stage
parameters and coefficient maps.

## Selected source scope

The selected mathematical inventory contains 2,458 production modules and
889 public client modules, totaling 919,070 physical Lean lines.

## Main results

- `quillenOriginalQSLoopHomotopyEquiv`: Quillen/S loop comparison for a general
  additive exact category with its standard Waldhausen structure, with whole
  maps, inverse homotopies, naturality and the specified unit paths.
- `quillenIndependentPlusEquivalence_exists`: the projective Quillen loop
  space of an associative unital ring is homotopy-equivalent to the fixed
  `K₀` factor times the independently constructed cell-plus model, preserving
  the `K₀` coordinate on every source point.
- `matsumotoAddEquiv_unconditional`: the Milnor/algebraic `K₂` equivalence for
  fields, with the actual comparison/reverse maps and forward naturality.
- `fieldRankEquiv` and `scalarExtensionK0_coefficient_dictionary`: field `K₀`
  is `ℤ`, with native scalar extension equal to the identity under the charts.
- `K1.detEquivUnitsOfField`: field `K₁` is the additive copy of its unit group.
  `K1.detEquivUnitsOfField_mapRingHom` preserves the coefficient square for
  independently chosen field universes.
- `K2.finiteField_eq_one`: every element of algebraic `K₂` of a finite field
  is the identity.

## Comparisons

For an additive exact category `C` with its standard Waldhausen structure,
the Quillen and S-construction loop models are related by the specified comparison maps and both inverse
homotopies. The comparison is natural under additive exact functors; its
basepoint and unit paths are part of the same map family.

For an associative unital ring `R`, the projective Quillen loop space is
homotopy-equivalent to `K₀(R) × BGL(R)⁺`. The plus factor is constructed
independently. The equivalence includes whole forward/inverse formulas,
both point-relative inverse families and preservation of the fixed `K₀`
coordinate on every source point.

## Ring and field computations

`K₂(R)` is the categorical kernel of the stable map `St(R) → E∞(R)`.
The canonical comparison identifies it with the corresponding subgroup
kernel and retains the kernel inclusion and coefficient maps.

For a field `F`, Matsumoto's comparison and reverse maps give
`MilnorK F 2 ≃+ Additive (K2 F)`. The forward equivalence is natural for
same-universe field homomorphisms. Its symbols satisfy bilinearity and the
Steinberg relation.

Projective dimension gives `RingK0 F ≃+* ℤ`, and determinant gives
`K1 F ≃+ Additive Fˣ`. Under the field `K₀` charts, the original scalar-
extension map is the identity on `ℤ`; the field universes remain independent.
Stable and `K₁` determinants commute with coefficient maps between
commutative rings. The field-unit charts preserve these maps for independent
field universes. For a finite field, every `x : K2 F` satisfies `x = 1`.

## Module guide

| Subject | Mathematical API and source |
| --- | --- |
| Exact/Waldhausen structures and finite S-stages | [Exact category](../CategoryTheory/ExactCategory/Basic.lean), [Waldhausen category](../CategoryTheory/Waldhausen/Basic.lean), [Finite stage](../CategoryTheory/Waldhausen/SConstruction/FiniteStage.lean) |
| Quillen/S loop comparison and naturality | [Loop comparison](Exact/Quillen/QuillenOriginalQSLoopComparison.lean): `quillenOriginalQSLoopHomotopyEquiv`, `quillenOriginalQSMixedLoopHomotopy`; [Unit coherence](Exact/Quillen/QuillenOriginalQSComparisonOwnUnit.lean) |
| Ring Q/plus comparison | [Independent-plus comparison](Ring/Comparison/QuillenIndependentPlus.lean): `quillenIndependentPlusEquivalence_exists` |
| Ring K₂ kernel and plus comparison | [Kernel](Ring/K2/Basic.lean), [Steinberg/Quillen comparison](Ring/K2/SteinbergQuillenComparison.lean) |
| Matsumoto's theorem | [Field symbol equivalence](Ring/K2/MatsumotoEquivalence.lean): `matsumotoAddEquiv_unconditional`, `matsumotoAddEquiv_mapRingHom` |
| Field K₀ and coefficient maps | [Integer rank chart](Ring/K0/FieldCoefficient.lean): `fieldRankEquiv`; [Independent field coefficients](Ring/K0/FieldCoefficientIndependent.lean): `scalarExtensionK0_coefficient_dictionary` |
| Field K₁ | [Determinant chart](Ring/K1/Field.lean): `K1.detEquivUnitsOfField` |
| Independent determinant/coefficient maps | [Determinant scalar map](Ring/K1/DeterminantScalarMap.lean): `StableGL.det_comp_scalarMap`, `K1.detHom_comp_mapRingHom`, `K1.detEquivUnitsOfField_comp_mapRingHom` |
| Finite-field K₂ | [Finite-field computation](Ring/K2/FiniteField.lean): `K2.finiteField_eq_one` |

The corresponding examples live in [MathlibExtTest](../../MathlibExtTest/),
including [determinant coefficient clients](../../MathlibExtTest/KTheory/Ring/K1/DeterminantScalarMapTests.lean)
and [Matsumoto clients](../../MathlibExtTest/KTheory/Ring/K2/MatsumotoTests.lean).
The latter check symbol order, both inverse identities, application/type
inference and field-homomorphism naturality.

## Sources

- Charles A. Weibel, *The K-book: An Introduction to Algebraic K-theory*,
  Graduate Studies in Mathematics 145, AMS, 2013: II §§2, 7 and 9;
  III §§1 and 6; IV §§6–8.
  [Author's edition](https://sites.math.rutgers.edu/~weibel/Kbook/Kbook.pdf).
- Daniel Quillen, *Higher Algebraic K-Theory I*, Lecture Notes in Mathematics
  341, Springer, 1973, pp. 85–147, §2.
- Friedhelm Waldhausen, *Algebraic K-theory of spaces*, Lecture Notes in
  Mathematics 1126, Springer, 1985, pp. 318–419, §1.

Applicable copyright, license and required source-attribution notices are
preserved in the source files and [NOTICE](../../NOTICE).
