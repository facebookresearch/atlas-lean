/-
Copyright (c) 2026 Andres Barei. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andres Barei
-/
import Appendix_FixedPoint.BezoutChain.Dimension.TriangularChain
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
import Mathlib.Algebra.Polynomial.Basis
import Mathlib.Data.Nat.Digits.Lemmas
import Mathlib.Order.KrullDimension
import Mathlib.RingTheory.Ideal.Lattice
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.Ideal.GoingDown
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
import Mathlib.RingTheory.IntegralClosure.GoingDown
import Mathlib.RingTheory.Polynomial.UniqueFactorization
import Mathlib.RingTheory.UniqueFactorizationDomain.GCDMonoid
import Mathlib.Algebra.GCDMonoid.IntegrallyClosed

/-!
# Fiber exhibit below a prime: `D ^ (i + 1)` recipe + flat going-down set-up
For `R = MvPolynomial (Fin m) K` with `[Field K] [Infinite K]` and prime `P`,
this file attacks the sole remainder of
`Formalization/Appendix_FixedPoint/BezoutChain/
Dimension/TriangularChain.lean`, namely deriving the
`fiber` monic element and the `exhibit` length-`(m - s)` chain below `P` from
the triangular data `(shear_idx, shear_exp, adm)` of `TriangularNormDatum`.

## Route

1. The collision-free `D ^ (i + 1)` shear-exponent recipe `shearExp`
   (`d i = D ^ (i.val + 1)` for `i ≠ j`, `0` at `j`; this replaces the dead
   `D ^ i` recipe whose `D ^ 0 = 1` collided with the fixed variable's weight):
   with `D ≠ 0` every off-`j` exponent is nonzero, i.e. the recipe discharges
   the `adm` field of `TriangularNormDatum` (`shearExp_adm`); with `1 < D`
   the powers are strictly monotone (`dpow_lt_of_lt`), no off-`j` weight is
   `1` (`shearExp_weight_ne_one`), and distinct off-`j` indices get distinct
   weights (`shearExp_weight_sep`) — the separation property the monic-fiber
   degree argument rests on.
2. The `fiber` field predicate is isolated as `fiberPred` (verbatim shape of
   the original datum `fiber` field, now refuted) and, after the weakening,
   as `fiberPredWeak` (verbatim shape of the weakened field: monic-in-`j`
   without univariateness in the shear contraction, plus the going-down
   integrality input) with projection `fiber_of_datum`; the recipe plus all
   datum components assemble to `TriangularNormDatum` via
   `datum_of_dpow_recipe`, thence to the height bound via
   `height_of_dpow_datum` (both in the exact shapes of `triangular_monic_chain`).
   The weakened fiber was refuted for the dead recipe at every `D`; for the
   `D ^ (i + 1)` recipe it collapses only at `D = 1` and is inhabited at
   `1 < D` on the diagonal test prime (see `## Obstruction`).
3. The below-`P` direction is set up through flat going-down:
   `goingDown_of_flat` (the `Algebra.HasGoingDown.of_flat` instance),
   the single-rung down-step `down_step_of_goingDown`
   (`Ideal.exists_ideal_lt_liesOver_of_lt`), and the full down-lift
   `down_lift_below` (`Ideal.exists_ltSeries_of_hasGoingDown`), which — unlike
   the going-up lift, whose pulled-back chains sit *above* `P` (coheight
   direction, already banked) — produces a same-length chain *ending* at the
   prime below which we build. The monic-fiber division step is discharged
   through `TriangularRegularity`'s (t2b) back-substitution by reference (cited, not
   imported), per the convention of `TriangularChain.lean`.

## What this file proves

* `shearExp`: the `D ^ (i + 1)` exponent recipe (replaces the dead `D ^ i`
  recipe).
* `shearExp_at_j` / `shearExp_adm`: the recipe is `0` at `j` and nonzero off
  `j` (the `adm` field shape for `shear_exp := shearExp j D`).
* `dpow_lt_of_lt`: strict monotonicity of `D ^ ·` for `1 < D` (separation).
* `fiberPred`: the `fiber`-field predicate, verbatim shape.
* `adm_of_datum` / `fiber_of_datum` / `exhibit_of_datum`: the triangular data
  project to exactly the `hnorm` field shapes they must derive.
* `goingDown_of_flat`: flat algebras satisfy going-down (the instance).
* `down_step_of_goingDown`: one rung of the going-down induction below `P`.
* `down_lift_below`: a base chain lifts to a same-length chain ending at the
  target prime (the below-`P` direction).
* `datum_of_dpow_recipe`: the recipe output feeds the `hnorm` fields exactly.
* `height_of_dpow_datum`: the assembled height bound (consumer shape).
* `shear_image_degreeOf_ge`: `degreeOf`-under-`triShear` for generators —
  the sheared generator has `j`-degree at least the shear exponent (via
  `triShear_coeff_shift`, closing obstruction item (i)).
* `shearExp_image_degreeOf_ge`: the bound at the recipe (`D ^ (i.val + 1)`).
* `shearExp_degreeOf_sep`: strict separation of the recipe lower bounds.
* `fiberPred_of_mem_univariate`: made-monic step — a univariate-off-`j`
  nonzero element of `P` normalizes to the `fiber` witness (first half of
  obstruction item (ii)).
* `exhibit_of_eq`: induction base case (`s = m`, singleton chain).
* `exhibit_extend_down`: one-rung downward extension preserving the last
  prime (induction step's order-theoretic content).
* `shearWeight`: the per-monomial shear weight (the `degreeOf`-under-shear cap).
* `shearFwd_generator_degreeOf_eq` / `shear_generator_degreeOf_eq`: generator
  `j`-degree equals the shear exponent (no `d i ≠ 0` needed).
* `shear_monomial_degreeOf_le` / `shear_image_degreeOf_le` /
  `shear_triShear_degreeOf_le`: per-monomial and general `degreeOf`-under-shear
  upper bounds (support-supremum of the weight).
* `shearWeight_single_off` / `shearWeight_single_at`: generator weights are
  the shear exponent off `j` and `1` at `j`.
* `shearExp_weight_ne_one` / `shearExp_weight_sep`: the `D ^ (i + 1)` recipe
  weights are collision-free for `1 < D` (the former `shearExp_weight_tie`
  is deleted — the tie is killed by construction).
* `spanSub_coeff_single` / `no_univariate_in_span_sub` /
  `fiberPred_false_span_sub`: the univariate-`fiber` refutation for
  `span {X₀ - X₁}`.
* `isSMulRegular_of_span_ringEquiv`: t2b-conclusion transport across a ring
  equivalence (bridge; `TriangularRegularity` stays cited, not imported).
* `fiberPredWeak`: the weakened `fiber`-field predicate, verbatim shape.
* `goingDown_of_normalization`: integrality ⇒ going-down for the
  normalization pair (integral over a UFD base, hence integrally closed).
* `triShear_recipe_span_sub_gen` / `triShear_recipe_span_sub_gen_one` /
  `contraction_recipe_span_sub_one` / `no_weakmonic_in_span_x0` /
  `weakFiberPred_false_new_recipe_one`: the weakened fiber is uninhabited
  for `span {X₀ - X₁}` at `j = 1`, `D = 1` (the dead recipe's every-`D`
  second refutation collapses to the `D = 1` boundary).
* `weakFiberMonic_new_recipe_of_lt`: production at `1 < D` — the weakened
  fiber's monic conjunct is inhabited for `span {X₀ - X₁}` at `j = 1` (no
  third counterexample: the recipe escapes within its operating range).
* `triShear_recipe_span_sub_gen_zero` / `contraction_recipe_span_sub_zero` /
  `no_weakmonic_in_span_x1` /
  `weakFiberPred_false_span_sub_recipe_zero`: mirrored collapse at `j = 0`,
  `D = 1`.
* `weakFiberMonic_escape_of_ne`: sharp boundary — a general shear with
  `d 0 ≠ 1` carries a weak-monic witness (the escape the dead recipe never
  takes; the new recipe takes it at `1 < D`).
* `carriedGen_coeff_top` / `carriedGen_coeff_x0` / `carriedGen_coeff_sub` /
  `carriedGen_coeff_other` / `carriedGen_support_sub` / `carriedGen_degreeOf` /
  `carriedGen_strong` / `carriedGen_strongMonic`: the carried generator
  `X₀ + X₁ ^ D - X₁` is strong-monic in `X₁` at `1 < D` (degree `D`, top
  coefficient `1`, all other support below `D`).
* `carriedGen_mem_recipe`: the carried generator lies in the recipe
  contraction.
* `delVarQuot_isIntegral_of_strongMonic`: strong-monic expansion — a
  strong-monic element of `Q` makes `delVarQuot j Q` integral (discharges
  the integrality conjunct of `fiberPredWeak`, exactly what going-down
  consumes).
* `fiberPredWeak_span_sub_recipe_of_lt`: test-prime fiber assembly — both
  `fiberPredWeak` conjuncts inhabited for `span {X₀ - X₁}` at `j = 1`,
  `1 < D`.
* `weightDigit` / `weightDigits`: digit function/list for the base-`D` weight
  reading (position `0` for `j`, `i.val + 1` off `j`, `0` skipped).
* `weightDigit_zero` / `weightDigit_succ` / `weightDigit_lt` /
  `weightDigits_length` / `weightDigits_mem_lt`: digit API.
* `ofDigits_map_range` / `weight_eq_ofDigits`: the recipe weight is
  `Nat.ofDigits D` of the digit list.
* `map_eq_of_mem` / `weight_injective_of_bounded`: base-`D` weight injectivity
  on `D`-bounded exponent vectors (via `Nat.injOn_ofDigits`).
* `shearExp_bounded`: per-`P` D-choice above all support coordinates.
* `shearWeight_recipe_eq`: recipe weight split (fixed part + off-`j` sum).
* `shearGen_ne_zero` / `shearFwd_monomial_eq_prod` / `degreeOf_pow_eq_of_ne` /
  `shear_monomial_degreeOf_eq`: monomial exactness (`degreeOf = weight`).
* `degreeOf_sum_unique_max` / `shear_poly_degreeOf_eq_of_unique_top` /
  `exists_maxWeight_of_bound` / `shear_poly_degreeOf_eq_of_bound` /
  `shear_production_degree`: unique-top extraction and general production,
  degree half.
* `shearGen_pow_eq_sum` / `shearFwd_monomial_expand`: support expansion of
  sheared monomials (product-of-sums over choice functions).
* `shearContraction_isPrime` / `shearPrime` / `shearPrime_strictMono` /
  `shearPrime_contraction` / `chain_transport_shear`: prime/chain transport
  along the shear (contraction to `P`).
* `exhibit_length_gain` / `exhibit_of_shear_chain`: length-gain rung and
  conditional exhibit assembly.
* `fiberPredWeak_of_strongMonic`: strong-monic element discharges both
  `fiberPredWeak` conjuncts.
* `hheight_of_production`: recipe-fed datum feeds `height_of_dpow_datum`
  (the `hheight` shape).
* `delVarPolyEquiv` / `delVar_compat` / `delVarLinearEquiv`: the delete-`j`
  inclusion presents `MvPolynomial (Fin m) K` as `B[X]` over the delete-`j`
  base, compatibly with the rename inclusion (hence free, hence flat:
  `delVarAlgebra`, `delVarFlat`).
* `hheight_of_eq`: induction base case (`s = m`) as an unconditional bound
  (reuses `exhibit_of_eq`).
* `hheight_step_flat`: induction step with all model instances discharged
  (only the production choice plus the below-positioned IH chain remain).

## Adjustments (no silent adaptation)

* `Algebra.HasGoingDown.of_flat` is an **instance**, not a lemma
  (`Mathlib/RingTheory/Ideal/GoingDown.lean`): `goingDown_of_flat` exposes
  it via `inferInstance` rather than applying it as a term.
* `TriangularChain.lean`'s `## Obstruction` discharges two fields
  unconditionally (`normap_of_prime` and `dir_of_finset`).
  `shearExp_adm` here supplies the recipe half for the
  `D ^ (i + 1)` choice; the all-ones
  choice is not formalized anywhere.
* `TriangularRegularity` (`t2b`) is cited, not imported (narrow imports).
* Namespace deviation: bare `EvolutionAlgebras.Appendix_FixedPoint.BezoutChain` does not mirror the
  module path, deliberately matching every other Track-B chunk file for
  consumer compatibility (same convention as `TriangularChain.lean`).
* Two narrow Mathlib imports added (`MvPolynomial.CommRing` for `coeff_sub`,
  `MvPolynomial.NoZeroDivisors` for `degreeOf_mul_eq`); `TriangularRegularity` stays
  cited, not imported (the bridge lemma is `Polynomial`/`triG`-free). No
  existing theorem, definition, or field was modified (all byte-identical).
* Reformulation attempt 1: four further narrow imports
  (`Ideal.GoingDown` was already present; added `IntegralClosure.GoingDown`
  for the normal-base going-down instance, `Polynomial.UniqueFactorization`
  for the `MvPolynomial` UFD instance, `UniqueFactorizationDomain.GCDMonoid`
  and `GCDMonoid.IntegrallyClosed` for the UFD-to-normal chain — all probed
  minimal: `IsIntegrallyClosed (MvPolynomial (Fin s) K)` fails to synthesize
  without them). `TriangularRegularity` stays cited, not imported.
* Field-shape change (forced by the `TriangularNormDatum.fiber` weakening in
  `TriangularChain.lean`, nothing else): `fiber_of_datum` now returns
  `fiberPredWeak m K P hnorm.shear_idx hnorm.shear_exp` (was the explicit
  univariate-`∃`); `datum_of_dpow_recipe` takes
  `fiber : fiberPredWeak m K P j D` (was the explicit univariate-`∃`).
  `height_of_dpow_datum` is unchanged (it passes `hnorm` whole — no forced
  edit). The original `fiberPred`, `fiberPred_false_span_sub`, and all
  earlier sections are byte-identical.
* No `haveILetI` suppressions: the TC-feeding steps use `have`/`let`
  (in Lean 4 these register local instances themselves, so synthesis
  is unaffected).
* Attempt-2 recipe replacement: `shearExp` is redefined from
  `D ^ i.val` to `D ^ (i.val + 1)` off `j`. Forced updates: `shearExp_adm`
  (now `pow_ne_zero`), `shearExp_image_degreeOf_ge` / `shearExp_degreeOf_sep`
  (now `D ^ (i.val + 1)`); `shearExp_weight_tie` (collision witness) deleted,
  replaced by `shearWeight_single_off` / `shearWeight_single_at` /
  `shearExp_weight_ne_one` / `shearExp_weight_sep`; the recipe-dependent
  `span {X₀ - X₁}` computations re-proved (`triShear_recipe_span_sub_gen`
  now carries `X₀ + X₁ ^ D - X₁`; the contraction equality and the
  `∀ D` refutation collapse to their `D = 1` versions
  `triShear_recipe_span_sub_gen_one`, `contraction_recipe_span_sub_one`,
  `weakFiberPred_false_new_recipe_one`); the `j = 0`, `D = 1` mirror keeps
  its statements (exponent proofs updated to `1 ^ (1 + 1)`). New: one narrow
  import (`IntegralClosure.Algebra.Basic` for `IsIntegralElem.add/mul`).
  `TriangularChain.lean` needs no field change (only its `## Obstruction`
  note is updated); `datum_of_dpow_recipe` / `height_of_dpow_datum` keep
  their shapes (the recipe name and type are unchanged).

## References

* `Formalization/Appendix_FixedPoint/BezoutChain/Dimension/TriangularChain.lean`,
  `TriangularNormDatum`, `triangular_monic_chain`, `triShear`,
  `triShear_backsubst`, `normap_of_prime`, `dir_of_finset`.
* `Formalization/Appendix_FixedPoint/BezoutChain/
  Regularity/Avoid/TriangularRegularity.lean`,
  `triG_isSMulRegular_mod_of_dvd` (t2b monic-fiber division step; cited, not
  imported). Exact shape (variables `{S: Type*} [CommRing S] [IsDomain S]
  [UniqueFactorizationMonoid S]`, namespace
  `EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.Triangular`):
  `triG_isSMulRegular_mod_of_dvd {F0 F1 a0 a1 L0: S} (hF0: F0 = a0 * L0)
  (hM: a0 * F1 - a1 * F0 ≠ 0) (hprime0: Prime a0) (hndvd: ¬a0 ∣ a1):
  IsSMulRegular (Polynomial S ⧸ Ideal.span {triG F0 a0})
  (Ideal.Quotient.mk (Ideal.span {triG F0 a0}) (triG F1 a1))`, where
  `triG Fc a = Polynomial.C Fc - Polynomial.C a * Polynomial.X` models
  `Gᵢ = Fᵢ(x) − z·xᵢ`. Carrying its conclusion back to `MvPolynomial` needs the
  last-variable isomorphism, which `TriangularRegularity.lean` itself records as a
  follow-up ("not claimed here").
* `Mathlib/Algebra/MvPolynomial/Degrees.lean`, `MvPolynomial.monomial_le_degreeOf`,
  `MvPolynomial.degreeOf_C_mul_le` (support-to-`degreeOf` bridge for (v)-(vi)).
* `Mathlib/Algebra/MvPolynomial/Basic.lean`, `MvPolynomial.mem_support_iff`,
  `MvPolynomial.coeff_C_mul`, `MvPolynomial.C_ne_zero` (used in (v)-(vi)).
* `Mathlib/Order/RelSeries.lean`, `RelSeries.singleton` (+ `last_singleton`),
  `RelSeries.append` (+ `head_append`, `last_append`, simps `append_length`)
  (used in (vii)).
* `Mathlib/RingTheory/Ideal/GoingDown.lean`, `Algebra.HasGoingDown`,
  `Algebra.HasGoingDown.of_flat` (instance), `Ideal.exists_ideal_lt_liesOver_of_lt`,
  `Ideal.exists_ltSeries_of_hasGoingDown`.
* `Nat.pow_lt_pow_right` (core Lean/Mathlib nat API).
* `Mathlib/Algebra/Order/GroupWithZero/Basic.lean`, `pow_pos`.
* `Mathlib/Order/KrullDimension.lean`, `Order.length_le_height_last`
  (consumed inside `triangular_monic_chain`).
* `Mathlib/Algebra/MvPolynomial/NoZeroDivisors.lean`,
  `MvPolynomial.degreeOf_mul_eq` (used in (x)).
* `Mathlib/Algebra/MvPolynomial/CommRing.lean`, `MvPolynomial.coeff_sub`
  (used in (x)).
* `Mathlib/Algebra/MvPolynomial/Eval.lean`, `MvPolynomial.aeval_monomial`
  (used in (viii)).
* `Mathlib/Algebra/MvPolynomial/Basic.lean`, `MvPolynomial.as_sum`,
  `MvPolynomial.ne_zero_iff`, `MvPolynomial.mem_support_iff`,
  `MvPolynomial.algebraMap_eq`, `MvPolynomial.coeff_X` (used in (viii)-(x)).
* `Mathlib/Algebra/MvPolynomial/Degrees.lean`,
  `MvPolynomial.degreeOf_add_le/mul_le/sum_le/prod_le/pow_le`,
  `MvPolynomial.degreeOf_X/X_self/X_self_pow/C`,
  `MvPolynomial.monomial_le_degreeOf` (used in (viii), (x)).
* `Mathlib/Data/Finsupp/Single.lean`,
  `Finsupp.single_eq_same/single_eq_of_ne` (used in (ix), (x)).
* `Mathlib/Algebra/BigOperators/Group/Finset/Basic.lean`,
  `Finset.sum_eq_single`, `Finset.sum_le_sum` (used in (ix)).
* `Mathlib/Algebra/Order/BigOperators/Group/Finset.lean`,
  `Finset.sum_le_sum_of_subset_of_nonneg` (used in (viii)).
* `Mathlib/Data/Finset/Lattice/Fold.lean`, `Finset.sup_le`, `Finset.le_sup`
  (used in (viii)).
* `Mathlib/RingTheory/Ideal/Span.lean`, `Ideal.mem_span_singleton`;
  `Mathlib/RingTheory/Ideal/Basic.lean`, `Ideal.span_singleton_eq_bot`;
  `Ideal.Quotient.mk_surjective`, `Ideal.Quotient.eq_zero_iff_mem`,
  `isSMulRegular_iff_right_eq_zero_of_smul`, `smul_eq_mul`,
  `Equiv.apply_symm_apply`, `Equiv.injective` (used in (x), (xi)).
* `Mathlib/RingTheory/IntegralClosure/GoingDown.lean`, the integral +
  integrally-closed-base `Algebra.HasGoingDown` instance (used in
  `goingDown_of_normalization`); `Mathlib/RingTheory/Polynomial/
  UniqueFactorization.lean`, `MvPolynomial.uniqueFactorizationMonoid`;
  `Mathlib/RingTheory/UniqueFactorizationDomain/GCDMonoid.lean` and
  `Mathlib/Algebra/GCDMonoid/IntegrallyClosed.lean`, the UFD-to-normal chain
  (used in `goingDown_of_normalization`).
* `Mathlib/Algebra/MvPolynomial/Basic.lean`, `MvPolynomial.coeff_mul`,
  `MvPolynomial.coeff_X_pow`, `MvPolynomial.coeff_X_same`,
  `MvPolynomial.coeff_one`, `MvPolynomial.coeff_C_mul`,
  `MvPolynomial.ne_zero_iff`; `Mathlib/Algebra/MvPolynomial/CommRing.lean`,
  `MvPolynomial.coeff_sub`, `MvPolynomial.degreeOf_sub_le`;
  `Mathlib/Algebra/MvPolynomial/Degrees.lean`, `MvPolynomial.degreeOf_add_le`,
  `MvPolynomial.degreeOf_one`, `MvPolynomial.degreeOf_X_self`,
  `MvPolynomial.degreeOf_X_self_pow`; `Mathlib/Algebra/Algebra/Equiv.lean`,
  `AlgEquiv.apply_symm_apply/symm_apply_apply`;
  `Mathlib/RingTheory/Ideal/Maps.lean`, `Ideal.mem_comap`;
  `Finset.mem_antidiagonal`, `Finset.sum_eq_zero` (core/Batteries finset API)
  (used in (xii)).
* `Mathlib/RingTheory/IntegralClosure/Algebra/Basic.lean`,
  `RingHom.IsIntegralElem.add/mul` (used in (xiv)).
* `Mathlib/Algebra/Polynomial/Monic.lean`, `Polynomial.monic_X_sub_C`,
  `Polynomial.monic_X_pow_add`; `Mathlib/Algebra/Polynomial/Eval/Defs.lean`,
  `Polynomial.eval₂_sub/X/C/pow/add/mul`; `Mathlib/Algebra/Polynomial/
  AlgebraMap.lean`, `Polynomial.aeval_def/X/C`; `Mathlib/Algebra/Polynomial/
  Degree/Defs.lean`, `Polynomial.degree_C_mul_X_pow_le`, `degree_sum_le`
  (used in (xiv)).
* `Mathlib/Algebra/MvPolynomial/Basic.lean`, `MvPolynomial.induction_on`,
  `MvPolynomial.monomial_single_add`, `MvPolynomial.X_pow_eq_monomial`;
  `Mathlib/Algebra/MvPolynomial/Rename.lean`, `MvPolynomial.rename_monomial`,
  `MvPolynomial.rename_X/C`; `Mathlib/Algebra/Algebra/Basic.lean`,
  `RingHom.algebraMap_toAlgebra` (an `rfl`-lemma bridging `algebraMap` and
  `toRingHom` for the `toAlgebra` instance);
  `Mathlib/RingTheory/Ideal/Quotient/Operations.lean`,
  `Ideal.Quotient.mkₐ_toRingHom/mkₐ_eq_mk`;
  `Mathlib/Data/Finsupp/Basic.lean`, `Finsupp.mapDomain/embDomain/
  comapDomain` roundtrip (`embDomain_comapDomain`, `embDomain_eq_mapDomain`),
  `Finsupp.tsub_apply` (truncated subtraction on `ℕ`-finsupps), `Nat.sub_self`;
  `Mathlib/Algebra/BigOperators/Group/Finset/Basic.lean`,
  `Finset.sum_fiberwise_of_maps_to`, `Finset.add_sum_erase`, `Finset.sum_mul`
  (used in (xiv)).
* `Mathlib/Data/Nat/Digits/Defs.lean`, `Nat.ofDigits`;
  `Mathlib/Data/Nat/Digits/Lemmas.lean`, `Nat.injOn_ofDigits`
  (base-`D` uniqueness, used in (xv)).
* `Mathlib/Algebra/BigOperators/Ring/Finset.lean`, `Finset.prod_sum`
  (product-of-sums over choice functions, used in (xvii)).
* `Mathlib/Algebra/MvPolynomial/NoZeroDivisors.lean`,
  `MvPolynomial.degreeOf_prod_eq` (used in (xvi)).
* `Mathlib/Algebra/MvPolynomial/Degrees.lean`,
  `MvPolynomial.degreeOf_add_eq_of_degreeOf_lt` (used in (xvi)).
* `Mathlib/Data/Nat/Choose/Sum.lean`, `add_pow` (used in (xvii)).
* `Mathlib/Data/Finset/Max.lean`, `Finset.exists_max_image` (used in (xvi)).
* `Mathlib/Order/RelSeries.lean`, `LTSeries.map` (+ `last_map`),
  `RelSeries.snoc` (+ `last_snoc`) (used in (xviii)).
* `Mathlib/RingTheory/Spectrum/Prime/Defs.lean`, `PrimeSpectrum.ext`,
  `PrimeSpectrum.asIdeal_lt_asIdeal`, `PrimeSpectrum.isPrime` (instance)
  (used in (xviii)).
* `Mathlib/RingTheory/Ideal/Maps.lean`, `Ideal.IsPrime.comap` (instance),
  `RingHom.strictMono_comap_of_surjective` (used in (xviii)).
-/

namespace EvolutionAlgebras
namespace Appendix_FixedPoint.BezoutChain
/-! ## (i) The `D ^ (i + 1)` shear-exponent recipe. -/

/-- Collision-free `D ^ (i + 1)` shear-exponent recipe for the triangular
change: exponent `D ^ (i.val + 1)` off the distinguished index `j` (so no
off-`j` weight collides with the fixed variable's own weight `1` or with each
other, by strict monotonicity of `D ^ ·` for `1 < D`), `0` at `j` (the fixed
last variable, whose exponent is unused). This replaces the dead `D ^ i`
recipe, whose off-`j` exponent `D ^ 0 = 1` at index `0` collided with the fixed
variable's weight (see the former `shearExp_weight_tie`, now deleted). -/
def shearExp {m : ℕ} (j : Fin m) (D : ℕ) : Fin m → ℕ :=
  fun i => if i = j then 0 else D ^ (i.val + 1)

/-- The recipe fixes exponent `0` at the distinguished index. -/
theorem shearExp_at_j {m : ℕ} (j : Fin m) (D : ℕ) : shearExp j D j = 0 := by
  simp [shearExp]

/-- The recipe discharges the `adm` field shape: with `D ≠ 0` every off-`j`
exponent is nonzero. -/
theorem shearExp_adm {m : ℕ} (j : Fin m) (D : ℕ) (hD : D ≠ 0) (i : Fin m)
    (hij : i ≠ j) : shearExp j D i ≠ 0 := by
  simp only [shearExp, hij, ite_false]
  exact pow_ne_zero _ hD

/-- Separation: `D ^ ·` is strictly monotone for `1 < D`, so distinct variable
indices get distinct shear exponents (the degree argument the monic-fiber
construction rests on). -/
theorem dpow_lt_of_lt {D a b : ℕ} (hD : 1 < D) (h : a < b) : D ^ a < D ^ b :=
  Nat.pow_lt_pow_right hD h

/-! ## (ii) The `fiber` predicate and the `hnorm` projections. -/

/-- The `fiber`-field predicate of `TriangularNormDatum`, isolated verbatim: a
nonzero element of `P` involving only the distinguished variable `j`, with
coefficient `1` somewhere nontrivial (the "made monic" essence). -/
def fiberPred (m : ℕ) (K : Type*) [Field K] (P : Ideal (MvPolynomial (Fin m) K))
    (j : Fin m) : Prop :=
  P ≠ ⊥ → ∃ f : MvPolynomial (Fin m) K, f ∈ P ∧ f ≠ 0 ∧
    (∀ i : Fin m, i ≠ j → f.degreeOf i = 0) ∧
    ∃ e : ℕ, e ≠ 0 ∧ f.coeff (Finsupp.single j e) = 1

/-- The weakened `fiber`-field predicate of `TriangularNormDatum`, isolated
verbatim: a nonzero element of the shear contraction
`shearContraction j d P`, monic in the distinguished variable `j` (degree
pinned with coefficient `1`) but not necessarily univariate, plus integrality
of the contracted quotient over the delete-`j` base — exactly the input
going-down consumes. -/
def fiberPredWeak (m : ℕ) (K : Type*) [Field K]
    (P : Ideal (MvPolynomial (Fin m) K)) (j : Fin m) (d : Fin m → ℕ) : Prop :=
  P ≠ ⊥ → (∃ f : MvPolynomial (Fin m) K, f ∈ shearContraction j d P ∧ f ≠ 0 ∧
    ∃ e : ℕ, e ≠ 0 ∧ f.degreeOf j = e ∧
      f.coeff (Finsupp.single j e) = 1) ∧
    (delVarQuot j (shearContraction j d P)).IsIntegral

/-- The triangular data project to exactly the `adm` field shape. -/
theorem adm_of_datum (m s : ℕ) (K : Type*) [Field K] [Infinite K]
    (P : Ideal (MvPolynomial (Fin m) K)) [P.IsPrime]
    (hnorm : TriangularNormDatum m s K P) :
    ∀ i : Fin m, i ≠ hnorm.shear_idx → hnorm.shear_exp i ≠ 0 :=
  hnorm.adm

/-- The datum carries exactly the weakened `fiber` field shape. -/
theorem fiber_of_datum (m s : ℕ) (K : Type*) [Field K] [Infinite K]
    (P : Ideal (MvPolynomial (Fin m) K)) [P.IsPrime]
    (hnorm : TriangularNormDatum m s K P) :
    fiberPredWeak m K P hnorm.shear_idx hnorm.shear_exp :=
  hnorm.fiber

/-- The datum carries exactly the `exhibit` field shape. -/
theorem exhibit_of_datum (m s : ℕ) (K : Type*) [Field K] [Infinite K]
    (P : Ideal (MvPolynomial (Fin m) K)) [P.IsPrime]
    (hnorm : TriangularNormDatum m s K P) :
    ∃ l : LTSeries (PrimeSpectrum (MvPolynomial (Fin m) K)),
      l.length = m - s ∧ l.last = ⟨P, ‹P.IsPrime›⟩ :=
  hnorm.exhibit

/-! ## (iii) Flat going-down set-up: the below-`P` direction. -/

/-- Flat algebras satisfy going-down (the `Algebra.HasGoingDown.of_flat`
instance, exposed for the down-route). -/
theorem goingDown_of_flat (R S : Type*) [CommRing R] [CommRing S] [Algebra R S]
    [Module.Flat R S] : Algebra.HasGoingDown R S :=
  inferInstance

/-- One rung of the going-down induction below `P`: given a prime `Q` of `S`
lying over `q` and `p < q` in `R`, some prime strictly below `Q` lies over
`p`. Iterating this down a base chain of length `m - s` builds the exhibit;
each rung stays below the previous prime, never above `P`. -/
theorem down_step_of_goingDown {R S : Type*} [CommRing R] [CommRing S]
    [Algebra R S] [Algebra.HasGoingDown R S]
    {p q : Ideal R} [p.IsPrime] [q.IsPrime] (Q : Ideal S) [Q.IsPrime]
    [Q.LiesOver q] (h : p < q) :
    ∃ Q' < Q, Q'.IsPrime ∧ Q'.LiesOver p :=
  Ideal.exists_ideal_lt_liesOver_of_lt Q h

/-- Full down-lift: a base prime chain in `R` lifts to a same-length prime
chain in `S` *ending* at the target prime `Q`. Applied with `Q := P`, this is
the below-`P` exhibit direction — dual to the going-up lift, whose pulled-back
chains sit above `P` (coheight). -/
theorem down_lift_below {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.HasGoingDown R S]
    (l : LTSeries (PrimeSpectrum R)) (Q : Ideal S) [Q.IsPrime]
    [Q.LiesOver l.last.asIdeal] :
    ∃ L : LTSeries (PrimeSpectrum S),
      L.length = l.length ∧ L.last = ⟨Q, inferInstance⟩ ∧
        List.map (PrimeSpectrum.comap (algebraMap R S)) L.toList = l.toList :=
  Ideal.exists_ltSeries_of_hasGoingDown l Q

/-- Going-down through the normalization: the injective integral normalization
map makes `R ⧸ P` integral over the polynomial base
`MvPolynomial (Fin s) K` — a UFD, hence integrally closed — so the
integral-plus-normal-base going-down instance fires. This closes
"integrality ⇒ going-down" for the normalization pair (the fiber pair needs
the strong-monic expansion first; see `## Obstruction`). -/
theorem goingDown_of_normalization (m s : ℕ) (K : Type*) [Field K]
    (P : Ideal (MvPolynomial (Fin m) K)) [P.IsPrime]
    (g : MvPolynomial (Fin s) K →ₐ[K] MvPolynomial (Fin m) K ⧸ P)
    (hinj : Function.Injective g) (hint : g.IsIntegral)
    [Algebra (MvPolynomial (Fin s) K) (MvPolynomial (Fin m) K ⧸ P)]
    (hmap : algebraMap (MvPolynomial (Fin s) K) (MvPolynomial (Fin m) K ⧸ P) =
      g.toRingHom) :
    Algebra.HasGoingDown (MvPolynomial (Fin s) K)
      (MvPolynomial (Fin m) K ⧸ P) := by
  have hInt : Algebra.IsIntegral (MvPolynomial (Fin s) K)
      (MvPolynomial (Fin m) K ⧸ P) := by
    rw [← algebraMap_isIntegral_iff, hmap]
    exact hint
  have hfaith : FaithfulSMul (MvPolynomial (Fin s) K)
      (MvPolynomial (Fin m) K ⧸ P) := by
    rw [faithfulSMul_iff_algebraMap_injective, hmap]
    exact hinj
  exact inferInstance

/-! ## (iv) Assembly: the recipe feeds `hnorm` exactly. -/

/-- The `D ^ (i + 1)` recipe output feeds the `hnorm` fields exactly:
`shear_exp` is the recipe, `adm` is the recipe lemma, and the remaining
components are passed through with unchanged names/shapes. -/
def datum_of_dpow_recipe (m s : ℕ) (K : Type*) [Field K] [Infinite K]
    (P : Ideal (MvPolynomial (Fin m) K)) [P.IsPrime]
    (s_le : s ≤ m)
    (normap : MvPolynomial (Fin s) K →ₐ[K] MvPolynomial (Fin m) K ⧸ P)
    (normap_inj : Function.Injective normap)
    (normap_int : normap.IsIntegral)
    (bad : Finset (Fin m → K))
    (dir : (Fin m → K) →ₗ[K] K)
    (dir_ne : ∀ v ∈ bad, dir v ≠ 0)
    (j : Fin m) (D : ℕ) (hD : D ≠ 0)
    (fiber : fiberPredWeak m K P j (shearExp j D))
    (exhibit : ∃ l : LTSeries (PrimeSpectrum (MvPolynomial (Fin m) K)),
      l.length = m - s ∧ l.last = ⟨P, ‹P.IsPrime›⟩) :
    TriangularNormDatum m s K P :=
  { s_le := s_le
    normap := normap
    normap_inj := normap_inj
    normap_int := normap_int
    bad := bad
    dir := dir
    dir_ne := dir_ne
    shear_idx := j
    shear_exp := shearExp j D
    adm := shearExp_adm j D hD
    fiber := fiber
    exhibit := exhibit }

/-- The assembled height bound from recipe-fed datum, in the exact shape
consumed by `hheight_of_production`. -/
theorem height_of_dpow_datum (m s : ℕ) (K : Type*) [Field K] [Infinite K]
    (P : Ideal (MvPolynomial (Fin m) K)) [P.IsPrime]
    (hnorm : TriangularNormDatum m s K P) :
    (((m - s : ℕ)) : WithBot ℕ∞) ≤ (P.height : WithBot ℕ∞) :=
  triangular_monic_chain m s K P hnorm

/-! ## (v) The `degreeOf`-under-`triShear` computation (obstruction item (i)).

For `i ≠ j` with `d i ≠ 0`, `triShear_coeff_shift` says the sheared generator
`σ (Xᵢ)` carries coefficient `1` at `Finsupp.single j (d i)`; a nonzero
coefficient lies in the support (`MvPolynomial.mem_support_iff`), and support
members bound `degreeOf` from below (`MvPolynomial.monomial_le_degreeOf`).
Hence `d i ≤ degreeOf j (σ Xᵢ)`: the shear pushes `Xᵢ` to `j`-degree at least
`dᵢ`. At the `D ^ (i + 1)` recipe the lower bounds are strictly separated
(`dpow_lt_of_lt`), the separation property the monic-fiber degree argument
rests on. -/

/-- `degreeOf`-under-`triShear` for generators: the sheared generator has
`j`-degree at least the shear exponent (via `triShear_coeff_shift`). -/
theorem shear_image_degreeOf_ge {m : ℕ} {K : Type*} [Field K] (j : Fin m)
    (d : Fin m → ℕ) (i : Fin m) (hij : i ≠ j) (hd : d i ≠ 0) :
    d i ≤ (triShear (K := K) j d (MvPolynomial.X i)).degreeOf j := by
  have h1 := triShear_coeff_shift (K := K) j d i hij hd
  have hmem : Finsupp.single j (d i) ∈
      (triShear (K := K) j d (MvPolynomial.X i)).support := by
    rw [MvPolynomial.mem_support_iff, h1]
    exact one_ne_zero
  have hle := MvPolynomial.monomial_le_degreeOf j hmem
  rwa [Finsupp.single_eq_same] at hle

/-- At the recipe, the lower bound reads `D ^ (i.val + 1)` (via
`shearExp_adm`). -/
theorem shearExp_image_degreeOf_ge {m : ℕ} {K : Type*} [Field K] (j : Fin m)
    (D : ℕ) (hD : D ≠ 0) (i : Fin m) (hij : i ≠ j) :
    D ^ (i.val + 1) ≤
      (triShear (K := K) j (shearExp j D) (MvPolynomial.X i)).degreeOf j := by
  have hd : shearExp j D i ≠ 0 := shearExp_adm j D hD i hij
  have hexp : shearExp j D i = D ^ (i.val + 1) := by
    simp only [shearExp, hij, ite_false]
  have hle := shear_image_degreeOf_ge (K := K) j (shearExp j D) i hij hd
  rwa [hexp] at hle

/-- Separation of the recipe lower bounds: for `1 < D` and off-`j` indices
with `i₁.val < i₂.val`, the `D ^ (· + 1)` values — hence the `degreeOf` lower
bounds from `shearExp_image_degreeOf_ge` — are strictly ordered. -/
theorem shearExp_degreeOf_sep {m : ℕ} {K : Type*} [Field K] (j : Fin m) (D : ℕ)
    (hD : 1 < D) {i₁ i₂ : Fin m} (h1 : i₁ ≠ j) (h2 : i₂ ≠ j)
    (hlt : i₁.val < i₂.val) :
    D ^ (i₁.val + 1) < D ^ (i₂.val + 1) ∧
      D ^ (i₁.val + 1) ≤
        (triShear (K := K) j (shearExp j D) (MvPolynomial.X i₁)).degreeOf j ∧
      D ^ (i₂.val + 1) ≤
        (triShear (K := K) j (shearExp j D) (MvPolynomial.X i₂)).degreeOf j := by
  have hD0 : D ≠ 0 := by omega
  exact ⟨dpow_lt_of_lt (a := i₁.val + 1) (b := i₂.val + 1) hD (by omega),
    shearExp_image_degreeOf_ge j D hD0 i₁ h1,
    shearExp_image_degreeOf_ge j D hD0 i₂ h2⟩

/-! ## (vi) Made-monic step: `fiber` from a univariate element (obstruction
item (ii), first half).

`fiberPred` asks for coefficient `1`; a univariate-off-`j` nonzero `g ∈ P`
with *some* nonzero coefficient `c` at level `e` scales by `C c⁻¹` — staying in
`P`, staying nonzero, keeping off-`j` degrees at `0` (by
`MvPolynomial.degreeOf_C_mul_le`), and turning the coefficient into `1` (by
`inv_mul_cancel₀`). What remains after this step is producing such a `g` from
the shear data (see `## Obstruction`). -/

/-- Made-monic: a nonzero element of `P` involving only `j`, with some nonzero
coefficient at a positive level, normalizes to the `fiber` witness. -/
theorem fiberPred_of_mem_univariate {m : ℕ} (K : Type*) [Field K]
    (P : Ideal (MvPolynomial (Fin m) K)) (j : Fin m)
    (g : MvPolynomial (Fin m) K) (hg : g ∈ P) (hne : g ≠ 0)
    (huni : ∀ i : Fin m, i ≠ j → g.degreeOf i = 0)
    (e : ℕ) (he : e ≠ 0) (c : K) (hc : g.coeff (Finsupp.single j e) = c)
    (hc0 : c ≠ 0) :
    fiberPred m K P j := by
  intro _
  refine ⟨MvPolynomial.C c⁻¹ * g, Ideal.mul_mem_left P _ hg, ?_, ?_, e, he, ?_⟩
  · exact mul_ne_zero (MvPolynomial.C_ne_zero.mpr (inv_ne_zero hc0)) hne
  · intro i hij
    have hle := MvPolynomial.degreeOf_C_mul_le g i c⁻¹
    rw [huni i hij] at hle
    exact Nat.le_zero.mp hle
  · rw [MvPolynomial.coeff_C_mul, hc, inv_mul_cancel₀ hc0]

/-! ## (vii) HilbertFunctionCount skeleton for `exhibit` (obstruction item (ii), second
half).

The base case (`s = m`: the singleton chain at `P`) and the one-rung downward
extension (a chain ending at `L.last` extends below any prime strictly under
its head, preserving the last prime and gaining one rung — via
`RelSeries.append` on the singleton) are pure order theory. With
`down_step_of_goingDown` supplying the prime below, the extension is the
induction step's order-theoretic content; the model-specific assembly (base
chain from the fiber integrality, then `down_lift_below`) is the stated
remainder. -/

/-- Base case of the induction on `m`: when `s = m` the length-`(m - s)`
exhibit is the singleton chain at `P`. -/
theorem exhibit_of_eq {m : ℕ} (K : Type*) [Field K] [Infinite K]
    (P : Ideal (MvPolynomial (Fin m) K)) [P.IsPrime]
    (s : ℕ) (h : s = m) :
    ∃ l : LTSeries (PrimeSpectrum (MvPolynomial (Fin m) K)),
      l.length = m - s ∧ l.last = ⟨P, ‹P.IsPrime›⟩ := by
  refine ⟨RelSeries.singleton _ ⟨P, ‹P.IsPrime›⟩, ?_, ?_⟩
  · have h0 : m - s = 0 := by omega
    rw [h0]
    rfl
  · simp

/-- One-rung downward extension: a chain extends below any prime strictly under
its head, preserving the last prime and gaining one rung. -/
theorem exhibit_extend_down {R : Type*} [CommRing R]
    (L : LTSeries (PrimeSpectrum R)) (Q' : PrimeSpectrum R) (h : Q' < L.head) :
    ∃ L' : LTSeries (PrimeSpectrum R),
      L'.length = L.length + 1 ∧ L'.last = L.last ∧ L'.head = Q' := by
  refine ⟨(RelSeries.singleton _ Q').append L ?_, ?_, ?_, ?_⟩
  · simpa using h
  · simp
  · simp
  · simp

/-! ## (viii) `degreeOf` under the shear for general polynomials (obstruction item (i)).

There is no `degreeOf`-under-`aeval` API in Mathlib (verified by grep over
`.lake/packages/mathlib`: no `degreeOf_aeval` lemma), so the general bound is
proved here from `MvPolynomial.as_sum` + `MvPolynomial.aeval_monomial` + the
`≤` lemmas of `Degrees.lean`. The shear weight `shearWeight j d e` is the
per-monomial `j`-degree cap: the generator equalities strengthen
`shear_image_degreeOf_ge` (kept byte-identical) from `≥` to `=` with no
`d i ≠ 0` hypothesis, and the monomial/general bounds constrain `degreeOf j`
of arbitrary sheared polynomials by the support-supremum of the weight. -/

/-- Shear weight of an exponent vector: `∑ i, e i * w i` with `w j = 1` (the
fixed last variable contributes its own exponent) and `w i = d i` off `j`
(the shear pushes `Xᵢ` to `j`-degree `d i`). The per-monomial cap for the
`degreeOf`-under-shear computation. -/
def shearWeight {m : ℕ} (j : Fin m) (d : Fin m → ℕ) (e : Fin m →₀ ℕ) : ℕ :=
  ∑ i, e i * (if i = j then 1 else d i)

/-- Generator equality for the forward shear: the sheared generator has
`j`-degree exactly the shear exponent (no `d i ≠ 0` hypothesis needed; the
`d i = 0` case is `Xᵢ + 1`). -/
theorem shearFwd_generator_degreeOf_eq {m : ℕ} {K : Type*} [Field K] (j : Fin m)
    (d : Fin m → ℕ) (i : Fin m) (hij : i ≠ j) :
    (MvPolynomial.X i + MvPolynomial.X j ^ d i :
      MvPolynomial (Fin m) K).degreeOf j = d i := by
  have hXi : (MvPolynomial.X i : MvPolynomial (Fin m) K).degreeOf j = 0 := by
    simp only [MvPolynomial.degreeOf_X, Ne.symm hij, ite_false]
  have hXj : (MvPolynomial.X j ^ d i :
      MvPolynomial (Fin m) K).degreeOf j = d i :=
    MvPolynomial.degreeOf_X_self_pow j (d i)
  have hle : (MvPolynomial.X i + MvPolynomial.X j ^ d i :
      MvPolynomial (Fin m) K).degreeOf j ≤ d i := by
    have h := MvPolynomial.degreeOf_add_le j
      (MvPolynomial.X i : MvPolynomial (Fin m) K)
      (MvPolynomial.X j ^ d i)
    rw [hXi, hXj] at h
    have hmax : max 0 (d i) = d i := by omega
    rwa [hmax] at h
  refine le_antisymm hle ?_
  by_cases hd : d i = 0
  · rw [hd]
    exact Nat.zero_le _
  · have hge := shear_image_degreeOf_ge (K := K) j d i hij hd
    simpa only [triShear_apply, hij, ite_false] using hge

/-- Generator equality for the shear automorphism (exact form of
`shear_image_degreeOf_ge`). -/
theorem shear_generator_degreeOf_eq {m : ℕ} {K : Type*} [Field K] (j : Fin m)
    (d : Fin m → ℕ) (i : Fin m) (hij : i ≠ j) :
    (triShear (K := K) j d (MvPolynomial.X i)).degreeOf j = d i := by
  simpa only [triShear_apply, hij, ite_false] using
    shearFwd_generator_degreeOf_eq (K := K) j d i hij

/-- Per-monomial cap: the sheared monomial has `j`-degree at most the shear
weight of its exponent vector (via `aeval_monomial` and the `≤` lemmas). -/
theorem shear_monomial_degreeOf_le {m : ℕ} {K : Type*} [Field K] (j : Fin m)
    (d : Fin m → ℕ) (e : Fin m →₀ ℕ) (c : K) :
    (shearFwd (K := K) j d (MvPolynomial.monomial e c)).degreeOf j ≤
      shearWeight j d e := by
  simp only [shearFwd, MvPolynomial.aeval_monomial]
  refine le_trans (MvPolynomial.degreeOf_mul_le j _ _) ?_
  rw [MvPolynomial.algebraMap_eq, MvPolynomial.degreeOf_C, zero_add]
  simp only [shearWeight]
  refine le_trans (MvPolynomial.degreeOf_prod_le j e.support _) ?_
  refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
    fun i _ _ => Nat.zero_le _) ?_
  refine Finset.sum_le_sum fun i _ => ?_
  refine le_trans (MvPolynomial.degreeOf_pow_le j _ _) ?_
  by_cases hij : i = j
  · subst hij
    rw [ite_eq_left rfl, ite_eq_left rfl, MvPolynomial.degreeOf_X_self, mul_one]
  · rw [ite_eq_right hij, ite_eq_right hij,
      shearFwd_generator_degreeOf_eq (K := K) j d i hij]

/-- General upper bound: `degreeOf j` of the sheared polynomial is at most the
support-supremum of the shear weight (via `as_sum` + `degreeOf_sum_le`). -/
theorem shear_image_degreeOf_le {m : ℕ} {K : Type*} [Field K] (j : Fin m)
    (d : Fin m → ℕ) (f : MvPolynomial (Fin m) K) :
    (shearFwd (K := K) j d f).degreeOf j ≤
      f.support.sup (shearWeight j d) := by
  have hf : f = ∑ e ∈ f.support, MvPolynomial.monomial e (f.coeff e) :=
    MvPolynomial.as_sum f
  conv_lhs => rw [hf, map_sum]
  refine le_trans (MvPolynomial.degreeOf_sum_le j _ _) ?_
  refine Finset.sup_le fun e he => ?_
  refine le_trans (shear_monomial_degreeOf_le (K := K) j d e _) ?_
  exact Finset.le_sup he

/-- Transfer of the general bound to the shear automorphism. -/
theorem shear_triShear_degreeOf_le {m : ℕ} {K : Type*} [Field K] (j : Fin m)
    (d : Fin m → ℕ) (f : MvPolynomial (Fin m) K) :
    (triShear (K := K) j d f).degreeOf j ≤
      f.support.sup (shearWeight j d) :=
  shear_image_degreeOf_le (K := K) j d f

/-! ## (ix) Weight separation for the `D ^ (i + 1)` recipe.

The dead `D ^ i` recipe's weights collided (off-`j` index `0` carried
`D ^ 0 = 1`, the fixed variable's own weight; the former `shearExp_weight_tie`
is deleted). For the `D ^ (i + 1)` recipe with `1 < D`, the weights separate
by construction: the fixed variable's own weight is `1`
(`shearWeight_single_at`), every off-`j` generator weight is the shear exponent
(`shearWeight_single_off`), no off-`j` weight equals `1`
(`shearExp_weight_ne_one`), and distinct off-`j` indices get distinct weights
(`shearExp_weight_sep`). -/

/-- The shear weight of an off-`j` generator exponent vector is the shear
exponent. -/
theorem shearWeight_single_off {m : ℕ} (j : Fin m) (d : Fin m → ℕ)
    (i : Fin m) (hij : i ≠ j) :
    shearWeight j d (Finsupp.single i (1 : ℕ)) = d i := by
  have h₀ : ∀ b ∈ (Finset.univ : Finset (Fin m)), b ≠ i →
      (Finsupp.single i (1 : ℕ) : Fin m →₀ ℕ) b *
        (if b = j then 1 else d b) = 0 := by
    intro b _ hb
    rw [Finsupp.single_eq_of_ne hb, zero_mul]
  have h₁ : i ∉ (Finset.univ : Finset (Fin m)) →
      (Finsupp.single i (1 : ℕ) : Fin m →₀ ℕ) i *
        (if i = j then 1 else d i) = 0 := by
    intro hcon
    exact absurd (Finset.mem_univ i) hcon
  simp only [shearWeight]
  rw [Finset.sum_eq_single i h₀ h₁, Finsupp.single_eq_same, ite_eq_right hij,
    one_mul]

/-- The shear weight of the fixed variable's own generator exponent vector is
`1`. -/
theorem shearWeight_single_at {m : ℕ} (j : Fin m) (d : Fin m → ℕ) :
    shearWeight j d (Finsupp.single j (1 : ℕ)) = 1 := by
  have h₀ : ∀ b ∈ (Finset.univ : Finset (Fin m)), b ≠ j →
      (Finsupp.single j (1 : ℕ) : Fin m →₀ ℕ) b *
        (if b = j then 1 else d b) = 0 := by
    intro b _ hb
    rw [Finsupp.single_eq_of_ne hb, zero_mul]
  have h₁ : j ∉ (Finset.univ : Finset (Fin m)) →
      (Finsupp.single j (1 : ℕ) : Fin m →₀ ℕ) j *
        (if j = j then 1 else d j) = 0 := by
    intro hcon
    exact absurd (Finset.mem_univ j) hcon
  simp only [shearWeight]
  rw [Finset.sum_eq_single j h₀ h₁, Finsupp.single_eq_same, ite_eq_left rfl,
    mul_one]

/-- No off-`j` recipe weight collides with `1`: for `1 < D` the off-`j`
generator weight `D ^ (i.val + 1)` strictly exceeds `1`. -/
theorem shearExp_weight_ne_one {m : ℕ} (j : Fin m) (D : ℕ) (hD : 1 < D)
    (i : Fin m) (hij : i ≠ j) :
    shearWeight j (shearExp j D) (Finsupp.single i (1 : ℕ)) ≠ 1 := by
  rw [shearWeight_single_off j _ _ hij]
  have hexp : shearExp j D i = D ^ (i.val + 1) := by
    simp only [shearExp, hij, ite_false]
  rw [hexp]
  have hlt : (1 : ℕ) < D ^ (i.val + 1) := by
    have h := dpow_lt_of_lt (D := D) (a := 0) (b := i.val + 1) hD
      (Nat.succ_pos _)
    rwa [pow_zero] at h
  omega

/-- Distinct off-`j` indices get distinct recipe weights for `1 < D` (by
strict monotonicity of `D ^ ·`). Together with `shearExp_weight_ne_one`,
the recipe weights are collision-free by construction. -/
theorem shearExp_weight_sep {m : ℕ} (j : Fin m) (D : ℕ) (hD : 1 < D)
    {i₁ i₂ : Fin m} (h1 : i₁ ≠ j) (h2 : i₂ ≠ j) (hne : i₁.val ≠ i₂.val) :
    shearWeight j (shearExp j D) (Finsupp.single i₁ (1 : ℕ)) ≠
      shearWeight j (shearExp j D) (Finsupp.single i₂ (1 : ℕ)) := by
  rw [shearWeight_single_off j _ _ h1, shearWeight_single_off j _ _ h2]
  have hexp1 : shearExp j D i₁ = D ^ (i₁.val + 1) := by
    simp only [shearExp, h1, ite_false]
  have hexp2 : shearExp j D i₂ = D ^ (i₂.val + 1) := by
    simp only [shearExp, h2, ite_false]
  rw [hexp1, hexp2]
  rcases lt_trichotomy i₁.val i₂.val with h | h | h
  · exact ne_of_lt (dpow_lt_of_lt (a := i₁.val + 1) (b := i₂.val + 1) hD (by omega))
  · exact absurd h hne
  · exact ne_of_gt (dpow_lt_of_lt (a := i₂.val + 1) (b := i₁.val + 1) hD (by omega))

/- Note: no tie witness is stated. For `2 ≤ m` the dead `D ^ i` recipe
weights tied (`single 0 1` vs `single j 1` when `j ≠ 0`, both of weight
`1`; `single 1 1` vs `single j D` when `j = 0`, both of weight `D`),
while the `D ^ (i + 1)` recipe kills the tie by
construction (`shearExp_weight_ne_one`, `shearExp_weight_sep`). -/

/-! ## (x) Fiber refutation: no univariate element for `span {X₀ - X₁}`.

The `fiber` field asks for a nonzero univariate-off-`j` element of `P` with a
`1` coefficient. For `P = span {X₀ - X₁} ⊂ K[X₀, X₁]` no such element exists
for either `j`: any `g ∈ P` is `(X₀ - X₁) * h`, and `h ≠ 0` forces both
`degreeOf 0` and `degreeOf 1` of `g` positive (via `degreeOf_mul_eq`), killing
univariateness off either index. Hence `fiber` is underivable from shear data
for arbitrary prime `P` — the datum is uninhabited there. -/

/-- Coefficient of `X₀ - X₁` at `single k 1`: `1` at `k = 0`, `-1` at
`k = 1`. -/
theorem spanSub_coeff_single {K : Type*} [Field K] (k : Fin 2) :
    (MvPolynomial.X 0 - MvPolynomial.X 1 :
      MvPolynomial (Fin 2) K).coeff (Finsupp.single k 1) =
      (if k = 0 then (1 : K) else -1) := by
  have hk01 : k = 0 ∨ k = 1 := by
    have h3 : k.val = 0 ∨ k.val = 1 := by
      have h2 := k.isLt
      omega
    rcases h3 with h | h
    · exact Or.inl (Fin.ext h)
    · exact Or.inr (Fin.ext h)
  rw [MvPolynomial.coeff_sub, MvPolynomial.coeff_X, MvPolynomial.coeff_X]
  rcases hk01 with rfl | rfl
  · have h10 : Finsupp.single (1 : Fin 2) (1 : ℕ) ≠
        Finsupp.single (0 : Fin 2) 1 := by
      intro hcon
      have h2 := congrArg (fun e : Fin 2 →₀ ℕ => e 1) hcon
      rw [Finsupp.single_eq_same,
        Finsupp.single_eq_of_ne (by decide : (1 : Fin 2) ≠ 0)] at h2
      exact one_ne_zero h2
    rw [ite_eq_left rfl, ite_eq_right h10, sub_zero, ite_eq_left rfl]
  · have h01 : Finsupp.single (0 : Fin 2) (1 : ℕ) ≠
        Finsupp.single (1 : Fin 2) 1 := by
      intro hcon
      have h2 := congrArg (fun e : Fin 2 →₀ ℕ => e 0) hcon
      rw [Finsupp.single_eq_same,
        Finsupp.single_eq_of_ne (by decide : (0 : Fin 2) ≠ 1)] at h2
      exact one_ne_zero h2
    rw [ite_eq_right (by decide : (1 : Fin 2) ≠ (0 : Fin 2)), ite_eq_right h01, ite_eq_left rfl,
      zero_sub]

/-- No nonzero element of `span {X₀ - X₁}` is univariate off either index:
every `g ∈ P` with all off-`j` degrees `0` vanishes. -/
theorem no_univariate_in_span_sub {K : Type*} [Field K] (j : Fin 2) :
    ∀ g : MvPolynomial (Fin 2) K,
      g ∈ Ideal.span {(MvPolynomial.X 0 - MvPolynomial.X 1 :
        MvPolynomial (Fin 2) K)} →
      (∀ i : Fin 2, i ≠ j → g.degreeOf i = 0) → g = 0 := by
  intro g hg huni
  rw [Ideal.mem_span_singleton] at hg
  obtain ⟨h, rfl⟩ := hg
  by_cases hh : h = 0
  · subst hh
    exact mul_zero _
  · exfalso
    obtain ⟨k, hkj⟩ : ∃ k : Fin 2, k ≠ j := by
      by_cases hj0 : j = 0
      · exact ⟨1, by rw [hj0]; decide⟩
      · exact ⟨0, fun hcon => hj0 hcon.symm⟩
    have hcoeff : (MvPolynomial.X 0 - MvPolynomial.X 1 :
        MvPolynomial (Fin 2) K).coeff (Finsupp.single k 1) ≠ 0 := by
      rw [spanSub_coeff_single]
      by_cases hk0 : k = 0
      · rw [ite_eq_left hk0]
        exact one_ne_zero
      · rw [ite_eq_right hk0]
        exact neg_ne_zero.mpr one_ne_zero
    have hsub : (MvPolynomial.X 0 - MvPolynomial.X 1 :
        MvPolynomial (Fin 2) K) ≠ 0 := by
      rw [MvPolynomial.ne_zero_iff]
      exact ⟨Finsupp.single k 1, hcoeff⟩
    have hmem : Finsupp.single k 1 ∈
        (MvPolynomial.X 0 - MvPolynomial.X 1 :
          MvPolynomial (Fin 2) K).support :=
      MvPolynomial.mem_support_iff.mpr hcoeff
    have hge : 1 ≤ (MvPolynomial.X 0 - MvPolynomial.X 1 :
        MvPolynomial (Fin 2) K).degreeOf k := by
      have hle := MvPolynomial.monomial_le_degreeOf k hmem
      rwa [Finsupp.single_eq_same] at hle
    have hmul := MvPolynomial.degreeOf_mul_eq (n := k) hsub hh
    have hdeg0 : ((MvPolynomial.X 0 - MvPolynomial.X 1 :
        MvPolynomial (Fin 2) K) * h).degreeOf k = 0 :=
      huni k hkj
    rw [hmul] at hdeg0
    omega

/-- The `fiber` predicate is false for `span {X₀ - X₁}` at every `j`: the
`fiber` field is underivable from shear data for arbitrary prime `P`. -/
theorem fiberPred_false_span_sub {K : Type*} [Field K] (j : Fin 2) :
    ¬ fiberPred 2 K
      (Ideal.span {(MvPolynomial.X 0 - MvPolynomial.X 1 :
        MvPolynomial (Fin 2) K)}) j := by
  intro hcon
  have hne : Ideal.span {(MvPolynomial.X 0 - MvPolynomial.X 1 :
      MvPolynomial (Fin 2) K)} ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]
    intro hzero
    have h1 : (MvPolynomial.X 0 - MvPolynomial.X 1 :
        MvPolynomial (Fin 2) K).coeff (Finsupp.single 0 1) = 1 := by
      rw [spanSub_coeff_single, ite_eq_left rfl]
    have hmem : Finsupp.single (0 : Fin 2) 1 ∈
        (MvPolynomial.X 0 - MvPolynomial.X 1 :
          MvPolynomial (Fin 2) K).support := by
      rw [MvPolynomial.mem_support_iff, h1]
      exact one_ne_zero
    rw [hzero] at hmem
    simp at hmem
  obtain ⟨f, hf, hf0, huni, -, -, -⟩ := hcon hne
  exact hf0 (no_univariate_in_span_sub j f hf huni)

/-! ## (xi) t2b division-step bridge: regularity transport across a ring
equivalence.

`TriangularRegularity.lean`'s (t2b) `triG_isSMulRegular_mod_of_dvd` concludes
`IsSMulRegular` on a `Polynomial S` quotient; carrying it back to
`MvPolynomial` needs the last-variable isomorphism (recorded there as a
follow-up, not claimed). The transport itself — regularity of a quotient
class across any ring equivalence mapping the span-generators — is proved
here with no `Polynomial`/`triG` API, so `TriangularRegularity` stays cited, not
imported. What remains for instantiation is exactly: the isomorphism plus the
t2b input data at the sheared fiber polynomial (see `## Obstruction`). -/

/-- Regularity transport: if a ring equivalence maps the span-generators, the
t2b-style regularity conclusion carries over to the source quotient. -/
theorem isSMulRegular_of_span_ringEquiv {R S : Type*} [CommRing R] [CommRing S]
    (e : R ≃+* S) (G₀ G₁ : R) (H₀ H₁ : S)
    (h₀ : e G₀ = H₀) (h₁ : e G₁ = H₁)
    (hreg : IsSMulRegular (S ⧸ Ideal.span {H₀})
      (Ideal.Quotient.mk (Ideal.span {H₀}) H₁)) :
    IsSMulRegular (R ⧸ Ideal.span {G₀})
      (Ideal.Quotient.mk (Ideal.span {G₀}) G₁) := by
  rw [isSMulRegular_iff_right_eq_zero_of_smul] at hreg ⊢
  intro m hm
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective m
  rw [smul_eq_mul, ← map_mul, Ideal.Quotient.eq_zero_iff_mem,
    Ideal.mem_span_singleton] at hm
  obtain ⟨w, hw⟩ := hm
  have hwx : e (G₁ * x) = H₁ * e x := by rw [map_mul, h₁]
  have hw0 : e (G₀ * w) = H₀ * e w := by rw [map_mul, h₀]
  have hmemS : H₁ * e x ∈ Ideal.span {H₀} := by
    rw [Ideal.mem_span_singleton]
    refine ⟨e w, ?_⟩
    rw [← hwx, ← hw0, hw]
  have hsmul : Ideal.Quotient.mk (Ideal.span {H₀}) H₁ •
      Ideal.Quotient.mk (Ideal.span {H₀}) (e x) = 0 := by
    rw [smul_eq_mul, ← map_mul, Ideal.Quotient.eq_zero_iff_mem]
    exact hmemS
  have hx0 := hreg _ hsmul
  rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton] at hx0
  obtain ⟨v, hv⟩ := hx0
  have hcancel : e (e.symm v) = v := e.toEquiv.apply_symm_apply v
  have key : e (G₀ * e.symm v) = e x := by
    rw [map_mul, h₀, hcancel, hv]
  have hx : G₀ * e.symm v = x := e.toEquiv.injective key
  rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]
  exact ⟨e.symm v, hx.symm⟩

/-! ## (xii) Recipe boundary: collapse at `D = 1`, production at `1 < D`.

The weakened `fiber` drops univariateness but keeps the monic requirement
(degree pinned, coefficient `1`) in the shear contraction. For
`P = span {X₀ - X₁} ⊂ K[X₀, X₁]` at `j = 1` the `D ^ (i + 1)` recipe puts
exponent `D ^ (0 + 1) = D` at index `0`, so the shear sends
`X₀ - X₁ ↦ X₀ + X₁ ^ D - X₁` (`triShear_recipe_span_sub_gen`). At `D = 1`
this collapses onto `span {X₀}` (`contraction_recipe_span_sub_one`), whose
every element carries `X₀`-content in each monomial, killing all pure-`X₁`
coefficients (`no_weakmonic_in_span_x0`, `weakFiberPred_false_new_recipe_one`).
At `1 < D` the carried generator escapes: the off-`j` exponent is
`D ≠ 1`, so `weakFiberMonic_escape_of_ne` fires and the weakened fiber's
monic conjunct is inhabited (`weakFiberMonic_new_recipe_of_lt`). The mirrored
collapse at `j = 0`, `D = 1` (onto `span {X₁}`) is unchanged. No third
counterexample: within the recipe's operating range (`1 < D`) the diagonal
test prime produces rather than refutes. -/

/-- The recipe shear sends `X₀ - X₁ ↦ X₀ + X₁ ^ D - X₁` at `j = 1`: the
off-`j` exponent at index `0` is `D ^ (0 + 1) = D`. -/
theorem triShear_recipe_span_sub_gen {K : Type*} [Field K] (D : ℕ) :
    (triShear (K := K) (1 : Fin 2) (shearExp (1 : Fin 2) D))
      (MvPolynomial.X 0 - MvPolynomial.X 1) =
    MvPolynomial.X 0 + MvPolynomial.X 1 ^ D - MvPolynomial.X 1 := by
  have h01 : (0 : Fin 2) ≠ (1 : Fin 2) := by decide
  have hd0 : shearExp (1 : Fin 2) D (0 : Fin 2) = D := by
    have hv : ((0 : Fin 2).val + 1) = 1 := by decide
    simp only [shearExp, h01, ite_false, hv, pow_one]
  rw [map_sub, triShear_apply, triShear_apply, ite_eq_right h01, ite_eq_left rfl,
    hd0]

/-- At `D = 1` the carried generator collapses to `X₀`. -/
theorem triShear_recipe_span_sub_gen_one {K : Type*} [Field K] :
    (triShear (K := K) (1 : Fin 2) (shearExp (1 : Fin 2) 1))
      (MvPolynomial.X 0 - MvPolynomial.X 1) = MvPolynomial.X 0 := by
  rw [triShear_recipe_span_sub_gen, pow_one]
  abel

/-- The recipe contraction of `span {X₀ - X₁}` at `j = 1`, `D = 1` is
`span {X₀}`. -/
theorem contraction_recipe_span_sub_one {K : Type*} [Field K] :
    shearContraction (1 : Fin 2) (shearExp (1 : Fin 2) 1)
      (Ideal.span {(MvPolynomial.X 0 - MvPolynomial.X 1 :
        MvPolynomial (Fin 2) K)}) =
    Ideal.span {(MvPolynomial.X 0 : MvPolynomial (Fin 2) K)} := by
  have h01 : (0 : Fin 2) ≠ (1 : Fin 2) := by decide
  have hd0 : shearExp (1 : Fin 2) 1 (0 : Fin 2) = 1 := by
    have hv : ((0 : Fin 2).val + 1) = 1 := by decide
    simp only [shearExp, h01, ite_false, hv, pow_one]
  apply le_antisymm
  · intro x hx
    unfold shearContraction at hx
    rw [Ideal.mem_comap] at hx
    have hx2 : (triShear (K := K) (1 : Fin 2) (shearExp (1 : Fin 2) 1)).symm x ∈
        Ideal.span {(MvPolynomial.X 0 - MvPolynomial.X 1 :
          MvPolynomial (Fin 2) K)} := hx
    rw [Ideal.mem_span_singleton] at hx2
    obtain ⟨h, hh⟩ := hx2
    rw [Ideal.mem_span_singleton]
    refine ⟨(triShear (K := K) (1 : Fin 2) (shearExp (1 : Fin 2) 1)) h, ?_⟩
    have hxx : x = (triShear (K := K) (1 : Fin 2) (shearExp (1 : Fin 2) 1))
        ((triShear (K := K) (1 : Fin 2) (shearExp (1 : Fin 2) 1)).symm x) :=
      ((triShear (K := K) (1 : Fin 2) (shearExp (1 : Fin 2) 1)).apply_symm_apply
        x).symm
    rw [hxx, hh, map_mul, triShear_recipe_span_sub_gen_one]
  · rw [Ideal.span_le]
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst hx
    change MvPolynomial.X (0 : Fin 2) ∈ Ideal.comap
      (triShear (K := K) (1 : Fin 2) (shearExp (1 : Fin 2) 1)).symm.toAlgHom.toRingHom
      (Ideal.span {(MvPolynomial.X 0 - MvPolynomial.X 1 :
        MvPolynomial (Fin 2) K)})
    rw [Ideal.mem_comap]
    have hx2 : (triShear (K := K) (1 : Fin 2) (shearExp (1 : Fin 2) 1)).symm
        (MvPolynomial.X (0 : Fin 2)) ∈
        Ideal.span {(MvPolynomial.X 0 - MvPolynomial.X 1 :
          MvPolynomial (Fin 2) K)} := by
      rw [triShear_backsubst _ _ _ h01, hd0, pow_one]
      exact Ideal.subset_span rfl
    exact hx2

/-- No element of `span {X₀}` is weak-monic in `X₁`: every monomial carries
`X₀`-content, so all pure-`X₁` coefficients vanish (via `coeff_mul` over the
antidiagonal). -/
theorem no_weakmonic_in_span_x0 {K : Type*} [Field K]
    (f : MvPolynomial (Fin 2) K)
    (hf : f ∈ Ideal.span {(MvPolynomial.X 0 : MvPolynomial (Fin 2) K)})
    (e : ℕ) (hcoeff : f.coeff (Finsupp.single 1 e) = 1) : False := by
  rw [Ideal.mem_span_singleton] at hf
  obtain ⟨h, rfl⟩ := hf
  have h0 : ((MvPolynomial.X 0 : MvPolynomial (Fin 2) K) * h).coeff
      (Finsupp.single 1 e) = 0 := by
    rw [MvPolynomial.coeff_mul]
    apply Finset.sum_eq_zero
    intro x hx
    have hmem : x.1 + x.2 = Finsupp.single (1 : Fin 2) e :=
      Finset.mem_antidiagonal.mp hx
    have hx0 : x.1 (0 : Fin 2) = 0 := by
      have h2 := congrArg (fun a : Fin 2 →₀ ℕ => a (0 : Fin 2)) hmem
      rw [Finsupp.add_apply] at h2
      have h3 : (Finsupp.single (1 : Fin 2) e) (0 : Fin 2) = 0 :=
        Finsupp.single_eq_of_ne (by decide : (0 : Fin 2) ≠ (1 : Fin 2))
      rw [h3] at h2
      omega
    have hne : x.1 ≠ Finsupp.single (0 : Fin 2) 1 := by
      intro hcon
      have h2 := congrArg (fun a : Fin 2 →₀ ℕ => a (0 : Fin 2)) hcon
      rw [Finsupp.single_eq_same] at h2
      omega
    have hX : (MvPolynomial.X 0 : MvPolynomial (Fin 2) K).coeff x.1 = 0 := by
      rw [MvPolynomial.coeff_X, ite_eq_right (Ne.symm hne)]
    rw [hX, zero_mul]
  rw [h0] at hcoeff
  exact one_ne_zero hcoeff.symm

/-- The weakened fiber is false for `span {X₀ - X₁}` at `j = 1`, `D = 1`:
the recipe contraction is `span {X₀}`, which holds no weak-monic element. -/
theorem weakFiberPred_false_new_recipe_one {K : Type*} [Field K] :
    ¬ fiberPredWeak 2 K
      (Ideal.span {(MvPolynomial.X 0 - MvPolynomial.X 1 :
        MvPolynomial (Fin 2) K)}) (1 : Fin 2) (shearExp (1 : Fin 2) 1) := by
  intro hcon
  have hne : Ideal.span {(MvPolynomial.X 0 - MvPolynomial.X 1 :
      MvPolynomial (Fin 2) K)} ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]
    intro hzero
    have h1 : (MvPolynomial.X 0 - MvPolynomial.X 1 :
        MvPolynomial (Fin 2) K).coeff (Finsupp.single 0 1) = 1 := by
      rw [spanSub_coeff_single, ite_eq_left rfl]
    have hmem : Finsupp.single (0 : Fin 2) 1 ∈
        (MvPolynomial.X 0 - MvPolynomial.X 1 :
          MvPolynomial (Fin 2) K).support := by
      rw [MvPolynomial.mem_support_iff, h1]
      exact one_ne_zero
    rw [hzero] at hmem
    simp at hmem
  obtain ⟨⟨f, hf, -, e, -, -, hcoeff⟩, -⟩ := hcon hne
  rw [contraction_recipe_span_sub_one] at hf
  exact no_weakmonic_in_span_x0 f hf e hcoeff

/-- Mirrored collapse at `j = 0`, `D = 1`: the shear sends `X₀ - X₁ ↦ -X₁`. -/
theorem triShear_recipe_span_sub_gen_zero {K : Type*} [Field K] :
    (triShear (K := K) (0 : Fin 2) (shearExp (0 : Fin 2) 1))
      (MvPolynomial.X 0 - MvPolynomial.X 1) = -MvPolynomial.X 1 := by
  have h10 : (1 : Fin 2) ≠ (0 : Fin 2) := by decide
  have hd1 : shearExp (0 : Fin 2) 1 (1 : Fin 2) = 1 := by
    have hv : ((1 : Fin 2).val + 1) = 2 := by decide
    simp only [shearExp, h10, ite_false, hv, one_pow]
  rw [map_sub, triShear_fixes, triShear_apply, ite_eq_right h10, hd1, pow_one]
  abel

/-- The recipe contraction of `span {X₀ - X₁}` at `j = 0`, `D = 1` is
`span {X₁}`. -/
theorem contraction_recipe_span_sub_zero {K : Type*} [Field K] :
    shearContraction (0 : Fin 2) (shearExp (0 : Fin 2) 1)
      (Ideal.span {(MvPolynomial.X 0 - MvPolynomial.X 1 :
        MvPolynomial (Fin 2) K)}) =
    Ideal.span {(MvPolynomial.X 1 : MvPolynomial (Fin 2) K)} := by
  have h10 : (1 : Fin 2) ≠ (0 : Fin 2) := by decide
  have hd1 : shearExp (0 : Fin 2) 1 (1 : Fin 2) = 1 := by
    have hv : ((1 : Fin 2).val + 1) = 2 := by decide
    simp only [shearExp, h10, ite_false, hv, one_pow]
  apply le_antisymm
  · intro x hx
    unfold shearContraction at hx
    rw [Ideal.mem_comap] at hx
    have hx2 : (triShear (K := K) (0 : Fin 2) (shearExp (0 : Fin 2) 1)).symm x ∈
        Ideal.span {(MvPolynomial.X 0 - MvPolynomial.X 1 :
          MvPolynomial (Fin 2) K)} := hx
    rw [Ideal.mem_span_singleton] at hx2
    obtain ⟨h, hh⟩ := hx2
    rw [Ideal.mem_span_singleton]
    refine ⟨-((triShear (K := K) (0 : Fin 2) (shearExp (0 : Fin 2) 1)) h), ?_⟩
    have hxx : x = (triShear (K := K) (0 : Fin 2) (shearExp (0 : Fin 2) 1))
        ((triShear (K := K) (0 : Fin 2) (shearExp (0 : Fin 2) 1)).symm x) :=
      ((triShear (K := K) (0 : Fin 2) (shearExp (0 : Fin 2) 1)).apply_symm_apply
        x).symm
    rw [hxx, hh, map_mul, triShear_recipe_span_sub_gen_zero]
    ring
  · rw [Ideal.span_le]
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst hx
    change MvPolynomial.X (1 : Fin 2) ∈ Ideal.comap
      (triShear (K := K) (0 : Fin 2) (shearExp (0 : Fin 2) 1)).symm.toAlgHom.toRingHom
      (Ideal.span {(MvPolynomial.X 0 - MvPolynomial.X 1 :
        MvPolynomial (Fin 2) K)})
    rw [Ideal.mem_comap]
    have hx2 : (triShear (K := K) (0 : Fin 2) (shearExp (0 : Fin 2) 1)).symm
        (MvPolynomial.X (1 : Fin 2)) ∈
        Ideal.span {(MvPolynomial.X 0 - MvPolynomial.X 1 :
          MvPolynomial (Fin 2) K)} := by
      rw [triShear_backsubst _ _ _ h10, hd1, pow_one,
        Ideal.mem_span_singleton]
      exact ⟨-1, by ring⟩
    exact hx2

/-- No element of `span {X₁}` is weak-monic in `X₀` (mirror of
`no_weakmonic_in_span_x0`). -/
theorem no_weakmonic_in_span_x1 {K : Type*} [Field K]
    (f : MvPolynomial (Fin 2) K)
    (hf : f ∈ Ideal.span {(MvPolynomial.X 1 : MvPolynomial (Fin 2) K)})
    (e : ℕ) (hcoeff : f.coeff (Finsupp.single 0 e) = 1) : False := by
  rw [Ideal.mem_span_singleton] at hf
  obtain ⟨h, rfl⟩ := hf
  have h0 : ((MvPolynomial.X 1 : MvPolynomial (Fin 2) K) * h).coeff
      (Finsupp.single 0 e) = 0 := by
    rw [MvPolynomial.coeff_mul]
    apply Finset.sum_eq_zero
    intro x hx
    have hmem : x.1 + x.2 = Finsupp.single (0 : Fin 2) e :=
      Finset.mem_antidiagonal.mp hx
    have hx1 : x.1 (1 : Fin 2) = 0 := by
      have h2 := congrArg (fun a : Fin 2 →₀ ℕ => a (1 : Fin 2)) hmem
      rw [Finsupp.add_apply] at h2
      have h3 : (Finsupp.single (0 : Fin 2) e) (1 : Fin 2) = 0 :=
        Finsupp.single_eq_of_ne (by decide : (1 : Fin 2) ≠ (0 : Fin 2))
      rw [h3] at h2
      omega
    have hne : x.1 ≠ Finsupp.single (1 : Fin 2) 1 := by
      intro hcon
      have h2 := congrArg (fun a : Fin 2 →₀ ℕ => a (1 : Fin 2)) hcon
      rw [Finsupp.single_eq_same] at h2
      omega
    have hX : (MvPolynomial.X 1 : MvPolynomial (Fin 2) K).coeff x.1 = 0 := by
      rw [MvPolynomial.coeff_X, ite_eq_right (Ne.symm hne)]
    rw [hX, zero_mul]
  rw [h0] at hcoeff
  exact one_ne_zero hcoeff.symm

/-- The weakened fiber is false for `span {X₀ - X₁}` at `j = 0`, `D = 1`. -/
theorem weakFiberPred_false_span_sub_recipe_zero {K : Type*} [Field K] :
    ¬ fiberPredWeak 2 K
      (Ideal.span {(MvPolynomial.X 0 - MvPolynomial.X 1 :
        MvPolynomial (Fin 2) K)}) (0 : Fin 2) (shearExp (0 : Fin 2) 1) := by
  intro hcon
  have hne : Ideal.span {(MvPolynomial.X 0 - MvPolynomial.X 1 :
      MvPolynomial (Fin 2) K)} ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]
    intro hzero
    have h1 : (MvPolynomial.X 0 - MvPolynomial.X 1 :
        MvPolynomial (Fin 2) K).coeff (Finsupp.single 0 1) = 1 := by
      rw [spanSub_coeff_single, ite_eq_left rfl]
    have hmem : Finsupp.single (0 : Fin 2) 1 ∈
        (MvPolynomial.X 0 - MvPolynomial.X 1 :
          MvPolynomial (Fin 2) K).support := by
      rw [MvPolynomial.mem_support_iff, h1]
      exact one_ne_zero
    rw [hzero] at hmem
    simp at hmem
  obtain ⟨⟨f, hf, -, e, -, -, hcoeff⟩, -⟩ := hcon hne
  rw [contraction_recipe_span_sub_zero] at hf
  exact no_weakmonic_in_span_x1 f hf e hcoeff

/-- Sharp boundary: a general shear with `d 0 ≠ 1` escapes the collapse — the
carried generator `σ(X₀ - X₁) = X₀ + X₁ ^ d₀ - X₁` is already weak-monic (up
to a scalar) in the contraction. -/
theorem weakFiberMonic_escape_of_ne {K : Type*} [Field K]
    (d : Fin 2 → ℕ) (hd : d (0 : Fin 2) ≠ 1) :
    ∃ f : MvPolynomial (Fin 2) K,
      f ∈ shearContraction (1 : Fin 2) d
        (Ideal.span {(MvPolynomial.X 0 - MvPolynomial.X 1 :
          MvPolynomial (Fin 2) K)}) ∧ f ≠ 0 ∧
      ∃ e : ℕ, e ≠ 0 ∧ f.degreeOf 1 = e ∧
        f.coeff (Finsupp.single 1 e) = 1 := by
  have h01 : (0 : Fin 2) ≠ (1 : Fin 2) := by decide
  have h10 : (1 : Fin 2) ≠ (0 : Fin 2) := by decide
  have hG : (triShear (K := K) (1 : Fin 2) d)
      (MvPolynomial.X 0 - MvPolynomial.X 1) =
      MvPolynomial.X 0 + MvPolynomial.X 1 ^ d (0 : Fin 2) -
        MvPolynomial.X 1 := by
    rw [map_sub, triShear_apply, ite_eq_right h01, triShear_fixes]
  have hmem : (triShear (K := K) (1 : Fin 2) d)
      (MvPolynomial.X 0 - MvPolynomial.X 1) ∈
      shearContraction (1 : Fin 2) d
        (Ideal.span {(MvPolynomial.X 0 - MvPolynomial.X 1 :
          MvPolynomial (Fin 2) K)}) := by
    change (triShear (K := K) (1 : Fin 2) d)
      (MvPolynomial.X 0 - MvPolynomial.X 1) ∈ Ideal.comap
      (triShear (K := K) (1 : Fin 2) d).symm.toAlgHom.toRingHom
      (Ideal.span {(MvPolynomial.X 0 - MvPolynomial.X 1 :
        MvPolynomial (Fin 2) K)})
    rw [Ideal.mem_comap]
    have hback : ((triShear (K := K) (1 : Fin 2) d).symm.toAlgHom.toRingHom)
        ((triShear (K := K) (1 : Fin 2) d)
          (MvPolynomial.X 0 - MvPolynomial.X 1)) =
        MvPolynomial.X 0 - MvPolynomial.X 1 :=
      (triShear (K := K) (1 : Fin 2) d).symm_apply_apply _
    rw [hback]
    exact Ideal.subset_span rfl
  have hX0deg : (MvPolynomial.X 0 : MvPolynomial (Fin 2) K).degreeOf 1 = 0 := by
    simp only [MvPolynomial.degreeOf_X,
      show (1 : Fin 2) ≠ (0 : Fin 2) from by decide, ite_false]
  by_cases hd0 : d (0 : Fin 2) = 0
  · have hG0 : (triShear (K := K) (1 : Fin 2) d)
        (MvPolynomial.X 0 - MvPolynomial.X 1) =
        MvPolynomial.X 0 + 1 - MvPolynomial.X 1 := by
      rw [hG, hd0, pow_zero]
    have hs0 : Finsupp.single (1 : Fin 2) (1 : ℕ) ≠ 0 := by
      intro hcon
      have h2 := congrArg (fun a : Fin 2 →₀ ℕ => a (1 : Fin 2)) hcon
      rw [Finsupp.single_eq_same] at h2
      simp at h2
    have hne01 : Finsupp.single (0 : Fin 2) (1 : ℕ) ≠
        Finsupp.single (1 : Fin 2) 1 := by
      intro hcon
      have h2 := congrArg (fun a : Fin 2 →₀ ℕ => a (0 : Fin 2)) hcon
      rw [Finsupp.single_eq_same,
        Finsupp.single_eq_of_ne (by decide : (0 : Fin 2) ≠ (1 : Fin 2))] at h2
      exact one_ne_zero h2
    have hc0 : (MvPolynomial.X 0 : MvPolynomial (Fin 2) K).coeff
        (Finsupp.single 1 1) = 0 := by
      rw [MvPolynomial.coeff_X, ite_eq_right hne01]
    have hc1 : ((1 : MvPolynomial (Fin 2) K)).coeff
        (Finsupp.single 1 1) = 0 := by
      rw [MvPolynomial.coeff_one, ite_eq_right (Ne.symm hs0)]
    have hcX : (MvPolynomial.X 1 : MvPolynomial (Fin 2) K).coeff
        (Finsupp.single 1 1) = 1 :=
      MvPolynomial.coeff_X_same _
    have hcoeff1 : (MvPolynomial.C (-1) * (triShear (K := K) (1 : Fin 2) d)
        (MvPolynomial.X 0 - MvPolynomial.X 1)).coeff
        (Finsupp.single 1 1) = 1 := by
      rw [MvPolynomial.coeff_C_mul, hG0, MvPolynomial.coeff_sub,
        AddMonoidAlgebra.coeff_add, Finsupp.add_apply, hc0, hc1, hcX]
      ring
    have hdeg1 : (MvPolynomial.C (-1) * (triShear (K := K) (1 : Fin 2) d)
        (MvPolynomial.X 0 - MvPolynomial.X 1)).degreeOf 1 = 1 := by
      apply le_antisymm
      · have h1 := MvPolynomial.degreeOf_sub_le (1 : Fin 2)
          (MvPolynomial.X 0 + 1 : MvPolynomial (Fin 2) K)
          (MvPolynomial.X 1 : MvPolynomial (Fin 2) K)
        have h2 := MvPolynomial.degreeOf_add_le (1 : Fin 2)
          (MvPolynomial.X 0 : MvPolynomial (Fin 2) K)
          (1 : MvPolynomial (Fin 2) K)
        rw [hX0deg, MvPolynomial.degreeOf_one] at h2
        have h3 : (MvPolynomial.X 1 : MvPolynomial (Fin 2) K).degreeOf 1 = 1 :=
          MvPolynomial.degreeOf_X_self _
        have hle0 : (MvPolynomial.X 0 + 1 :
            MvPolynomial (Fin 2) K).degreeOf 1 ≤ 0 :=
          le_trans h2 (by decide)
        refine le_trans (MvPolynomial.degreeOf_C_mul_le _ _ _) ?_
        rw [hG0]
        omega
      · have hmem1 : Finsupp.single (1 : Fin 2) 1 ∈
            (MvPolynomial.C (-1) * (triShear (K := K) (1 : Fin 2) d)
              (MvPolynomial.X 0 - MvPolynomial.X 1)).support := by
          rw [MvPolynomial.mem_support_iff, hcoeff1]
          exact one_ne_zero
        have hle := MvPolynomial.monomial_le_degreeOf (1 : Fin 2) hmem1
        rwa [Finsupp.single_eq_same] at hle
    have hne1 : MvPolynomial.C (-1) * (triShear (K := K) (1 : Fin 2) d)
        (MvPolynomial.X 0 - MvPolynomial.X 1) ≠ 0 :=
      MvPolynomial.ne_zero_iff.mpr
        ⟨_, by rw [hcoeff1]; exact one_ne_zero⟩
    exact ⟨_, Ideal.mul_mem_left _ _ hmem, hne1, 1, one_ne_zero, hdeg1,
      hcoeff1⟩
  · have hdpos : 0 < d (0 : Fin 2) := Nat.pos_of_ne_zero hd0
    have hd1 : 1 < d (0 : Fin 2) := by omega
    have hneA : Finsupp.single (0 : Fin 2) (1 : ℕ) ≠
        Finsupp.single (1 : Fin 2) (d (0 : Fin 2)) := by
      intro hcon
      have h2 := congrArg (fun a : Fin 2 →₀ ℕ => a (0 : Fin 2)) hcon
      rw [Finsupp.single_eq_same,
        Finsupp.single_eq_of_ne (by decide : (0 : Fin 2) ≠ (1 : Fin 2))] at h2
      exact one_ne_zero h2
    have hneB : Finsupp.single (1 : Fin 2) (1 : ℕ) ≠
        Finsupp.single (1 : Fin 2) (d (0 : Fin 2)) := by
      intro hcon
      have h2 := congrArg (fun a : Fin 2 →₀ ℕ => a (1 : Fin 2)) hcon
      rw [Finsupp.single_eq_same, Finsupp.single_eq_same] at h2
      omega
    have hc0' : (MvPolynomial.X 0 : MvPolynomial (Fin 2) K).coeff
        (Finsupp.single 1 (d (0 : Fin 2))) = 0 := by
      rw [MvPolynomial.coeff_X, ite_eq_right hneA]
    have hcX' : (MvPolynomial.X 1 ^ d (0 : Fin 2) :
        MvPolynomial (Fin 2) K).coeff
        (Finsupp.single 1 (d (0 : Fin 2))) = 1 := by
      rw [MvPolynomial.coeff_X_pow, ite_eq_left rfl]
    have hc1' : (MvPolynomial.X 1 : MvPolynomial (Fin 2) K).coeff
        (Finsupp.single 1 (d (0 : Fin 2))) = 0 := by
      rw [MvPolynomial.coeff_X, ite_eq_right hneB]
    have hcoeff' : ((triShear (K := K) (1 : Fin 2) d)
        (MvPolynomial.X 0 - MvPolynomial.X 1)).coeff
        (Finsupp.single 1 (d (0 : Fin 2))) = 1 := by
      rw [hG, MvPolynomial.coeff_sub, AddMonoidAlgebra.coeff_add,
        Finsupp.add_apply, hc0', hcX', hc1']
      simp
    have hdeg' : ((triShear (K := K) (1 : Fin 2) d)
        (MvPolynomial.X 0 - MvPolynomial.X 1)).degreeOf 1 = d (0 : Fin 2) := by
      apply le_antisymm
      · have h1 := MvPolynomial.degreeOf_sub_le (1 : Fin 2)
          (MvPolynomial.X 0 + MvPolynomial.X 1 ^ d (0 : Fin 2) :
            MvPolynomial (Fin 2) K)
          (MvPolynomial.X 1 : MvPolynomial (Fin 2) K)
        have h2 := MvPolynomial.degreeOf_add_le (1 : Fin 2)
          (MvPolynomial.X 0 : MvPolynomial (Fin 2) K)
          (MvPolynomial.X 1 ^ d (0 : Fin 2) : MvPolynomial (Fin 2) K)
        rw [hX0deg, MvPolynomial.degreeOf_X_self_pow] at h2
        have h3 : (MvPolynomial.X 1 : MvPolynomial (Fin 2) K).degreeOf 1 = 1 :=
          MvPolynomial.degreeOf_X_self _
        rw [hG]
        omega
      · have hmem' : Finsupp.single (1 : Fin 2) (d (0 : Fin 2)) ∈
            ((triShear (K := K) (1 : Fin 2) d)
              (MvPolynomial.X 0 - MvPolynomial.X 1)).support := by
          rw [MvPolynomial.mem_support_iff, hcoeff']
          exact one_ne_zero
        have hle := MvPolynomial.monomial_le_degreeOf (1 : Fin 2) hmem'
        rwa [Finsupp.single_eq_same] at hle
    have hne' : (triShear (K := K) (1 : Fin 2) d)
        (MvPolynomial.X 0 - MvPolynomial.X 1) ≠ 0 :=
      MvPolynomial.ne_zero_iff.mpr
        ⟨_, by rw [hcoeff']; exact one_ne_zero⟩
    exact ⟨_, hmem, hne', _, by omega, hdeg', hcoeff'⟩

/-- Production at `1 < D`: the weakened fiber's monic conjunct is inhabited
for `span {X₀ - X₁}` at `j = 1` — the recipe off-`j` exponent is `D ≠ 1`,
so the escape lemma fires. -/
theorem weakFiberMonic_new_recipe_of_lt {K : Type*} [Field K] (D : ℕ)
    (hD : 1 < D) :
    ∃ f : MvPolynomial (Fin 2) K,
      f ∈ shearContraction (1 : Fin 2) (shearExp (1 : Fin 2) D)
        (Ideal.span {(MvPolynomial.X 0 - MvPolynomial.X 1 :
          MvPolynomial (Fin 2) K)}) ∧ f ≠ 0 ∧
      ∃ e : ℕ, e ≠ 0 ∧ f.degreeOf 1 = e ∧
        f.coeff (Finsupp.single 1 e) = 1 := by
  apply weakFiberMonic_escape_of_ne
  have h01 : (0 : Fin 2) ≠ (1 : Fin 2) := by decide
  have hv : ((0 : Fin 2).val + 1) = 1 := by decide
  have hexp : shearExp (1 : Fin 2) D (0 : Fin 2) = D := by
    simp only [shearExp, h01, ite_false, hv, pow_one]
  rw [hexp]
  omega

/-! ## (xiii) Strong-monic expansion: the carried generator.

At `1 < D` the carried generator `σ(X₀ - X₁) = X₀ + X₁ ^ D - X₁` is
strong-monic in `X₁`: its `X₁`-degree is `D` with top coefficient `1`
(`carriedGen_coeff_top`, `carriedGen_degreeOf`), and every other support
element has `X₁`-degree strictly below `D` (`carriedGen_strong`, via the
three-point support computation `carriedGen_coeff_x0`,
`carriedGen_coeff_sub`, `carriedGen_coeff_other`, `carriedGen_support_sub`).
The conjunction (`carriedGen_strongMonic`) is exactly the input shape of the
integrality lifting `delVarQuot_isIntegral_of_strongMonic` — the
weak-to-strong upgrade in the diagonal test case. -/

/-- Top coefficient of the carried generator: `1` at `single 1 D`. -/
theorem carriedGen_coeff_top {K : Type*} [Field K] (D : ℕ) (hD : 1 < D) :
    (MvPolynomial.X 0 + MvPolynomial.X 1 ^ D - MvPolynomial.X 1 :
      MvPolynomial (Fin 2) K).coeff (Finsupp.single 1 D) = 1 := by
  have hD1 : D ≠ 1 := by omega
  have hA : Finsupp.single (0 : Fin 2) (1 : ℕ) ≠
      Finsupp.single (1 : Fin 2) D := by
    intro hcon
    have h2 := congrArg (fun a : Fin 2 →₀ ℕ => a (0 : Fin 2)) hcon
    rw [Finsupp.single_eq_same,
      Finsupp.single_eq_of_ne (by decide : (0 : Fin 2) ≠ (1 : Fin 2))] at h2
    exact one_ne_zero h2
  have hB : Finsupp.single (1 : Fin 2) (1 : ℕ) ≠
      Finsupp.single (1 : Fin 2) D := by
    intro hcon
    have h2 := congrArg (fun a : Fin 2 →₀ ℕ => a (1 : Fin 2)) hcon
    rw [Finsupp.single_eq_same, Finsupp.single_eq_same] at h2
    exact hD1 h2.symm
  have eX0 : (MvPolynomial.X 0 : MvPolynomial (Fin 2) K).coeff
      (Finsupp.single 1 D) = 0 := by
    rw [MvPolynomial.coeff_X, ite_eq_right hA]
  have eXD : (MvPolynomial.X 1 ^ D : MvPolynomial (Fin 2) K).coeff
      (Finsupp.single 1 D) = 1 := by
    rw [MvPolynomial.coeff_X_pow, ite_eq_left rfl]
  have eX1 : (MvPolynomial.X 1 : MvPolynomial (Fin 2) K).coeff
      (Finsupp.single 1 D) = 0 := by
    rw [MvPolynomial.coeff_X, ite_eq_right hB]
  rw [MvPolynomial.coeff_sub, AddMonoidAlgebra.coeff_add, Finsupp.add_apply,
    eX0, eXD, eX1]
  simp

/-- The carried generator has coefficient `1` at `single 0 1`. -/
theorem carriedGen_coeff_x0 {K : Type*} [Field K] (D : ℕ) (_hD : 1 < D) :
    (MvPolynomial.X 0 + MvPolynomial.X 1 ^ D - MvPolynomial.X 1 :
      MvPolynomial (Fin 2) K).coeff (Finsupp.single 0 1) = 1 := by
  have hC : Finsupp.single (1 : Fin 2) D ≠
      Finsupp.single (0 : Fin 2) (1 : ℕ) := by
    intro hcon
    have h2 := congrArg (fun a : Fin 2 →₀ ℕ => a (0 : Fin 2)) hcon
    rw [Finsupp.single_eq_of_ne (by decide : (0 : Fin 2) ≠ (1 : Fin 2)),
      Finsupp.single_eq_same] at h2
    exact one_ne_zero h2.symm
  have hE : Finsupp.single (1 : Fin 2) (1 : ℕ) ≠
      Finsupp.single (0 : Fin 2) (1 : ℕ) := by
    intro hcon
    have h2 := congrArg (fun a : Fin 2 →₀ ℕ => a (0 : Fin 2)) hcon
    rw [Finsupp.single_eq_of_ne (by decide : (0 : Fin 2) ≠ (1 : Fin 2)),
      Finsupp.single_eq_same] at h2
    exact one_ne_zero h2.symm
  have eX0 : (MvPolynomial.X 0 : MvPolynomial (Fin 2) K).coeff
      (Finsupp.single 0 1) = 1 :=
    MvPolynomial.coeff_X_same _
  have eXD : (MvPolynomial.X 1 ^ D : MvPolynomial (Fin 2) K).coeff
      (Finsupp.single 0 1) = 0 := by
    rw [MvPolynomial.coeff_X_pow, ite_eq_right hC]
  have eX1 : (MvPolynomial.X 1 : MvPolynomial (Fin 2) K).coeff
      (Finsupp.single 0 1) = 0 := by
    rw [MvPolynomial.coeff_X, ite_eq_right hE]
  rw [MvPolynomial.coeff_sub, AddMonoidAlgebra.coeff_add, Finsupp.add_apply,
    eX0, eXD, eX1]
  simp

/-- The carried generator has coefficient `-1` at `single 1 1`. -/
theorem carriedGen_coeff_sub {K : Type*} [Field K] (D : ℕ) (hD : 1 < D) :
    (MvPolynomial.X 0 + MvPolynomial.X 1 ^ D - MvPolynomial.X 1 :
      MvPolynomial (Fin 2) K).coeff (Finsupp.single 1 1) = -1 := by
  have hD1 : D ≠ 1 := by omega
  have hF : Finsupp.single (0 : Fin 2) (1 : ℕ) ≠
      Finsupp.single (1 : Fin 2) (1 : ℕ) := by
    intro hcon
    have h2 := congrArg (fun a : Fin 2 →₀ ℕ => a (0 : Fin 2)) hcon
    rw [Finsupp.single_eq_same,
      Finsupp.single_eq_of_ne (by decide : (0 : Fin 2) ≠ (1 : Fin 2))] at h2
    exact one_ne_zero h2
  have hG : Finsupp.single (1 : Fin 2) D ≠
      Finsupp.single (1 : Fin 2) (1 : ℕ) := by
    intro hcon
    have h2 := congrArg (fun a : Fin 2 →₀ ℕ => a (1 : Fin 2)) hcon
    rw [Finsupp.single_eq_same, Finsupp.single_eq_same] at h2
    exact hD1 h2
  have eX0 : (MvPolynomial.X 0 : MvPolynomial (Fin 2) K).coeff
      (Finsupp.single 1 1) = 0 := by
    rw [MvPolynomial.coeff_X, ite_eq_right hF]
  have eXD : (MvPolynomial.X 1 ^ D : MvPolynomial (Fin 2) K).coeff
      (Finsupp.single 1 1) = 0 := by
    rw [MvPolynomial.coeff_X_pow, ite_eq_right hG]
  have eX1 : (MvPolynomial.X 1 : MvPolynomial (Fin 2) K).coeff
      (Finsupp.single 1 1) = 1 :=
    MvPolynomial.coeff_X_same _
  rw [MvPolynomial.coeff_sub, AddMonoidAlgebra.coeff_add, Finsupp.add_apply,
    eX0, eXD, eX1]
  simp

/-- All other coefficients of the carried generator vanish. -/
theorem carriedGen_coeff_other {K : Type*} [Field K] (D : ℕ)
    (a : Fin 2 →₀ ℕ)
    (h0 : a ≠ Finsupp.single (0 : Fin 2) 1)
    (hDD : a ≠ Finsupp.single (1 : Fin 2) D)
    (h1 : a ≠ Finsupp.single (1 : Fin 2) 1) :
    (MvPolynomial.X 0 + MvPolynomial.X 1 ^ D - MvPolynomial.X 1 :
      MvPolynomial (Fin 2) K).coeff a = 0 := by
  have eX0 : (MvPolynomial.X 0 : MvPolynomial (Fin 2) K).coeff a = 0 := by
    rw [MvPolynomial.coeff_X, ite_eq_right (Ne.symm h0)]
  have eXD : (MvPolynomial.X 1 ^ D : MvPolynomial (Fin 2) K).coeff a = 0 := by
    rw [MvPolynomial.coeff_X_pow, ite_eq_right (Ne.symm hDD)]
  have eX1 : (MvPolynomial.X 1 : MvPolynomial (Fin 2) K).coeff a = 0 := by
    rw [MvPolynomial.coeff_X, ite_eq_right (Ne.symm h1)]
  rw [MvPolynomial.coeff_sub, AddMonoidAlgebra.coeff_add, Finsupp.add_apply,
    eX0, eXD, eX1]
  simp

/-- The carried generator's support lies in the three computed points. -/
theorem carriedGen_support_sub {K : Type*} [Field K] (D : ℕ) :
    (MvPolynomial.X 0 + MvPolynomial.X 1 ^ D - MvPolynomial.X 1 :
      MvPolynomial (Fin 2) K).support ⊆
      {Finsupp.single (0 : Fin 2) 1, Finsupp.single 1 D,
        Finsupp.single 1 1} := by
  intro a ha
  rw [MvPolynomial.mem_support_iff] at ha
  by_cases h0 : a = Finsupp.single (0 : Fin 2) 1
  · rw [h0]
    exact Finset.mem_insert_self _ _
  · by_cases hDD : a = Finsupp.single (1 : Fin 2) D
    · rw [hDD]
      exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
    · by_cases h1 : a = Finsupp.single (1 : Fin 2) 1
      · rw [h1]
        exact Finset.mem_insert_of_mem
          (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
      · exact absurd (carriedGen_coeff_other D a h0 hDD h1) ha

/-- The carried generator has `X₁`-degree exactly `D`. -/
theorem carriedGen_degreeOf {K : Type*} [Field K] (D : ℕ) (hD : 1 < D) :
    (MvPolynomial.X 0 + MvPolynomial.X 1 ^ D - MvPolynomial.X 1 :
      MvPolynomial (Fin 2) K).degreeOf 1 = D := by
  apply le_antisymm
  · have h1 := MvPolynomial.degreeOf_sub_le (1 : Fin 2)
      (MvPolynomial.X 0 + MvPolynomial.X 1 ^ D : MvPolynomial (Fin 2) K)
      (MvPolynomial.X 1 : MvPolynomial (Fin 2) K)
    have h2 := MvPolynomial.degreeOf_add_le (1 : Fin 2)
      (MvPolynomial.X 0 : MvPolynomial (Fin 2) K)
      (MvPolynomial.X 1 ^ D : MvPolynomial (Fin 2) K)
    have hX0deg : (MvPolynomial.X 0 : MvPolynomial (Fin 2) K).degreeOf 1 = 0 := by
      simp only [MvPolynomial.degreeOf_X,
        show (1 : Fin 2) ≠ (0 : Fin 2) from by decide, ite_false]
    rw [hX0deg, MvPolynomial.degreeOf_X_self_pow] at h2
    have h3 : (MvPolynomial.X 1 : MvPolynomial (Fin 2) K).degreeOf 1 = 1 :=
      MvPolynomial.degreeOf_X_self _
    omega
  · have hmem : Finsupp.single (1 : Fin 2) D ∈
        (MvPolynomial.X 0 + MvPolynomial.X 1 ^ D - MvPolynomial.X 1 :
          MvPolynomial (Fin 2) K).support := by
      rw [MvPolynomial.mem_support_iff, carriedGen_coeff_top D hD]
      exact one_ne_zero
    have hle := MvPolynomial.monomial_le_degreeOf (1 : Fin 2) hmem
    rwa [Finsupp.single_eq_same] at hle

/-- Strongness: every non-top support element has `X₁`-degree below `D`. -/
theorem carriedGen_strong {K : Type*} [Field K] (D : ℕ) (hD : 1 < D)
    (a : Fin 2 →₀ ℕ)
    (ha : a ∈ (MvPolynomial.X 0 + MvPolynomial.X 1 ^ D - MvPolynomial.X 1 :
      MvPolynomial (Fin 2) K).support)
    (hne : a ≠ Finsupp.single (1 : Fin 2) D) :
    a (1 : Fin 2) < D := by
  have hsub := carriedGen_support_sub (K := K) D ha
  simp only [Finset.mem_insert, Finset.mem_singleton] at hsub
  rcases hsub with rfl | rfl | rfl
  · rw [Finsupp.single_eq_of_ne (by decide : (1 : Fin 2) ≠ (0 : Fin 2))]
    omega
  · exact absurd rfl hne
  · rw [Finsupp.single_eq_same]
    exact hD

/-- The carried generator is strong-monic: degree pinned at `D` with top
coefficient `1`, all other support elements strictly below `D` in `X₁`-degree
— exactly the input shape of `delVarQuot_isIntegral_of_strongMonic`. -/
theorem carriedGen_strongMonic {K : Type*} [Field K] (D : ℕ) (hD : 1 < D) :
    (MvPolynomial.X 0 + MvPolynomial.X 1 ^ D - MvPolynomial.X 1 :
      MvPolynomial (Fin 2) K).degreeOf 1 = D ∧
    (MvPolynomial.X 0 + MvPolynomial.X 1 ^ D - MvPolynomial.X 1 :
      MvPolynomial (Fin 2) K).coeff (Finsupp.single 1 D) = 1 ∧
    ∀ a ∈ (MvPolynomial.X 0 + MvPolynomial.X 1 ^ D - MvPolynomial.X 1 :
      MvPolynomial (Fin 2) K).support,
      a ≠ Finsupp.single 1 D → a 1 < D :=
  ⟨carriedGen_degreeOf D hD, carriedGen_coeff_top D hD,
    carriedGen_strong D hD⟩

/-- The carried generator lies in the recipe contraction (the shear carries
`X₀ - X₁ ∈ span {X₀ - X₁}` into the contraction by definition). -/
theorem carriedGen_mem_recipe {K : Type*} [Field K] (D : ℕ) :
    (triShear (K := K) (1 : Fin 2) (shearExp (1 : Fin 2) D))
      (MvPolynomial.X 0 - MvPolynomial.X 1) ∈
    shearContraction (1 : Fin 2) (shearExp (1 : Fin 2) D)
      (Ideal.span {(MvPolynomial.X 0 - MvPolynomial.X 1 :
        MvPolynomial (Fin 2) K)}) := by
  change (triShear (K := K) (1 : Fin 2) (shearExp (1 : Fin 2) D))
    (MvPolynomial.X 0 - MvPolynomial.X 1) ∈ Ideal.comap
    (triShear (K := K) (1 : Fin 2) (shearExp (1 : Fin 2) D)).symm.toAlgHom.toRingHom
    (Ideal.span {(MvPolynomial.X 0 - MvPolynomial.X 1 :
      MvPolynomial (Fin 2) K)})
  rw [Ideal.mem_comap]
  have hback : ((triShear (K := K) (1 : Fin 2) (shearExp (1 : Fin 2) D)).symm.toAlgHom.toRingHom)
      ((triShear (K := K) (1 : Fin 2) (shearExp (1 : Fin 2) D))
        (MvPolynomial.X 0 - MvPolynomial.X 1)) =
      MvPolynomial.X 0 - MvPolynomial.X 1 :=
    (triShear (K := K) (1 : Fin 2) (shearExp (1 : Fin 2) D)).symm_apply_apply _
  rw [hback]
  exact Ideal.subset_span rfl

/-! ## (xiv) Integrality lifting: strong-monic ⇒ `delVarQuot` integral.

A strong-monic element `f ∈ Q` — top `Xⱼ`-coefficient `1` with every other
support element strictly below the top `Xⱼ`-degree `e` — makes the delete-`j`
map `delVarQuot j Q` integral. The `Xⱼ`-class satisfies the monic equation
read off from `f` (monic via `monic_X_pow_add`, evaluated through the bundled
`aeval` against the quotient equation `mk f = 0`), every other generator
class lies in the image (`rename_X`), and `MvPolynomial.induction_on` with
`RingHom.IsIntegralElem` closure under addition and multiplication extends
integrality to the whole quotient. This discharges the integrality conjunct
of `fiberPredWeak` — exactly what going-down consumes. (The hypotheses
`e ≠ 0` and `f.degreeOf j = e` are carried for interface compatibility with
the weak-monic data; the proof itself needs only the coefficient, the
support bound, and `f ∈ Q`.) -/

/-- Integrality lifting: a strong-monic element of `Q` makes `delVarQuot j Q`
integral. -/
theorem delVarQuot_isIntegral_of_strongMonic {m : ℕ} {K : Type*} [Field K]
    (j : Fin m) (Q : Ideal (MvPolynomial (Fin m) K))
    (f : MvPolynomial (Fin m) K) (hf : f ∈ Q)
    (e : ℕ) (_he : e ≠ 0)
    (_hdeg : f.degreeOf j = e)
    (hcoeff : f.coeff (Finsupp.single j e) = 1)
    (hstrong : ∀ a ∈ f.support, a ≠ Finsupp.single j e → a j < e) :
    (delVarQuot j Q).IsIntegral := by
  let : Algebra (MvPolynomial {i : Fin m // i ≠ j} K)
      (MvPolynomial (Fin m) K ⧸ Q) :=
    (delVarQuot j Q).toRingHom.toAlgebra
  have hφalg : (delVarQuot j Q).toRingHom = algebraMap _ _ := rfl
  have hφ : ∀ r : MvPolynomial {i : Fin m // i ≠ j} K,
      (delVarQuot j Q).toRingHom r = Ideal.Quotient.mk Q
        (MvPolynomial.rename (fun i : {i : Fin m // i ≠ j} => (i : Fin m))
          r) := by
    intro r
    have h1 : (delVarQuot j Q).toRingHom r =
        (Ideal.Quotient.mkₐ K Q).toRingHom
          (MvPolynomial.rename (fun i : {i : Fin m // i ≠ j} => (i : Fin m))
            r) := rfl
    rw [h1, Ideal.Quotient.mkₐ_toRingHom]
  have hinj : ∀ a : Fin m →₀ ℕ, Set.InjOn
      (fun i : {i : Fin m // i ≠ j} => (i : Fin m))
      (Subtype.val ⁻¹' ↑(a - Finsupp.single j (a j)).support) := by
    intro a x _ y _ h
    exact Subtype.val_injective h
  have hsj : ∀ a : Fin m →₀ ℕ, (a - Finsupp.single j (a j)) j = 0 := by
    intro a
    rw [Finsupp.tsub_apply, Finsupp.single_eq_same, Nat.sub_self]
  have hrange : ∀ a : Fin m →₀ ℕ, ↑(a - Finsupp.single j (a j)).support ⊆
      Set.range (fun i : {i : Fin m // i ≠ j} => (i : Fin m)) := by
    intro a b hb
    by_cases hjb : b = j
    · subst hjb
      exfalso
      rw [Finset.mem_coe, Finsupp.mem_support_iff] at hb
      exact hb (hsj a)
    · exact ⟨⟨b, hjb⟩, rfl⟩
  have hemba : ∀ a : Fin m →₀ ℕ, Finsupp.mapDomain
      (fun i : {i : Fin m // i ≠ j} => (i : Fin m))
      (Finsupp.comapDomain (fun i : {i : Fin m // i ≠ j} => (i : Fin m))
        (a - Finsupp.single j (a j)) (hinj a)) =
      a - Finsupp.single j (a j) := by
    intro a
    have h := Finsupp.embDomain_comapDomain
      (f := (⟨Subtype.val, Subtype.val_injective⟩ :
        {i : Fin m // i ≠ j} ↪ Fin m))
      (hrange a)
    rwa [Finsupp.embDomain_eq_mapDomain] at h
  have hrename : ∀ a : Fin m →₀ ℕ, (delVarQuot j Q).toRingHom
      (MvPolynomial.monomial
        (Finsupp.comapDomain (fun i : {i : Fin m // i ≠ j} => (i : Fin m))
          (a - Finsupp.single j (a j)) (hinj a))
        (f.coeff a)) =
      Ideal.Quotient.mk Q
        (MvPolynomial.monomial (a - Finsupp.single j (a j)) (f.coeff a)) := by
    intro a
    rw [hφ, MvPolynomial.rename_monomial, hemba a]
  have himg : ∀ r : MvPolynomial {i : Fin m // i ≠ j} K,
      (delVarQuot j Q).toRingHom.IsIntegralElem
        ((delVarQuot j Q).toRingHom r) := by
    intro r
    refine ⟨Polynomial.X - Polynomial.C r, Polynomial.monic_X_sub_C r, ?_⟩
    rw [Polynomial.eval₂_sub, Polynomial.eval₂_X, Polynomial.eval₂_C, sub_self]
  have hmem_top : Finsupp.single j e ∈ f.support := by
    rw [MvPolynomial.mem_support_iff, hcoeff]
    exact one_ne_zero
  have htop : MvPolynomial.monomial (Finsupp.single j e)
      (f.coeff (Finsupp.single j e)) = MvPolynomial.X j ^ e := by
    rw [hcoeff, MvPolynomial.X_pow_eq_monomial]
  have hsplit_sum : (∑ a ∈ f.support, MvPolynomial.monomial a (f.coeff a)) =
      MvPolynomial.monomial (Finsupp.single j e)
        (f.coeff (Finsupp.single j e)) +
      (∑ a ∈ f.support.erase (Finsupp.single j e),
        MvPolynomial.monomial a (f.coeff a)) :=
    (Finset.add_sum_erase _ _ hmem_top).symm
  have hterm : ∀ a ∈ f.support.erase (Finsupp.single j e),
      Ideal.Quotient.mk Q (MvPolynomial.monomial a (f.coeff a)) =
        Ideal.Quotient.mk Q (MvPolynomial.X j ^ (a j)) *
          (delVarQuot j Q).toRingHom (MvPolynomial.monomial
            (Finsupp.comapDomain (fun i : {i : Fin m // i ≠ j} => (i : Fin m))
              (a - Finsupp.single j (a j)) (hinj a))
            (f.coeff a)) := by
    intro a ha
    have hdecomp : a =
        Finsupp.single j (a j) + (a - Finsupp.single j (a j)) := by
      ext i
      by_cases hij : i = j
      · subst hij
        rw [Finsupp.add_apply, Finsupp.single_eq_same, Finsupp.tsub_apply,
          Finsupp.single_eq_same, Nat.sub_self, add_zero]
      · rw [Finsupp.add_apply, Finsupp.single_eq_of_ne hij,
          Finsupp.tsub_apply, Finsupp.single_eq_of_ne hij, Nat.sub_zero,
          zero_add]
    have e1 : MvPolynomial.monomial a (f.coeff a) =
        MvPolynomial.X j ^ (a j) *
          MvPolynomial.monomial (a - Finsupp.single j (a j)) (f.coeff a) := by
      rw [← MvPolynomial.monomial_single_add]
      exact congrArg (fun s => MvPolynomial.monomial s (f.coeff a)) hdecomp
    rw [e1, map_mul, hrename a]
  have hterm_sum : (∑ a ∈ f.support.erase (Finsupp.single j e),
        Ideal.Quotient.mk Q (MvPolynomial.monomial a (f.coeff a))) =
      ∑ a ∈ f.support.erase (Finsupp.single j e),
        Ideal.Quotient.mk Q (MvPolynomial.X j ^ (a j)) *
          (delVarQuot j Q).toRingHom (MvPolynomial.monomial
            (Finsupp.comapDomain (fun i : {i : Fin m // i ≠ j} => (i : Fin m))
              (a - Finsupp.single j (a j)) (hinj a))
            (f.coeff a)) :=
    Finset.sum_congr rfl (fun a ha => hterm a ha)
  have hmaps : ∀ a ∈ f.support.erase (Finsupp.single j e),
      (fun a => a j) a ∈ Finset.range e := by
    intro a ha
    rw [Finset.mem_range]
    exact hstrong a (Finset.mem_of_mem_erase ha) (Finset.ne_of_mem_erase ha)
  have hbmap : ∀ k : ℕ, (delVarQuot j Q).toRingHom
      (∑ a ∈ (f.support.erase (Finsupp.single j e)).filter (fun a => a j = k),
        MvPolynomial.monomial
          (Finsupp.comapDomain (fun i : {i : Fin m // i ≠ j} => (i : Fin m))
            (a - Finsupp.single j (a j)) (hinj a))
          (f.coeff a)) =
      ∑ a ∈ (f.support.erase (Finsupp.single j e)).filter (fun a => a j = k),
        (delVarQuot j Q).toRingHom (MvPolynomial.monomial
          (Finsupp.comapDomain (fun i : {i : Fin m // i ≠ j} => (i : Fin m))
            (a - Finsupp.single j (a j)) (hinj a))
          (f.coeff a)) := by
    intro k
    rw [map_sum]
  have hfib_rw := Finset.sum_fiberwise_of_maps_to (fun a ha => hmaps a ha)
    (fun a => Ideal.Quotient.mk Q (MvPolynomial.X j ^ (a j)) *
      (delVarQuot j Q).toRingHom (MvPolynomial.monomial
        (Finsupp.comapDomain (fun i : {i : Fin m // i ≠ j} => (i : Fin m))
          (a - Finsupp.single j (a j)) (hinj a))
        (f.coeff a)))
  have hgroup : (∑ a ∈ f.support.erase (Finsupp.single j e),
        Ideal.Quotient.mk Q (MvPolynomial.X j ^ (a j)) *
          (delVarQuot j Q).toRingHom (MvPolynomial.monomial
            (Finsupp.comapDomain (fun i : {i : Fin m // i ≠ j} => (i : Fin m))
              (a - Finsupp.single j (a j)) (hinj a))
            (f.coeff a))) =
      ∑ k ∈ Finset.range e, (delVarQuot j Q).toRingHom
        (∑ a ∈ (f.support.erase (Finsupp.single j e)).filter (fun a => a j = k),
          MvPolynomial.monomial
            (Finsupp.comapDomain (fun i : {i : Fin m // i ≠ j} => (i : Fin m))
              (a - Finsupp.single j (a j)) (hinj a))
            (f.coeff a)) *
        Ideal.Quotient.mk Q (MvPolynomial.X j) ^ k := by
    rw [← hfib_rw]
    refine Finset.sum_congr rfl (fun k hk => ?_)
    rw [hbmap k, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun a ha => ?_)
    have hak : a j = k := (Finset.mem_filter.mp ha).2
    set m_a : MvPolynomial {i : Fin m // i ≠ j} K :=
      MvPolynomial.monomial
        (Finsupp.comapDomain (fun i : {i : Fin m // i ≠ j} => (i : Fin m))
          (a - Finsupp.single j (a j)) (hinj a))
        (f.coeff a) with hmdef
    rw [hak]
    exact mul_comm _ _
  have hexpand : Ideal.Quotient.mk Q f =
      Ideal.Quotient.mk Q (MvPolynomial.X j) ^ e +
      ∑ k ∈ Finset.range e, (delVarQuot j Q).toRingHom
        (∑ a ∈ (f.support.erase (Finsupp.single j e)).filter (fun a => a j = k),
          MvPolynomial.monomial
            (Finsupp.comapDomain (fun i : {i : Fin m // i ≠ j} => (i : Fin m))
              (a - Finsupp.single j (a j)) (hinj a))
            (f.coeff a)) *
        Ideal.Quotient.mk Q (MvPolynomial.X j) ^ k := by
    conv_lhs => rw [MvPolynomial.as_sum f, hsplit_sum, htop]
    rw [map_add, map_pow, map_sum, hterm_sum, add_left_cancel_iff]
    exact hgroup
  have hQ0 : Ideal.Quotient.mk Q (MvPolynomial.X j) ^ e +
      ∑ k ∈ Finset.range e, (delVarQuot j Q).toRingHom
        (∑ a ∈ (f.support.erase (Finsupp.single j e)).filter (fun a => a j = k),
          MvPolynomial.monomial
            (Finsupp.comapDomain (fun i : {i : Fin m // i ≠ j} => (i : Fin m))
              (a - Finsupp.single j (a j)) (hinj a))
            (f.coeff a)) *
        Ideal.Quotient.mk Q (MvPolynomial.X j) ^ k = 0 := by
    have hzero : Ideal.Quotient.mk Q f = 0 :=
      (Ideal.Quotient.eq_zero_iff_mem).mpr hf
    rw [hexpand] at hzero
    exact hzero
  have hterm_deg : ∀ k ∈ Finset.range e,
      (Polynomial.C
        (∑ a ∈ (f.support.erase (Finsupp.single j e)).filter (fun a => a j = k),
          MvPolynomial.monomial
            (Finsupp.comapDomain (fun i : {i : Fin m // i ≠ j} => (i : Fin m))
              (a - Finsupp.single j (a j)) (hinj a))
            (f.coeff a)) *
        Polynomial.X ^ k :
        Polynomial (MvPolynomial {i : Fin m // i ≠ j} K)).degree ≤ k := by
    intro k _
    exact Polynomial.degree_C_mul_X_pow_le k _
  have hsup : (Finset.range e).sup (fun k =>
      (Polynomial.C
        (∑ a ∈ (f.support.erase (Finsupp.single j e)).filter (fun a => a j = k),
          MvPolynomial.monomial
            (Finsupp.comapDomain (fun i : {i : Fin m // i ≠ j} => (i : Fin m))
              (a - Finsupp.single j (a j)) (hinj a))
            (f.coeff a)) *
        Polynomial.X ^ k :
        Polynomial (MvPolynomial {i : Fin m // i ≠ j} K)).degree) < e := by
    rw [Finset.sup_lt_iff (WithBot.bot_lt_coe _)]
    intro k hk
    have hk' : k < e := Finset.mem_range.mp hk
    refine lt_of_le_of_lt (hterm_deg k hk) ?_
    exact_mod_cast hk'
  have hPdeg : (∑ k ∈ Finset.range e, Polynomial.C
      (∑ a ∈ (f.support.erase (Finsupp.single j e)).filter (fun a => a j = k),
        MvPolynomial.monomial
          (Finsupp.comapDomain (fun i : {i : Fin m // i ≠ j} => (i : Fin m))
            (a - Finsupp.single j (a j)) (hinj a))
          (f.coeff a)) *
      Polynomial.X ^ k :
      Polynomial (MvPolynomial {i : Fin m // i ≠ j} K)).degree < e :=
    lt_of_le_of_lt (Polynomial.degree_sum_le _ _) hsup
  have hPmonic : (Polynomial.X ^ e + ∑ k ∈ Finset.range e, Polynomial.C
      (∑ a ∈ (f.support.erase (Finsupp.single j e)).filter (fun a => a j = k),
        MvPolynomial.monomial
          (Finsupp.comapDomain (fun i : {i : Fin m // i ≠ j} => (i : Fin m))
            (a - Finsupp.single j (a j)) (hinj a))
          (f.coeff a)) *
      Polynomial.X ^ k :
      Polynomial (MvPolynomial {i : Fin m // i ≠ j} K)).Monic :=
    Polynomial.monic_X_pow_add hPdeg
  have hae : Polynomial.aeval (Ideal.Quotient.mk Q (MvPolynomial.X j))
      (Polynomial.X ^ e + ∑ k ∈ Finset.range e, Polynomial.C
        (∑ a ∈ (f.support.erase (Finsupp.single j e)).filter (fun a => a j = k),
          MvPolynomial.monomial
            (Finsupp.comapDomain (fun i : {i : Fin m // i ≠ j} => (i : Fin m))
              (a - Finsupp.single j (a j)) (hinj a))
            (f.coeff a)) *
        Polynomial.X ^ k :
        Polynomial (MvPolynomial {i : Fin m // i ≠ j} K)) = 0 := by
    have e1 : Polynomial.aeval (Ideal.Quotient.mk Q (MvPolynomial.X j))
        (Polynomial.X ^ e : Polynomial (MvPolynomial {i : Fin m // i ≠ j} K)) =
        Ideal.Quotient.mk Q (MvPolynomial.X j) ^ e := by
      rw [map_pow, Polynomial.aeval_X]
    have e2 : Polynomial.aeval (Ideal.Quotient.mk Q (MvPolynomial.X j))
        (∑ k ∈ Finset.range e, Polynomial.C
          (∑ a ∈ (f.support.erase (Finsupp.single j e)).filter
            (fun a => a j = k),
            MvPolynomial.monomial
              (Finsupp.comapDomain (fun i : {i : Fin m // i ≠ j} => (i : Fin m))
                (a - Finsupp.single j (a j)) (hinj a))
              (f.coeff a)) *
          Polynomial.X ^ k :
          Polynomial (MvPolynomial {i : Fin m // i ≠ j} K)) =
        ∑ k ∈ Finset.range e, (delVarQuot j Q).toRingHom
          (∑ a ∈ (f.support.erase (Finsupp.single j e)).filter
            (fun a => a j = k),
            MvPolynomial.monomial
              (Finsupp.comapDomain (fun i : {i : Fin m // i ≠ j} => (i : Fin m))
                (a - Finsupp.single j (a j)) (hinj a))
              (f.coeff a)) *
          Ideal.Quotient.mk Q (MvPolynomial.X j) ^ k := by
      rw [map_sum]
      refine Finset.sum_congr rfl (fun k _ => ?_)
      rw [map_mul, map_pow, Polynomial.aeval_X, Polynomial.aeval_C, ← hφalg]
    rw [map_add, e1, e2]
    exact hQ0
  have hxj : (delVarQuot j Q).toRingHom.IsIntegralElem
      (Ideal.Quotient.mk Q (MvPolynomial.X j)) := by
    refine ⟨Polynomial.X ^ e + ∑ k ∈ Finset.range e, Polynomial.C
      (∑ a ∈ (f.support.erase (Finsupp.single j e)).filter (fun a => a j = k),
        MvPolynomial.monomial
          (Finsupp.comapDomain (fun i : {i : Fin m // i ≠ j} => (i : Fin m))
            (a - Finsupp.single j (a j)) (hinj a))
          (f.coeff a)) *
      Polynomial.X ^ k, hPmonic, ?_⟩
    rw [hφalg, ← Polynomial.aeval_def]
    exact hae
  have hgen : ∀ n : Fin m, (delVarQuot j Q).toRingHom.IsIntegralElem
      (Ideal.Quotient.mk Q (MvPolynomial.X n)) := by
    intro n
    by_cases hnj : n = j
    · subst hnj
      exact hxj
    · have hX : (delVarQuot j Q).toRingHom (MvPolynomial.X ⟨n, hnj⟩) =
          Ideal.Quotient.mk Q (MvPolynomial.X n) := by
        rw [hφ, MvPolynomial.rename_X]
      rw [← hX]
      exact himg _
  have hall : ∀ y : MvPolynomial (Fin m) K ⧸ Q,
      (delVarQuot j Q).toRingHom.IsIntegralElem y := by
    intro y
    obtain ⟨g, rfl⟩ := Ideal.Quotient.mk_surjective y
    induction g using MvPolynomial.induction_on with
    | C a =>
      have hC : (delVarQuot j Q).toRingHom (MvPolynomial.C a) =
          Ideal.Quotient.mk Q (MvPolynomial.C a) := by
        rw [hφ, MvPolynomial.rename_C]
      rw [← hC]
      exact himg _
    | add p q hp hq =>
      exact RingHom.IsIntegralElem.add _ hp hq
    | mul_X p n ih =>
      rw [map_mul]
      exact RingHom.IsIntegralElem.mul _ ih (hgen n)
  exact hall

/-- Test-prime fiber assembly: for `span {X₀ - X₁}` at `j = 1` with `1 < D`,
the carried generator is strong-monic, so the weakened fiber (both conjuncts)
is inhabited — the monic conjunct from `carriedGen_strongMonic`, the
integrality conjunct by lifting. -/
theorem fiberPredWeak_span_sub_recipe_of_lt {K : Type*} [Field K] (D : ℕ)
    (hD : 1 < D) :
    fiberPredWeak 2 K
      (Ideal.span {(MvPolynomial.X 0 - MvPolynomial.X 1 :
        MvPolynomial (Fin 2) K)}) (1 : Fin 2) (shearExp (1 : Fin 2) D) := by
  intro hne
  have hmem : (MvPolynomial.X 0 + MvPolynomial.X 1 ^ D - MvPolynomial.X 1 :
      MvPolynomial (Fin 2) K) ∈ shearContraction (1 : Fin 2)
      (shearExp (1 : Fin 2) D)
      (Ideal.span {(MvPolynomial.X 0 - MvPolynomial.X 1 :
        MvPolynomial (Fin 2) K)}) := by
    rw [← triShear_recipe_span_sub_gen]
    exact carriedGen_mem_recipe D
  obtain ⟨hdeg, hcoeff, hstrong⟩ := carriedGen_strongMonic (K := K) D hD
  have hne0 : (MvPolynomial.X 0 + MvPolynomial.X 1 ^ D - MvPolynomial.X 1 :
      MvPolynomial (Fin 2) K) ≠ 0 :=
    MvPolynomial.ne_zero_iff.mpr
      ⟨Finsupp.single 1 D, by rw [hcoeff]; exact one_ne_zero⟩
  have hD0 : D ≠ 0 := by omega
  refine ⟨⟨_, hmem, hne0, D, hD0, hdeg, hcoeff⟩, ?_⟩
  exact delVarQuot_isIntegral_of_strongMonic (1 : Fin 2) _ _ hmem D hD0 hdeg
    hcoeff hstrong

/-! ## (xv) Base-`D` weight injectivity on bounded supports.

For `1 < D`, the recipe weight is injective on exponent vectors whose
coordinates are all `< D`: the weight is `Nat.ofDigits D` of an explicit
digit list (position `0` for `j`, position `i.val + 1` for `i ≠ j`, `0` at
the skipped position `j.val + 1`), and Mathlib's `injOn_ofDigits` gives
injectivity. Hence for every nonzero `g`, choosing `D` above all support
coordinates yields a unique maximal-weight support element. -/

/-- Digit function: `j` reads position `0`, `i ≠ j` reads `i.val + 1`, the
skipped position `j.val + 1` reads `0`. -/
def weightDigit {m : ℕ} (j : Fin m) (a : Fin m →₀ ℕ) (p : ℕ) : ℕ :=
  if p = 0 then a j
  else if h : p - 1 < m then (if ⟨p - 1, h⟩ = j then 0 else a ⟨p - 1, h⟩)
  else 0

/-- The digit list of `a` (length `m + 1`). -/
def weightDigits {m : ℕ} (j : Fin m) (a : Fin m →₀ ℕ) : List ℕ :=
  (List.range (m + 1)).map (weightDigit j a)

/-- Position `0` reads `a j`. -/
theorem weightDigit_zero {m : ℕ} (j : Fin m) (a : Fin m →₀ ℕ) :
    weightDigit j a 0 = a j := by
  unfold weightDigit
  rw [ite_eq_left rfl]

/-- Position `q + 1` reads `a` at `⟨q, _⟩` (or `0` at the skipped index). -/
theorem weightDigit_succ {m : ℕ} (j : Fin m) (a : Fin m →₀ ℕ) (q : ℕ)
    (hq : q < m) :
    weightDigit j a (q + 1) =
      if (⟨q, hq⟩ : Fin m) = j then 0 else a ⟨q, hq⟩ := by
  unfold weightDigit
  rw [ite_eq_right (by omega : q + 1 ≠ 0), dite_eq_left (by omega : q + 1 - 1 < m)]
  have hq1 : q + 1 - 1 = q := by omega
  have hFin : ∀ h : q + 1 - 1 < m, (⟨q + 1 - 1, h⟩ : Fin m) = ⟨q, hq⟩ :=
    fun h => Fin.ext (by change q + 1 - 1 = q; exact hq1)
  rw [hFin]

/-- Every digit is `< D` when all coordinates are. -/
theorem weightDigit_lt {m : ℕ} (j : Fin m) (D : ℕ)
    (a : Fin m →₀ ℕ) (ha : ∀ i, a i < D) (p : ℕ) :
    weightDigit j a p < D := by
  have hj : a j < D := ha j
  unfold weightDigit
  by_cases h0 : p = 0
  · rw [ite_eq_left h0]; exact hj
  · rw [ite_eq_right h0]
    by_cases h1 : p - 1 < m
    · rw [dite_eq_left h1]
      by_cases h2 : (⟨p - 1, h1⟩ : Fin m) = j
      · rw [ite_eq_left h2]; omega
      · rw [ite_eq_right h2]; exact ha _
    · rw [dite_eq_right h1]; omega

/-- The digit list has length `m + 1`. -/
theorem weightDigits_length {m : ℕ} (j : Fin m) (a : Fin m →₀ ℕ) :
    (weightDigits j a).length = m + 1 := by
  simp [weightDigits]

/-- Every digit-list entry is `< D` when all coordinates are. -/
theorem weightDigits_mem_lt {m : ℕ} (j : Fin m) (D : ℕ)
    (a : Fin m →₀ ℕ) (ha : ∀ i, a i < D) (x : ℕ) (hx : x ∈ weightDigits j a) :
    x < D := by
  rw [weightDigits, List.mem_map] at hx
  obtain ⟨p, -, rfl⟩ := hx
  exact weightDigit_lt j D a ha p

/-- `ofDigits` of a mapped `range` is the weighted sum (cons induction). -/
theorem ofDigits_map_range (D n : ℕ) (f : ℕ → ℕ) :
    Nat.ofDigits D ((List.range n).map f) =
      ∑ p ∈ Finset.range n, f p * D ^ p := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.map_append, List.map_singleton,
      Nat.ofDigits_append, ih, Finset.sum_range_succ]
    simp only [List.length_map, List.length_range, Nat.ofDigits_singleton]
    ring

/-- The recipe weight is `ofDigits` of the digit list. -/
theorem weight_eq_ofDigits {m : ℕ} (j : Fin m) (D : ℕ)
    (a : Fin m →₀ ℕ) :
    shearWeight j (shearExp j D) a = Nat.ofDigits D (weightDigits j a) := by
  have hz : weightDigit j a 0 * D ^ (0 : ℕ) = a j := by
    rw [weightDigit_zero, pow_zero, mul_one]
  have hsum : (∑ p ∈ Finset.range m, weightDigit j a (p + 1) * D ^ (p + 1)) =
      ∑ i ∈ Finset.univ.erase j, a i * D ^ (i.val + 1) := by
    have step1 : (∑ p ∈ Finset.range m, weightDigit j a (p + 1) * D ^ (p + 1)) =
        ∑ i : Fin m, (if i = j then (0 : ℕ) else a i) * D ^ (i.val + 1) := by
      rw [← Fin.sum_univ_eq_sum_range]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      show weightDigit j a (i.val + 1) * D ^ (i.val + 1) = _
      rw [weightDigit_succ j a i.val i.isLt]
    have step2 : (∑ i : Fin m, (if i = j then (0 : ℕ) else a i) * D ^ (i.val + 1)) =
        ∑ i ∈ Finset.univ.erase j, a i * D ^ (i.val + 1) := by
      have h := Finset.add_sum_erase Finset.univ
        (fun i => (if i = j then (0 : ℕ) else a i) * D ^ (i.val + 1))
        (Finset.mem_univ j)
      rw [ite_eq_left rfl] at h
      simp only [zero_mul, zero_add] at h
      rw [← h]
      refine Finset.sum_congr rfl (fun i hi => ?_)
      rw [ite_eq_right (Finset.ne_of_mem_erase hi)]
    rw [step1, step2]
  have hw : shearWeight j (shearExp j D) a =
      a j + ∑ i ∈ Finset.univ.erase j, a i * D ^ (i.val + 1) := by
    change (∑ i ∈ Finset.univ, a i * (if i = j then 1 else shearExp j D i)) = _
    have h := Finset.add_sum_erase Finset.univ
      (fun i => a i * (if i = j then 1 else shearExp j D i))
      (Finset.mem_univ j)
    rw [← h]
    have hjj : a j * (if j = j then 1 else shearExp j D j) = a j := by
      rw [ite_eq_left rfl, mul_one]
    rw [hjj]
    congr 1
    refine Finset.sum_congr rfl (fun i hi => ?_)
    rw [ite_eq_right (Finset.ne_of_mem_erase hi)]
    congr 1
    show shearExp j D i = D ^ (i.val + 1)
    unfold shearExp
    rw [ite_eq_right (Finset.ne_of_mem_erase hi)]
  rw [weightDigits, ofDigits_map_range D (m + 1), Finset.sum_range_succ', hw,
    hsum, hz]
  exact add_comm _ _

/-- From equal mapped lists, the mapping functions agree on members
(list induction; avoids index-lemma hunting). -/
theorem map_eq_of_mem {α β : Type*} (f g : α → β) (l : List α)
    (h : l.map f = l.map g) (x : α) (hx : x ∈ l) : f x = g x := by
  induction l with
  | nil => simp at hx
  | cons y ys ih =>
    simp only [List.map_cons] at h
    rw [List.mem_cons] at hx
    rcases hx with rfl | hmem
    · have hc := congrArg List.head? h
      simp only [List.head?_cons] at hc
      exact Option.some_inj.mp hc
    · exact ih (congrArg List.tail h) hmem

/-- The recipe weight is injective on `D`-bounded exponent vectors. -/
theorem weight_injective_of_bounded {m : ℕ} (j : Fin m) (D : ℕ) (hD : 1 < D)
    (a b : Fin m →₀ ℕ) (ha : ∀ i, a i < D) (hb : ∀ i, b i < D)
    (h : shearWeight j (shearExp j D) a = shearWeight j (shearExp j D) b) :
    a = b := by
  have e1 := weight_eq_ofDigits j D a
  have e2 := weight_eq_ofDigits j D b
  have hL : weightDigits j a = weightDigits j b := by
    apply Nat.injOn_ofDigits hD (m + 1)
    · exact ⟨weightDigits_length j a,
        fun x hx => weightDigits_mem_lt j D a ha x hx⟩
    · exact ⟨weightDigits_length j b,
        fun x hx => weightDigits_mem_lt j D b hb x hx⟩
    · rw [← e1, ← e2]; exact h
  have hdigit : ∀ p, p < m + 1 → weightDigit j a p = weightDigit j b p := by
    intro p hp
    have hmem : p ∈ List.range (m + 1) := List.mem_range.mpr hp
    have hmaps : (List.range (m + 1)).map (weightDigit j a) =
        (List.range (m + 1)).map (weightDigit j b) := hL
    exact map_eq_of_mem _ _ _ hmaps p hmem
  apply Finsupp.ext
  intro i
  by_cases hij : i = j
  · subst hij
    have h0 := hdigit 0 (by omega : 0 < m + 1)
    rwa [weightDigit_zero, weightDigit_zero] at h0
  · have hlt : i.val + 1 < m + 1 := by
      have his := i.isLt; omega
    have hdig := hdigit (i.val + 1) hlt
    rw [weightDigit_succ j a i.val i.isLt,
      weightDigit_succ j b i.val i.isLt] at hdig
    rw [ite_eq_right (fun hcon => hij hcon), ite_eq_right (fun hcon => hij hcon)] at hdig
    exact hdig

/-- `D`-choice: some `D > 1` bounds all support coordinates. -/
theorem shearExp_bounded {m : ℕ} {K : Type*} [Field K] (_j : Fin m)
    (g : MvPolynomial (Fin m) K) :
    ∃ D : ℕ, 1 < D ∧ ∀ a ∈ g.support, ∀ i, a i < D := by
  refine ⟨g.support.sup (fun a => a.support.sup fun i => a i) + 2, by omega, ?_⟩
  intro a ha i
  have h2 : a.support.sup (fun i => a i) ≤
      g.support.sup (fun a => a.support.sup fun i => a i) :=
    Finset.le_sup (f := fun a => a.support.sup fun i => a i) ha
  have h1 : a i ≤ a.support.sup (fun i => a i) := by
    by_cases hi : a i = 0
    · rw [hi]; exact Nat.zero_le _
    · exact Finset.le_sup (Finsupp.mem_support_iff.mpr hi)
  omega

/-! ## (xvi) General production infrastructure: weight split, monomial
exactness, unique top.

The recipe weight splits off the fixed variable; each sheared monomial has
`j`-degree exactly its weight (via `degreeOf_prod_eq` — no support-expansion
needed for the degree); a unique maximal-weight support element pins the
sheared polynomial's `j`-degree (via `degreeOf_add_eq_of_degreeOf_lt`). With
(xv)'s D-choice plus injectivity this is general production, degree half. -/

/-- Recipe weight split: the fixed variable contributes its own exponent, the
rest is the off-`j` power sum. -/
theorem shearWeight_recipe_eq {m : ℕ} (j : Fin m) (D : ℕ) (e : Fin m →₀ ℕ) :
    shearWeight j (shearExp j D) e =
      e j + ∑ i ∈ Finset.univ.erase j, e i * D ^ (i.val + 1) := by
  have hsplit : ∑ i ∈ Finset.univ, e i * (if i = j then 1 else shearExp j D i) =
      e j * (if j = j then (1 : ℕ) else shearExp j D j) +
        ∑ i ∈ Finset.univ.erase j,
          e i * (if i = j then 1 else shearExp j D i) :=
    (Finset.add_sum_erase _ _ (Finset.mem_univ j)).symm
  simp only [shearWeight]
  rw [hsplit]
  congr 1
  · rw [ite_eq_left rfl, mul_one]
  · apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mem_erase] at hi
    rw [ite_eq_right hi.1]
    simp only [shearExp, ite_eq_right hi.1]

/-- Off-`j` shear generators are nonzero (the two summands live at distinct
exponent vectors). -/
theorem shearGen_ne_zero {m : ℕ} {K : Type*} [Field K] (j : Fin m)
    (d : Fin m → ℕ) (i : Fin m) (hij : i ≠ j) :
    (MvPolynomial.X i + MvPolynomial.X j ^ d i :
      MvPolynomial (Fin m) K) ≠ 0 := by
  have hne : Finsupp.single j (d i) ≠ Finsupp.single i 1 := by
    intro hcon
    have h2 := congrArg (fun a : Fin m →₀ ℕ => a i) hcon
    rw [Finsupp.single_eq_of_ne hij, Finsupp.single_eq_same] at h2
    exact zero_ne_one h2
  have e1 : (MvPolynomial.X i : MvPolynomial (Fin m) K).coeff
      (Finsupp.single i 1) = 1 :=
    MvPolynomial.coeff_X_same _
  have e2 : (MvPolynomial.X j ^ d i : MvPolynomial (Fin m) K).coeff
      (Finsupp.single i 1) = 0 := by
    rw [MvPolynomial.coeff_X_pow, ite_eq_right hne]
  have hsum : (MvPolynomial.X i + MvPolynomial.X j ^ d i :
      MvPolynomial (Fin m) K).coeff (Finsupp.single i 1) = 1 := by
    rw [AddMonoidAlgebra.coeff_add, Finsupp.add_apply, e1, e2, add_zero]
  exact MvPolynomial.ne_zero_iff.mpr ⟨_, by rw [hsum]; exact one_ne_zero⟩

/-- Expansion first step: the sheared monomial is the scalar times the product
of the sheared generators (`aeval_monomial`). -/
theorem shearFwd_monomial_eq_prod {m : ℕ} {K : Type*} [Field K] (j : Fin m)
    (d : Fin m → ℕ) (e : Fin m →₀ ℕ) (c : K) :
    shearFwd (K := K) j d (MvPolynomial.monomial e c) =
      algebraMap K (MvPolynomial (Fin m) K) c *
        ∏ i ∈ e.support, (if i = j then MvPolynomial.X j
          else MvPolynomial.X i + MvPolynomial.X j ^ d i) ^ (e i) := by
  simp only [shearFwd, MvPolynomial.aeval_monomial, Finsupp.prod]

/-- Power degree: in a domain, `degreeOf` of a power is the multiple. -/
theorem degreeOf_pow_eq_of_ne {m : ℕ} {K : Type*} [Field K] (i : Fin m)
    (g : MvPolynomial (Fin m) K) (hg : g ≠ 0) (k : ℕ) :
    (g ^ k).degreeOf i = k * g.degreeOf i := by
  induction k with
  | zero => rw [pow_zero, MvPolynomial.degreeOf_one, Nat.zero_mul]
  | succ n ih =>
    rw [pow_succ, MvPolynomial.degreeOf_mul_eq (pow_ne_zero n hg) hg, ih,
      add_mul, one_mul]

/-- Monomial exactness: the sheared monomial has `j`-degree exactly its shear
weight (needs only `c ≠ 0`; no support-expansion, via `degreeOf_prod_eq`). -/
theorem shear_monomial_degreeOf_eq {m : ℕ} {K : Type*} [Field K] (j : Fin m)
    (d : Fin m → ℕ) (e : Fin m →₀ ℕ) (c : K) (hc : c ≠ 0) :
    (shearFwd (K := K) j d (MvPolynomial.monomial e c)).degreeOf j =
      shearWeight j d e := by
  rw [shearFwd_monomial_eq_prod, MvPolynomial.algebraMap_eq]
  have hC : (MvPolynomial.C c : MvPolynomial (Fin m) K) ≠ 0 :=
    MvPolynomial.C_ne_zero.mpr hc
  have hfac : ∀ i ∈ e.support,
      ((if i = j then MvPolynomial.X j
        else MvPolynomial.X i + MvPolynomial.X j ^ d i) ^ (e i) :
        MvPolynomial (Fin m) K) ≠ 0 := by
    intro i _
    apply pow_ne_zero
    by_cases hij : i = j
    · subst hij
      rw [ite_eq_left rfl]
      exact MvPolynomial.ne_zero_iff.mpr
        ⟨Finsupp.single i 1, by
          rw [MvPolynomial.coeff_X_same]; exact one_ne_zero⟩
    · rw [ite_eq_right hij]
      exact shearGen_ne_zero j d i hij
  have hprod : (∏ i ∈ e.support, ((if i = j then MvPolynomial.X j
      else MvPolynomial.X i + MvPolynomial.X j ^ d i) ^ (e i) :
      MvPolynomial (Fin m) K)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr hfac
  rw [MvPolynomial.degreeOf_mul_eq hC hprod, MvPolynomial.degreeOf_C, zero_add,
    MvPolynomial.degreeOf_prod_eq _ _ hfac]
  have hterm : ∀ i ∈ e.support, ((((if i = j then MvPolynomial.X j
      else MvPolynomial.X i + MvPolynomial.X j ^ d i) ^ (e i) :
      MvPolynomial (Fin m) K)).degreeOf j) = e i * (if i = j then 1 else d i) := by
    intro i _
    by_cases hij : i = j
    · subst hij
      have hX : (MvPolynomial.X i : MvPolynomial (Fin m) K) ≠ 0 :=
        MvPolynomial.ne_zero_iff.mpr
          ⟨Finsupp.single i 1, by
            rw [MvPolynomial.coeff_X_same]; exact one_ne_zero⟩
      rw [ite_eq_left rfl, degreeOf_pow_eq_of_ne _ _ hX _,
        MvPolynomial.degreeOf_X_self, mul_one, ite_eq_left rfl, mul_one]
    · rw [ite_eq_right hij,
        degreeOf_pow_eq_of_ne _ _ (shearGen_ne_zero j d i hij) _,
        shearFwd_generator_degreeOf_eq (K := K) j d i hij, ite_eq_right hij]
  rw [Finset.sum_congr rfl (fun i hi => hterm i hi)]
  simp only [shearWeight]
  apply Finset.sum_subset (Finset.subset_univ _)
  intro i _ hi
  have hei : e i = 0 := by
    by_contra h0
    exact hi (Finsupp.mem_support_iff.mpr h0)
  rw [hei, zero_mul]

/-- Sum degree from a unique strict maximizer (binary exactness under the sum,
via `degreeOf_add_eq_of_degreeOf_lt`). -/
theorem degreeOf_sum_unique_max {m : ℕ} {K : Type*} [Field K] {ι : Type*}
    [DecidableEq ι] (i : Fin m) (s : Finset ι)
    (f : ι → MvPolynomial (Fin m) K) (a₀ : ι)
    (hmem : a₀ ∈ s)
    (hmax : ∀ a ∈ s.erase a₀, (f a).degreeOf i < (f a₀).degreeOf i) :
    (∑ a ∈ s, f a).degreeOf i = (f a₀).degreeOf i := by
  rw [← Finset.add_sum_erase _ _ hmem]
  by_cases hempty : s.erase a₀ = ∅
  · rw [hempty, Finset.sum_empty, add_zero]
  · have hne : (s.erase a₀).Nonempty := Finset.nonempty_iff_ne_empty.mpr hempty
    obtain ⟨a₁, ha₁⟩ := hne
    have hpos : 0 < (f a₀).degreeOf i :=
      lt_of_le_of_lt (Nat.zero_le _) (hmax a₁ ha₁)
    have hsup : (s.erase a₀).sup (fun a => (f a).degreeOf i) <
        (f a₀).degreeOf i := by
      rw [Finset.sup_lt_iff (show (⊥ : ℕ) < (f a₀).degreeOf i from hpos)]
      exact fun a ha => hmax a ha
    have hle := MvPolynomial.degreeOf_sum_le i (s.erase a₀) f
    exact MvPolynomial.degreeOf_add_eq_of_degreeOf_lt (lt_of_le_of_lt hle hsup)

/-- Polynomial exactness from a unique top: the sheared polynomial's `j`-degree
is the maximal support weight. -/
theorem shear_poly_degreeOf_eq_of_unique_top {m : ℕ} {K : Type*} [Field K]
    (j : Fin m) (d : Fin m → ℕ) (g : MvPolynomial (Fin m) K) (a₀ : Fin m →₀ ℕ)
    (hmem : a₀ ∈ g.support)
    (hmax : ∀ a ∈ g.support.erase a₀, shearWeight j d a < shearWeight j d a₀) :
    (shearFwd (K := K) j d g).degreeOf j = shearWeight j d a₀ := by
  have hf : g = ∑ e ∈ g.support, MvPolynomial.monomial e (g.coeff e) :=
    MvPolynomial.as_sum g
  conv_lhs => rw [hf, map_sum]
  have htop : (shearFwd (K := K) j d
      (MvPolynomial.monomial a₀ (g.coeff a₀))).degreeOf j =
      shearWeight j d a₀ :=
    shear_monomial_degreeOf_eq _ _ _ _
      (MvPolynomial.mem_support_iff.mp hmem)
  rw [← htop]
  refine degreeOf_sum_unique_max j g.support
    (fun e => shearFwd (K := K) j d (MvPolynomial.monomial e (g.coeff e))) a₀
    hmem ?_
  intro a ha
  have hamem : a ∈ g.support := Finset.mem_of_mem_erase ha
  change (shearFwd (K := K) j d
    (MvPolynomial.monomial a (g.coeff a))).degreeOf j <
    (shearFwd (K := K) j d (MvPolynomial.monomial a₀ (g.coeff a₀))).degreeOf j
  rw [shear_monomial_degreeOf_eq _ _ _ _
    (MvPolynomial.mem_support_iff.mp hamem), htop]
  exact hmax a ha

/-- Unique-top extraction: at large `D` the weights separate (xv), so a
nonzero polynomial has a strict maximal-weight support element. -/
theorem exists_maxWeight_of_bound {m : ℕ} {K : Type*} [Field K] (j : Fin m)
    (g : MvPolynomial (Fin m) K) (D : ℕ) (hD : 1 < D) (hne : g ≠ 0)
    (hb : ∀ a ∈ g.support, ∀ i : Fin m, a i < D) :
    ∃ a₀, a₀ ∈ g.support ∧
      ∀ a ∈ g.support.erase a₀, shearWeight j (shearExp j D) a <
        shearWeight j (shearExp j D) a₀ := by
  have hsup_ne : g.support.Nonempty := by
    obtain ⟨d, hd⟩ := MvPolynomial.ne_zero_iff.mp hne
    exact ⟨d, MvPolynomial.mem_support_iff.mpr hd⟩
  obtain ⟨a₀, ha₀, hle⟩ := Finset.exists_max_image g.support
    (fun a => shearWeight j (shearExp j D) a) hsup_ne
  refine ⟨a₀, ha₀, fun a ha => ?_⟩
  have hamem : a ∈ g.support := Finset.mem_of_mem_erase ha
  have hne' : a ≠ a₀ := Finset.ne_of_mem_erase ha
  have hle' := hle a hamem
  have hne'' : shearWeight j (shearExp j D) a ≠
      shearWeight j (shearExp j D) a₀ := by
    intro hcon
    exact hne' (weight_injective_of_bounded j D hD a a₀
      (fun i => hb a hamem i) (fun i => hb a₀ ha₀ i) hcon)
  exact lt_of_le_of_ne hle' hne''

/-- General production, degree half: at large `D` the sheared nonzero
polynomial has `j`-degree exactly the maximal support weight. -/
theorem shear_poly_degreeOf_eq_of_bound {m : ℕ} {K : Type*} [Field K] (j : Fin m)
    (g : MvPolynomial (Fin m) K) (D : ℕ) (hD : 1 < D) (hne : g ≠ 0)
    (hb : ∀ a ∈ g.support, ∀ i : Fin m, a i < D) :
    ∃ a₀, a₀ ∈ g.support ∧
      (∀ a ∈ g.support.erase a₀, shearWeight j (shearExp j D) a <
        shearWeight j (shearExp j D) a₀) ∧
      (shearFwd (K := K) j (shearExp j D) g).degreeOf j =
        shearWeight j (shearExp j D) a₀ := by
  obtain ⟨a₀, ha₀, hmax⟩ := exists_maxWeight_of_bound j g D hD hne hb
  exact ⟨a₀, ha₀, hmax,
    shear_poly_degreeOf_eq_of_unique_top j (shearExp j D) g a₀ ha₀ hmax⟩

/-- General production, packaged: for nonzero `g`, some `D > 1` makes the
sheared `j`-degree exactly the maximal support weight. -/
theorem shear_production_degree {m : ℕ} {K : Type*} [Field K] (j : Fin m)
    (g : MvPolynomial (Fin m) K) (hne : g ≠ 0) :
    ∃ D : ℕ, 1 < D ∧ ∃ a₀, a₀ ∈ g.support ∧
      (∀ a ∈ g.support.erase a₀, shearWeight j (shearExp j D) a <
        shearWeight j (shearExp j D) a₀) ∧
      (shearFwd (K := K) j (shearExp j D) g).degreeOf j =
        shearWeight j (shearExp j D) a₀ := by
  obtain ⟨D, hD, hb⟩ := shearExp_bounded j g
  exact ⟨D, hD, shear_poly_degreeOf_eq_of_bound j g D hD hne hb⟩

/-! ## (xvii) Support expansion of sheared monomials.

Each off-`j` generator power expands by the binomial theorem, and the product
over the off-`j` indices expands as a product-of-sums over choice functions
(`Finset.prod_sum`). This is the expansion half of general production;
isolating the top term's coefficient from the expansion (hence the strong-monic
upgrade for general `g`) is the documented remainder. -/

/-- Single-factor expansion: an off-`j` generator power expands by the binomial
theorem, in the summand shape feeding `Finset.prod_sum`. -/
theorem shearGen_pow_eq_sum {m : ℕ} {K : Type*} [Field K] (j : Fin m)
    (d : Fin m → ℕ) (i : Fin m) (_hij : i ≠ j) (k : ℕ) :
    (MvPolynomial.X i + MvPolynomial.X j ^ d i :
      MvPolynomial (Fin m) K) ^ k =
      ∑ t ∈ Finset.range (k + 1),
        MvPolynomial.X i ^ t * (MvPolynomial.X j ^ d i) ^ (k - t) *
          (((k.choose t : ℕ)) : MvPolynomial (Fin m) K) :=
  add_pow _ _ _

/-- Support expansion of sheared monomials: product-of-sums over choice
functions (`Finset.prod_sum`), after the binomial expansion of each off-`j`
factor. -/
theorem shearFwd_monomial_expand {m : ℕ} {K : Type*} [Field K] (j : Fin m)
    (d : Fin m → ℕ) (e : Fin m →₀ ℕ) (c : K) :
    shearFwd (K := K) j d (MvPolynomial.monomial e c) =
      algebraMap K (MvPolynomial (Fin m) K) c * MvPolynomial.X j ^ (e j) *
        ∑ κ ∈ (Finset.univ.erase j).pi (fun i => Finset.range (e i + 1)),
          ∏ x ∈ (Finset.univ.erase j).attach,
            (MvPolynomial.X x.1 ^ (κ x.1 x.2) *
              (MvPolynomial.X j ^ d x.1) ^ (e x.1 - κ x.1 x.2) *
              ((((e x.1).choose (κ x.1 x.2) : ℕ)) :
                MvPolynomial (Fin m) K)) := by
  have huniv : (∏ i ∈ e.support, (if i = j then MvPolynomial.X j
      else MvPolynomial.X i + MvPolynomial.X j ^ d i) ^ (e i) :
      MvPolynomial (Fin m) K) =
      MvPolynomial.X j ^ (e j) *
        ∏ i ∈ Finset.univ.erase j, (if i = j then MvPolynomial.X j
          else MvPolynomial.X i + MvPolynomial.X j ^ d i) ^ (e i) := by
    have hsub : (∏ i ∈ e.support, (if i = j then MvPolynomial.X j
        else MvPolynomial.X i + MvPolynomial.X j ^ d i) ^ (e i) :
        MvPolynomial (Fin m) K) =
        ∏ i ∈ Finset.univ, (if i = j then MvPolynomial.X j
          else MvPolynomial.X i + MvPolynomial.X j ^ d i) ^ (e i) := by
      apply Finset.prod_subset (Finset.subset_univ _)
      intro i _ hi
      have hei : e i = 0 := by
        by_contra h0
        exact hi (Finsupp.mem_support_iff.mpr h0)
      rw [hei, pow_zero]
    rw [hsub, ← Finset.mul_prod_erase _ _ (Finset.mem_univ j), ite_eq_left rfl]
  rw [shearFwd_monomial_eq_prod, huniv, mul_assoc]
  have hfac : ∀ i ∈ Finset.univ.erase j,
      ((if i = j then MvPolynomial.X j
        else MvPolynomial.X i + MvPolynomial.X j ^ d i) ^ (e i) :
        MvPolynomial (Fin m) K) =
      ∑ t ∈ Finset.range (e i + 1),
        (MvPolynomial.X i ^ t * (MvPolynomial.X j ^ d i) ^ (e i - t) *
          ((((e i).choose t : ℕ)) : MvPolynomial (Fin m) K)) := by
    intro i hi
    have hij : i ≠ j := (Finset.mem_erase.mp hi).1
    rw [ite_eq_right hij]
    exact shearGen_pow_eq_sum j d i hij (e i)
  have hprod : (∏ i ∈ Finset.univ.erase j, ((if i = j then MvPolynomial.X j
      else MvPolynomial.X i + MvPolynomial.X j ^ d i) ^ (e i) :
      MvPolynomial (Fin m) K)) =
      ∑ κ ∈ (Finset.univ.erase j).pi (fun i => Finset.range (e i + 1)),
        ∏ x ∈ (Finset.univ.erase j).attach,
          (MvPolynomial.X x.1 ^ (κ x.1 x.2) *
            (MvPolynomial.X j ^ d x.1) ^ (e x.1 - κ x.1 x.2) *
            ((((e x.1).choose (κ x.1 x.2) : ℕ)) :
              MvPolynomial (Fin m) K)) :=
    Eq.trans (Finset.prod_congr rfl hfac) (Finset.prod_sum _ _ _)
  rw [hprod]

/-! ## (xx) Top-choice evaluation and choice degree bounds.

First half of top-coefficient isolation (remainder item 1): each binomial
factor at choice `0` collapses to the pure `Xⱼ`-power
(`shear_factor_top_eq`); the product of top factors is the pure power at
the off-`j` weight sum (`shear_top_prod_eq`, via `prod_pow_eq_pow_sum` —
no support-expansion needed); and every choice product has `j`-degree at
most the off-`j` weight sum (`shear_choice_degreeOf_le`, via
`degreeOf_prod_le` plus per-factor `≤`-bounds — no nonzeroness hypotheses,
so positive-characteristic vanishing of binomial coefficients is
harmless). Assembling the top coefficient across the sum (hence the
strong-monic upgrade) is the remaining half. -/

/-- Top factor: at choice `0` the binomial factor collapses to the pure
`Xⱼ`-power (the summand shape feeding the top-term assembly). -/
theorem shear_factor_top_eq {m : ℕ} {K : Type*} [Field K] (j : Fin m)
    (d : Fin m → ℕ) (e : Fin m →₀ ℕ) (i : Fin m) :
    (MvPolynomial.X i ^ (0 : ℕ) * (MvPolynomial.X j ^ d i) ^ (e i - 0) *
      ((((e i).choose 0 : ℕ)) : MvPolynomial (Fin m) K)) =
      (MvPolynomial.X j ^ d i) ^ (e i) := by
  rw [pow_zero, Nat.sub_zero, Nat.choose_zero_right, Nat.cast_one, mul_one,
    one_mul]

/-- Top product: the product of top factors is the pure `Xⱼ`-power at the
off-`j` weight sum (stated over `attach`, matching the expansion). -/
theorem shear_top_prod_eq {m : ℕ} {K : Type*} [Field K] (j : Fin m)
    (d : Fin m → ℕ) (e : Fin m →₀ ℕ) :
    ∏ x ∈ (Finset.univ.erase j).attach,
        (MvPolynomial.X j ^ d x.1 : MvPolynomial (Fin m) K) ^ (e x.1) =
      MvPolynomial.X j ^
        (∑ x ∈ (Finset.univ.erase j).attach, d x.1 * e x.1) := by
  calc ∏ x ∈ (Finset.univ.erase j).attach,
          (MvPolynomial.X j ^ d x.1 : MvPolynomial (Fin m) K) ^ (e x.1)
      = ∏ x ∈ (Finset.univ.erase j).attach,
          MvPolynomial.X j ^ (d x.1 * e x.1) :=
        Finset.prod_congr rfl (fun x _ => (pow_mul _ _ _).symm)
    _ = MvPolynomial.X j ^
          (∑ x ∈ (Finset.univ.erase j).attach, d x.1 * e x.1) :=
        Finset.prod_pow_eq_pow_sum _ _ _

/-- Per-factor degree bound: one binomial factor has `j`-degree at most
`d i * e i` (the `Xᵢ`-part vanishes off `j`; `≤`-only, uniform in the
choice index `t`). -/
theorem shear_factor_degreeOf_le {m : ℕ} {K : Type*} [Field K] (j : Fin m)
    (d : Fin m → ℕ) (e : Fin m →₀ ℕ) (i : Fin m) (hij : i ≠ j) (t : ℕ) :
    (MvPolynomial.X i ^ t * (MvPolynomial.X j ^ d i) ^ (e i - t) *
      ((((e i).choose t : ℕ)) : MvPolynomial (Fin m) K)).degreeOf j ≤
      d i * e i := by
  have hX : (MvPolynomial.X i ^ t :
      MvPolynomial (Fin m) K).degreeOf j = 0 :=
    MvPolynomial.degreeOf_X_pow_of_ne _ (Ne.symm hij)
  have hdX : (MvPolynomial.X j ^ d i :
      MvPolynomial (Fin m) K).degreeOf j ≤ d i := by
    calc _ ≤ d i * (MvPolynomial.X j :
        MvPolynomial (Fin m) K).degreeOf j :=
          MvPolynomial.degreeOf_pow_le _ _ _
      _ = d i := by rw [MvPolynomial.degreeOf_X_self, mul_one]
  have hmid : ((MvPolynomial.X j ^ d i) ^ (e i - t) :
      MvPolynomial (Fin m) K).degreeOf j ≤ d i * (e i - t) := by
    calc _ ≤ (e i - t) * (MvPolynomial.X j ^ d i :
        MvPolynomial (Fin m) K).degreeOf j :=
          MvPolynomial.degreeOf_pow_le _ _ _
      _ ≤ (e i - t) * d i := Nat.mul_le_mul_left _ hdX
      _ = d i * (e i - t) := Nat.mul_comm _ _
  have hC : (((((e i).choose t : ℕ)) :
      MvPolynomial (Fin m) K)).degreeOf j = 0 := by
    rw [← map_natCast (MvPolynomial.C (R := K)), MvPolynomial.degreeOf_C]
  calc (MvPolynomial.X i ^ t * (MvPolynomial.X j ^ d i) ^ (e i - t) *
        (((((e i).choose t : ℕ)) :
          MvPolynomial (Fin m) K))).degreeOf j
      ≤ (MvPolynomial.X i ^ t * (MvPolynomial.X j ^ d i) ^ (e i - t) :
          MvPolynomial (Fin m) K).degreeOf j +
          (((((e i).choose t : ℕ)) :
            MvPolynomial (Fin m) K)).degreeOf j :=
        MvPolynomial.degreeOf_mul_le _ _ _
    _ ≤ ((MvPolynomial.X i ^ t :
          MvPolynomial (Fin m) K).degreeOf j +
          (((MvPolynomial.X j ^ d i) ^ (e i - t) :
            MvPolynomial (Fin m) K).degreeOf j)) +
          (((((e i).choose t : ℕ)) :
            MvPolynomial (Fin m) K)).degreeOf j :=
        Nat.add_le_add_right (MvPolynomial.degreeOf_mul_le _ _ _) _
    _ ≤ d i * e i := by
        rw [hX, hC, zero_add, add_zero]
        calc ((MvPolynomial.X j ^ d i) ^ (e i - t) :
            MvPolynomial (Fin m) K).degreeOf j
            ≤ d i * (e i - t) := hmid
          _ ≤ d i * e i := Nat.mul_le_mul_left _ (Nat.sub_le _ _)

/-- Choice degree bound: every choice product has `j`-degree at most the
off-`j` weight sum (uniform in the choice; `≤`-only, so no nonzeroness and
no characteristic hypothesis). -/
theorem shear_choice_degreeOf_le {m : ℕ} {K : Type*} [Field K] (j : Fin m)
    (d : Fin m → ℕ) (e : Fin m →₀ ℕ)
    (κ : ∀ (i : Fin m), i ∈ Finset.univ.erase j → ℕ) :
    (∏ x ∈ (Finset.univ.erase j).attach,
      (MvPolynomial.X x.1 ^ (κ x.1 x.2) *
        (MvPolynomial.X j ^ d x.1) ^ (e x.1 - κ x.1 x.2) *
        ((((e x.1).choose (κ x.1 x.2) : ℕ)) :
          MvPolynomial (Fin m) K))).degreeOf j ≤
      ∑ x ∈ (Finset.univ.erase j).attach, d x.1 * e x.1 := by
  have hfac_le : ∀ x ∈ (Finset.univ.erase j).attach,
      (MvPolynomial.X x.1 ^ (κ x.1 x.2) *
        (MvPolynomial.X j ^ d x.1) ^ (e x.1 - κ x.1 x.2) *
        ((((e x.1).choose (κ x.1 x.2) : ℕ)) :
          MvPolynomial (Fin m) K)).degreeOf j ≤ d x.1 * e x.1 :=
    fun x _ => shear_factor_degreeOf_le j d e x.1
      ((Finset.mem_erase.mp x.2).1) (κ x.1 x.2)
  have key : ∀ (F : ↥(Finset.univ.erase j) → MvPolynomial (Fin m) K),
      (∀ x ∈ (Finset.univ.erase j).attach, (F x).degreeOf j ≤ d x.1 * e x.1) →
      (∏ x ∈ (Finset.univ.erase j).attach, F x).degreeOf j ≤
        ∑ x ∈ (Finset.univ.erase j).attach, d x.1 * e x.1 := by
    intro F hF
    calc (∏ x ∈ (Finset.univ.erase j).attach, F x).degreeOf j
        ≤ ∑ x ∈ (Finset.univ.erase j).attach, (F x).degreeOf j :=
          MvPolynomial.degreeOf_prod_le _ _ _
      _ ≤ ∑ x ∈ (Finset.univ.erase j).attach, d x.1 * e x.1 :=
          Finset.sum_le_sum (fun x hx => hF x hx)
  exact key _ hfac_le

/-! ## (xviii) Going-down induction architecture: transport, length gain,
conditional exhibit.

The shear contraction of a prime is prime; prime chains transport along the
shear automorphism (same length, contraction to `P`); a chain ending strictly
below a prime snocs one rung longer ending at it (the length-gain rung
`(m - 1 - s) → (m - s)`); together they assemble the exhibit from any
below-contraction chain. Producing that below-contraction chain (delete-`j` IH
base chain plus the going-down lift with `LiesOver`) is the documented
remainder. -/

/-- The shear contraction of a prime is prime (comap along the inverse shear). -/
theorem shearContraction_isPrime {m : ℕ} {K : Type*} [Field K] (j : Fin m)
    (d : Fin m → ℕ) (P : Ideal (MvPolynomial (Fin m) K)) [P.IsPrime] :
    (shearContraction j d P).IsPrime := by
  unfold shearContraction
  infer_instance

/-- The shear prime map: transport of primes along the shear automorphism. -/
noncomputable def shearPrime {m : ℕ} {K : Type*} [Field K] (j : Fin m)
    (d : Fin m → ℕ) : PrimeSpectrum (MvPolynomial (Fin m) K) →
      PrimeSpectrum (MvPolynomial (Fin m) K) :=
  fun p => ⟨p.asIdeal.comap (triShear (K := K) j d).toRingHom, inferInstance⟩

/-- The shear prime map is strictly monotone (comap along a surjective map). -/
theorem shearPrime_strictMono {m : ℕ} {K : Type*} [Field K] (j : Fin m)
    (d : Fin m → ℕ) : StrictMono (shearPrime (K := K) j d) := by
  intro a b hab
  have habI : a.asIdeal < b.asIdeal := hab
  have hsurj : Function.Surjective (triShear (K := K) j d).toRingHom := by
    intro y
    exact ⟨(triShear (K := K) j d).symm y,
      (triShear (K := K) j d).apply_symm_apply y⟩
  have h := RingHom.strictMono_comap_of_surjective hsurj habI
  exact h

/-- The shear prime map sends the contraction back to `P` (the transport proves
exactly where the exhibit must end). -/
theorem shearPrime_contraction {m : ℕ} {K : Type*} [Field K] (j : Fin m)
    (d : Fin m → ℕ) (P : Ideal (MvPolynomial (Fin m) K)) [P.IsPrime] :
    shearPrime (K := K) j d
        ⟨shearContraction j d P, shearContraction_isPrime j d P⟩ =
      ⟨P, ‹P.IsPrime›⟩ := by
  apply PrimeSpectrum.ext
  change Ideal.comap (triShear (K := K) j d).toRingHom (shearContraction j d P) = P
  have hcon : shearContraction j d P =
      P.comap (triShear (K := K) j d).symm.toAlgHom.toRingHom := rfl
  have hcomp : (triShear (K := K) j d).symm.toAlgHom.toRingHom.comp
      (triShear (K := K) j d).toRingHom = RingHom.id _ :=
    RingHom.ext fun x => (triShear (K := K) j d).symm_apply_apply x
  rw [hcon, Ideal.comap_comap, hcomp, Ideal.comap_id]

/-- Chain transport along the shear: a chain ending at the contraction maps to
the same-length chain ending at `P` (the exhibit transport). -/
theorem chain_transport_shear {m : ℕ} {K : Type*} [Field K] (j : Fin m)
    (d : Fin m → ℕ) (P : Ideal (MvPolynomial (Fin m) K)) [P.IsPrime]
    (L : LTSeries (PrimeSpectrum (MvPolynomial (Fin m) K)))
    (hL : L.last.asIdeal = shearContraction j d P) :
    ∃ L' : LTSeries (PrimeSpectrum (MvPolynomial (Fin m) K)),
      L'.length = L.length ∧ L'.last = ⟨P, ‹P.IsPrime›⟩ := by
  refine ⟨L.map (shearPrime (K := K) j d) (shearPrime_strictMono j d), rfl, ?_⟩
  rw [LTSeries.last_map]
  have hFlast : shearPrime (K := K) j d L.last = ⟨P, ‹P.IsPrime›⟩ := by
    have hbund : L.last =
        ⟨shearContraction j d P, shearContraction_isPrime j d P⟩ :=
      PrimeSpectrum.ext hL
    rw [hbund]
    exact shearPrime_contraction j d P
  rw [hFlast]

/-- Length-gain rung: a chain of length `m - 1 - s` ending strictly below `Q`
snocs to length `m - s` ending at `Q` (pure order theory; the model content —
producing the below-`Q` prime via going-down — is the documented remainder). -/
theorem exhibit_length_gain {R : Type*} [CommRing R]
    (L : LTSeries (PrimeSpectrum R)) (Q : PrimeSpectrum R) (h : L.last < Q)
    (m s : ℕ) (hs : s < m) (hlen : L.length = m - 1 - s) :
    ∃ L' : LTSeries (PrimeSpectrum R),
      L'.length = m - s ∧ L'.last.asIdeal = Q.asIdeal := by
  refine ⟨L.snoc Q h, ?_, ?_⟩
  · have hlen' : (L.snoc Q h).length = L.length + 1 := by
      simp only [RelSeries.snoc, RelSeries.append_length, RelSeries.singleton,
        add_zero]
    rw [hlen', hlen]
    omega
  · simp

/-- Conditional exhibit assembly: a length-`(m - 1 - s)` chain ending strictly
below the contraction snocs onto the contraction (length gain) and transports
along the shear to `P`. The below-contraction chain (going-down lift of the
delete-`j` IH base chain) is the hypothesis; producing it is the remainder. -/
theorem exhibit_of_shear_chain {m : ℕ} {K : Type*} [Field K] [Infinite K]
    (P : Ideal (MvPolynomial (Fin m) K)) [P.IsPrime]
    (s : ℕ) (hs : s < m) (j : Fin m) (D : ℕ)
    (L : LTSeries (PrimeSpectrum (MvPolynomial (Fin m) K)))
    (hlen : L.length = m - 1 - s)
    (hlt : L.last < ⟨shearContraction j (shearExp j D) P,
      shearContraction_isPrime j (shearExp j D) P⟩) :
    ∃ l : LTSeries (PrimeSpectrum (MvPolynomial (Fin m) K)),
      l.length = m - s ∧ l.last = ⟨P, ‹P.IsPrime›⟩ := by
  obtain ⟨L₁, hlen₁, hlast₁⟩ := exhibit_length_gain L
    ⟨shearContraction j (shearExp j D) P,
      shearContraction_isPrime j (shearExp j D) P⟩
    hlt m s hs hlen
  obtain ⟨L₂, hlen₂, hlast₂⟩ :=
    chain_transport_shear j (shearExp j D) P L₁ hlast₁
  refine ⟨L₂, ?_, hlast₂⟩
  omega

/-! ## (xix) Strong-monic assembly and closing `hheight`.

A strong-monic element of the contraction discharges both `fiberPredWeak`
conjuncts at once (monic witness plus the integrality lifting), reducing
general production to finding strong-monic `f`. The recipe-fed datum then
feeds `height_of_dpow_datum` — the exact shape consumed by
`hheight_of_production`. -/

/-- Strong-monic assembly: a strong-monic element of the contraction discharges
both `fiberPredWeak` conjuncts at once (monic witness plus integrality
lifting). -/
theorem fiberPredWeak_of_strongMonic {m : ℕ} {K : Type*} [Field K]
    (P : Ideal (MvPolynomial (Fin m) K)) [P.IsPrime]
    (j : Fin m) (d : Fin m → ℕ)
    (f : MvPolynomial (Fin m) K) (hf : f ∈ shearContraction j d P)
    (hne0 : f ≠ 0) (e : ℕ) (he : e ≠ 0)
    (hdeg : f.degreeOf j = e) (hcoeff : f.coeff (Finsupp.single j e) = 1)
    (hstrong : ∀ a ∈ f.support, a ≠ Finsupp.single j e → a j < e) :
    fiberPredWeak m K P j d := by
  intro _
  exact ⟨⟨f, hf, hne0, e, he, hdeg, hcoeff⟩,
    delVarQuot_isIntegral_of_strongMonic j _ f hf e he hdeg hcoeff hstrong⟩

/-- Closing `hheight` from production: recipe-fed datum (fiber from general
production, exhibit from the going-down induction) feeds
`height_of_dpow_datum` — the exact shape consumed by
`hheight_uncond`. -/
theorem hheight_of_production (m s : ℕ) (K : Type*) [Field K] [Infinite K]
    (P : Ideal (MvPolynomial (Fin m) K)) [P.IsPrime]
    (s_le : s ≤ m)
    (normap : MvPolynomial (Fin s) K →ₐ[K] MvPolynomial (Fin m) K ⧸ P)
    (normap_inj : Function.Injective normap)
    (normap_int : normap.IsIntegral)
    (bad : Finset (Fin m → K))
    (dir : (Fin m → K) →ₗ[K] K)
    (dir_ne : ∀ v ∈ bad, dir v ≠ 0)
    (j : Fin m) (D : ℕ) (hD : D ≠ 0)
    (fiber : fiberPredWeak m K P j (shearExp j D))
    (exhibit : ∃ l : LTSeries (PrimeSpectrum (MvPolynomial (Fin m) K)),
      l.length = m - s ∧ l.last = ⟨P, ‹P.IsPrime›⟩) :
    (((m - s : ℕ)) : WithBot ℕ∞) ≤ (P.height : WithBot ℕ∞) :=
  height_of_dpow_datum m s K P
    (datum_of_dpow_recipe m s K P s_le normap normap_inj normap_int bad dir dir_ne
      j D hD fiber exhibit)

/-! ## (xxi) Strict top isolation for the recipe.

Second half of top-coefficient isolation (remainder item 1): the top choice
(`κ = 0` everywhere, `shearTopChoice`) carries the full off-`j` weight
(`shear_choice_top_eq`, via the proved `shear_factor_top_eq`), while every
non-top choice has `j`-degree strictly below the off-`j` weight sum
(`shear_nontop_degree_lt` — this is where `d i ≠ 0` off `j` is spent, true at
the recipe for `D ≠ 0`). With the weight equation in attach form
(`shearWeight_attach_eq`, via the `sum_attach_erase` bridge) this splits each
sheared monomial into its top scalar term plus a strictly lower-`j`-degree
remainder (`shear_monomial_top_decomp`) — the strong-monic upgrade input. -/

/-- The top choice function: `0` at every off-`j` index. -/
def shearTopChoice {m : ℕ} (j : Fin m) : ∀ i ∈ Finset.univ.erase j, ℕ :=
  fun _ _ => 0

/-- The top choice lies in every choice set. -/
theorem shearTopChoice_mem {m : ℕ} (j : Fin m) (e : Fin m →₀ ℕ) :
    shearTopChoice j ∈
      (Finset.univ.erase j).pi (fun i => Finset.range (e i + 1)) := by
  rw [Finset.mem_pi]
  intro a _
  change (0 : ℕ) ∈ Finset.range (e a + 1)
  exact Finset.mem_range.mpr (Nat.succ_pos _)

/-- Recipe exponent at an off-`j` index. -/
theorem shearExp_of_mem {m : ℕ} (j : Fin m) (D : ℕ) (i : Fin m)
    (hi : i ∈ Finset.univ.erase j) : shearExp j D i = D ^ (i.val + 1) := by
  have hne : i ≠ j := (Finset.mem_erase.mp hi).1
  simp only [shearExp, hne, ite_false]

/-- Recipe positivity off `j` (for `1 < D`). -/
theorem shearExp_pos_of_mem {m : ℕ} (j : Fin m) (D : ℕ) (hD : 1 < D)
    (i : Fin m) (hi : i ∈ Finset.univ.erase j) :
    1 ≤ shearExp j D i := by
  rw [shearExp_of_mem j D i hi]
  have hpos := pow_pos (by omega : 0 < D) (i.val + 1)
  omega

/-- Attach/erase sum bridge. -/
theorem sum_attach_erase {m : ℕ} (j : Fin m) (f : Fin m → ℕ) :
    (∑ x ∈ (Finset.univ.erase j).attach, f x.1) =
      ∑ i ∈ Finset.univ.erase j, f i :=
  Finset.sum_attach _ _

/-- Recipe weight in attach form. -/
theorem shearWeight_attach_eq {m : ℕ} {K : Type*} [Field K] (j : Fin m) (D : ℕ)
    (e : Fin m →₀ ℕ) :
    shearWeight j (shearExp j D) e =
      e j + ∑ x ∈ (Finset.univ.erase j).attach,
        (shearExp j D) x.1 * e x.1 := by
  have hbase := shearWeight_recipe_eq j D e
  have hconv : (∑ i ∈ Finset.univ.erase j, e i * D ^ (i.val + 1)) =
      ∑ x ∈ (Finset.univ.erase j).attach,
        (shearExp j D) x.1 * e x.1 := by
    have h1 : (∑ i ∈ Finset.univ.erase j, e i * D ^ (i.val + 1)) =
        ∑ i ∈ Finset.univ.erase j, e i * shearExp j D i :=
      Finset.sum_congr rfl (fun i hi => by
        show e i * D ^ (i.val + 1) = e i * shearExp j D i
        rw [shearExp_of_mem j D i hi])
    have h2 : (∑ i ∈ Finset.univ.erase j, e i * shearExp j D i) =
        ∑ x ∈ (Finset.univ.erase j).attach,
          (shearExp j D) x.1 * e x.1 := by
      have h := sum_attach_erase j (fun i => e i * shearExp j D i)
      rw [show (∑ x ∈ (Finset.univ.erase j).attach,
          (fun i => e i * shearExp j D i) x.1) =
          (∑ x ∈ (Finset.univ.erase j).attach,
            (shearExp j D) x.1 * e x.1) from
          Finset.sum_congr rfl (fun x _ => Nat.mul_comm _ _)] at h
      rw [show (∑ i ∈ Finset.univ.erase j,
          (fun i => e i * shearExp j D i) i) =
          (∑ i ∈ Finset.univ.erase j, e i * shearExp j D i) from
          Finset.sum_congr rfl (fun i _ => rfl)] at h
      exact h.symm
    rw [h1]
    exact h2
  rw [hbase, hconv]

/-- Top choice product identity (general shear exponents): at `κ = 0`
everywhere each factor collapses to the pure `Xⱼ`-power. -/
theorem shear_choice_top_eq {m : ℕ} {K : Type*} [Field K] (j : Fin m)
    (d : Fin m → ℕ) (e : Fin m →₀ ℕ) :
    ∏ x ∈ (Finset.univ.erase j).attach,
      (MvPolynomial.X x.1 ^ (shearTopChoice j x.1 x.2) *
        (MvPolynomial.X j ^ d x.1) ^ (e x.1 - shearTopChoice j x.1 x.2) *
        ((((e x.1).choose (shearTopChoice j x.1 x.2) : ℕ)) :
          MvPolynomial (Fin m) K)) =
      ∏ x ∈ (Finset.univ.erase j).attach,
        (MvPolynomial.X j ^ d x.1 : MvPolynomial (Fin m) K) ^ (e x.1) := by
  refine Finset.prod_congr rfl (fun x _ =>
    shear_factor_top_eq j d e x.1)

/-- Tight per-factor degree bound (for the strict drop at a nonzero choice):
the factor has `j`-degree at most `d i * (e i - t)`. -/
theorem shear_factor_degreeOf_tight {m : ℕ} {K : Type*} [Field K] (j : Fin m)
    (d : Fin m → ℕ) (e : Fin m →₀ ℕ) (i : Fin m) (hij : i ≠ j) (t : ℕ) :
    (MvPolynomial.X i ^ t * (MvPolynomial.X j ^ d i) ^ (e i - t) *
      ((((e i).choose t : ℕ)) : MvPolynomial (Fin m) K)).degreeOf j ≤
      d i * (e i - t) := by
  have hX : (MvPolynomial.X i ^ t :
      MvPolynomial (Fin m) K).degreeOf j = 0 :=
    MvPolynomial.degreeOf_X_pow_of_ne _ (Ne.symm hij)
  have hdX : (MvPolynomial.X j ^ d i :
      MvPolynomial (Fin m) K).degreeOf j ≤ d i := by
    calc _ ≤ d i * (MvPolynomial.X j :
        MvPolynomial (Fin m) K).degreeOf j :=
          MvPolynomial.degreeOf_pow_le _ _ _
      _ = d i := by rw [MvPolynomial.degreeOf_X_self, mul_one]
  have hmid : ((MvPolynomial.X j ^ d i) ^ (e i - t) :
      MvPolynomial (Fin m) K).degreeOf j ≤ d i * (e i - t) := by
    calc _ ≤ (e i - t) * (MvPolynomial.X j ^ d i :
          MvPolynomial (Fin m) K).degreeOf j :=
        MvPolynomial.degreeOf_pow_le _ _ _
      _ ≤ (e i - t) * d i := Nat.mul_le_mul_left _ hdX
      _ = d i * (e i - t) := Nat.mul_comm _ _
  have hC : (((((e i).choose t : ℕ)) :
      MvPolynomial (Fin m) K)).degreeOf j = 0 := by
    rw [← map_natCast (MvPolynomial.C (R := K)), MvPolynomial.degreeOf_C]
  calc (MvPolynomial.X i ^ t * (MvPolynomial.X j ^ d i) ^ (e i - t) *
        (((((e i).choose t : ℕ)) :
          MvPolynomial (Fin m) K))).degreeOf j
      ≤ (MvPolynomial.X i ^ t * (MvPolynomial.X j ^ d i) ^ (e i - t) :
          MvPolynomial (Fin m) K).degreeOf j +
          (((((e i).choose t : ℕ)) :
            MvPolynomial (Fin m) K)).degreeOf j :=
        MvPolynomial.degreeOf_mul_le _ _ _
    _ ≤ ((MvPolynomial.X i ^ t :
            MvPolynomial (Fin m) K).degreeOf j +
            (((MvPolynomial.X j ^ d i) ^ (e i - t) :
              MvPolynomial (Fin m) K).degreeOf j)) +
            (((((e i).choose t : ℕ)) :
              MvPolynomial (Fin m) K)).degreeOf j :=
        Nat.add_le_add_right (MvPolynomial.degreeOf_mul_le _ _ _) _
    _ ≤ d i * (e i - t) := by
        rw [hX, hC, zero_add, add_zero]
        exact hmid

/-- Strict degree bound for non-top choices at the recipe: a choice that is
nonzero somewhere has `j`-degree strictly below the off-`j` weight sum (the
nonzero choice drops at least one `d i ≥ 1` worth of `Xⱼ`-degree). -/
theorem shear_nontop_degree_lt {m : ℕ} {K : Type*} [Field K] (j : Fin m)
    (D : ℕ) (hD : 1 < D) (e : Fin m →₀ ℕ)
    (κ : ∀ i ∈ Finset.univ.erase j, ℕ)
    (hmem : κ ∈ (Finset.univ.erase j).pi (fun i => Finset.range (e i + 1)))
    (hne : κ ≠ shearTopChoice j) :
    (∏ x ∈ (Finset.univ.erase j).attach,
      (MvPolynomial.X x.1 ^ (κ x.1 x.2) *
        (MvPolynomial.X j ^ (shearExp j D) x.1) ^ (e x.1 - κ x.1 x.2) *
        ((((e x.1).choose (κ x.1 x.2) : ℕ)) :
          MvPolynomial (Fin m) K))).degreeOf j <
      ∑ x ∈ (Finset.univ.erase j).attach,
        (shearExp j D) x.1 * e x.1 := by
  have hwit : ∃ i hi, κ i hi ≠ 0 := by
    by_contra hcon
    have hall : ∀ i hi, κ i hi = 0 :=
      fun i hi => by_contra fun h => hcon ⟨i, hi, h⟩
    exact hne (funext fun i => funext fun hi => hall i hi)
  obtain ⟨i₀, hi₀, h0⟩ := hwit
  have hkle : κ i₀ hi₀ ≤ e i₀ := by
    have hmem' : κ i₀ hi₀ ∈ Finset.range (e i₀ + 1) :=
      Finset.mem_pi.mp hmem i₀ hi₀
    exact Nat.le_of_lt_succ (Finset.mem_range.mp hmem')
  have hfac : ∀ x ∈ (Finset.univ.erase j).attach,
      (MvPolynomial.X x.1 ^ (κ x.1 x.2) *
        (MvPolynomial.X j ^ (shearExp j D) x.1) ^ (e x.1 - κ x.1 x.2) *
        ((((e x.1).choose (κ x.1 x.2) : ℕ)) :
          MvPolynomial (Fin m) K)).degreeOf j ≤
        (shearExp j D) x.1 * (e x.1 - κ x.1 x.2) := by
    intro x _
    exact shear_factor_degreeOf_tight j _ e x.1
      ((Finset.mem_erase.mp x.2).1) _
  have key : ∀ (F : ↥(Finset.univ.erase j) → MvPolynomial (Fin m) K),
      (∀ x ∈ (Finset.univ.erase j).attach,
        (F x).degreeOf j ≤
          (shearExp j D) x.1 * (e x.1 - κ x.1 x.2)) →
      (∏ x ∈ (Finset.univ.erase j).attach, F x).degreeOf j ≤
        ∑ x ∈ (Finset.univ.erase j).attach,
          (shearExp j D) x.1 * (e x.1 - κ x.1 x.2) := by
    intro F hF
    calc (∏ x ∈ (Finset.univ.erase j).attach, F x).degreeOf j
        ≤ ∑ x ∈ (Finset.univ.erase j).attach, (F x).degreeOf j := by
          apply MvPolynomial.degreeOf_prod_le
      _ ≤ ∑ x ∈ (Finset.univ.erase j).attach,
            (shearExp j D) x.1 * (e x.1 - κ x.1 x.2) := by
          exact Finset.sum_le_sum (fun x hx => hF x hx)
  have hT : (∏ x ∈ (Finset.univ.erase j).attach,
      (MvPolynomial.X x.1 ^ (κ x.1 x.2) *
        (MvPolynomial.X j ^ (shearExp j D) x.1) ^ (e x.1 - κ x.1 x.2) *
        ((((e x.1).choose (κ x.1 x.2) : ℕ)) :
          MvPolynomial (Fin m) K))).degreeOf j ≤
      ∑ x ∈ (Finset.univ.erase j).attach,
        (shearExp j D) x.1 * (e x.1 - κ x.1 x.2) :=
    key _ hfac
  have hle_all : ∀ x ∈ (Finset.univ.erase j).attach,
      (shearExp j D) x.1 * (e x.1 - κ x.1 x.2) ≤
        (shearExp j D) x.1 * e x.1 := by
    intro x _
    exact Nat.mul_le_mul_left _ (Nat.sub_le _ _)
  have hlt_wit : ∃ x ∈ (Finset.univ.erase j).attach,
      (shearExp j D) x.1 * (e x.1 - κ x.1 x.2) <
        (shearExp j D) x.1 * e x.1 := by
    refine ⟨⟨i₀, hi₀⟩, Finset.mem_attach _ _, ?_⟩
    change (shearExp j D) i₀ * (e i₀ - κ i₀ hi₀) <
      (shearExp j D) i₀ * e i₀
    have hsplit : (shearExp j D) i₀ * (e i₀ - κ i₀ hi₀) +
        (shearExp j D) i₀ * κ i₀ hi₀ = (shearExp j D) i₀ * e i₀ := by
      rw [← mul_add, Nat.sub_add_cancel hkle]
    have hdκ : 1 ≤ (shearExp j D) i₀ * κ i₀ hi₀ :=
      Nat.pos_of_ne_zero
        (mul_ne_zero (by have := shearExp_pos_of_mem j D hD i₀ hi₀; omega) h0)
    omega
  have hstrict : (∑ x ∈ (Finset.univ.erase j).attach,
        (shearExp j D) x.1 * (e x.1 - κ x.1 x.2)) <
      ∑ x ∈ (Finset.univ.erase j).attach,
        (shearExp j D) x.1 * e x.1 :=
    Finset.sum_lt_sum hle_all hlt_wit
  exact lt_of_le_of_lt hT hstrict

/-! ## (xxii) Monomial decomposition and general fiber production.

The top/non-top split of each sheared monomial
(`shear_monomial_top_decomp`): the top choice contributes the scalar top term
`C c * Xⱼ ^ W`, everything else has `j`-degree below `W`. Summing over the
support, the maximal-weight element survives alone at the top; scaling by the
inverse top coefficient yields a strong-monic element of the contraction
(`shear_strongMonic_of_mem`), and `fiberPredWeak_of_strongMonic` closes
`fiber` for general `P` — at a given recipe choice (`fiber_of_production_at`)
and hence for some choice from prime data alone (`fiber_of_production`). -/

/-- Weight of the zero exponent vector. -/
theorem shearWeight_zero {m : ℕ} (j : Fin m) (d : Fin m → ℕ) :
    shearWeight j d 0 = 0 := by
  unfold shearWeight
  refine Finset.sum_eq_zero (fun i _ => ?_)
  simp

/-- Monomial top decomposition at the recipe: the sheared monomial is its top
scalar term plus a strictly lower-`j`-degree remainder. -/
theorem shear_monomial_top_decomp {m : ℕ} {K : Type*} [Field K] (j : Fin m)
    (D : ℕ) (hD : 1 < D) (e : Fin m →₀ ℕ) (c : K) (he : e ≠ 0) :
    ∃ R : MvPolynomial (Fin m) K,
      shearFwd (K := K) j (shearExp j D) (MvPolynomial.monomial e c) =
        MvPolynomial.C c * MvPolynomial.X j ^ (shearWeight j (shearExp j D) e) +
          R ∧
      R.degreeOf j < shearWeight j (shearExp j D) e := by
  have hκmem : shearTopChoice j ∈
      (Finset.univ.erase j).pi (fun i => Finset.range (e i + 1)) :=
    shearTopChoice_mem j e
  have hW := shearWeight_attach_eq (K := K) j D e
  have hS : (∏ x ∈ (Finset.univ.erase j).attach,
        (MvPolynomial.X x.1 ^ (shearTopChoice j x.1 x.2) *
          (MvPolynomial.X j ^ (shearExp j D) x.1) ^
            (e x.1 - shearTopChoice j x.1 x.2) *
          ((((e x.1).choose (shearTopChoice j x.1 x.2) : ℕ)) :
            MvPolynomial (Fin m) K))) +
        (∑ κ ∈ ((Finset.univ.erase j).pi
          (fun i => Finset.range (e i + 1))).erase (shearTopChoice j),
          ∏ x ∈ (Finset.univ.erase j).attach,
            (MvPolynomial.X x.1 ^ (κ x.1 x.2) *
              (MvPolynomial.X j ^ (shearExp j D) x.1) ^ (e x.1 - κ x.1 x.2) *
              ((((e x.1).choose (κ x.1 x.2) : ℕ)) :
                MvPolynomial (Fin m) K))) =
        ∑ κ ∈ (Finset.univ.erase j).pi (fun i => Finset.range (e i + 1)),
          ∏ x ∈ (Finset.univ.erase j).attach,
            (MvPolynomial.X x.1 ^ (κ x.1 x.2) *
              (MvPolynomial.X j ^ (shearExp j D) x.1) ^ (e x.1 - κ x.1 x.2) *
              ((((e x.1).choose (κ x.1 x.2) : ℕ)) :
                MvPolynomial (Fin m) K)) :=
    Finset.add_sum_erase ((Finset.univ.erase j).pi
      (fun i => Finset.range (e i + 1))) (fun κ => ∏ x ∈ (Finset.univ.erase j).attach,
        (MvPolynomial.X x.1 ^ (κ x.1 x.2) *
          (MvPolynomial.X j ^ (shearExp j D) x.1) ^ (e x.1 - κ x.1 x.2) *
          ((((e x.1).choose (κ x.1 x.2) : ℕ)) :
            MvPolynomial (Fin m) K))) hκmem
  have htop : algebraMap K (MvPolynomial (Fin m) K) c *
        MvPolynomial.X j ^ (e j) *
        (∏ x ∈ (Finset.univ.erase j).attach,
          (MvPolynomial.X x.1 ^ (shearTopChoice j x.1 x.2) *
            (MvPolynomial.X j ^ (shearExp j D) x.1) ^
              (e x.1 - shearTopChoice j x.1 x.2) *
            ((((e x.1).choose (shearTopChoice j x.1 x.2) : ℕ)) :
              MvPolynomial (Fin m) K))) =
      MvPolynomial.C c *
        MvPolynomial.X j ^ (shearWeight j (shearExp j D) e) := by
    rw [shear_choice_top_eq, shear_top_prod_eq, mul_assoc, ← pow_add,
      MvPolynomial.algebraMap_eq, hW]
  refine ⟨algebraMap K (MvPolynomial (Fin m) K) c *
    MvPolynomial.X j ^ (e j) *
    (∑ κ ∈ ((Finset.univ.erase j).pi
      (fun i => Finset.range (e i + 1))).erase (shearTopChoice j),
      ∏ x ∈ (Finset.univ.erase j).attach,
        (MvPolynomial.X x.1 ^ (κ x.1 x.2) *
          (MvPolynomial.X j ^ (shearExp j D) x.1) ^ (e x.1 - κ x.1 x.2) *
          ((((e x.1).choose (κ x.1 x.2) : ℕ)) :
            MvPolynomial (Fin m) K))), ?_, ?_⟩
  · rw [shearFwd_monomial_expand, ← hS, mul_add, htop]
  · have hA : (algebraMap K (MvPolynomial (Fin m) K) c *
        MvPolynomial.X j ^ (e j)).degreeOf j ≤ e j := by
      calc (algebraMap K (MvPolynomial (Fin m) K) c *
            MvPolynomial.X j ^ (e j)).degreeOf j
          ≤ (algebraMap K (MvPolynomial (Fin m) K) c).degreeOf j +
            (MvPolynomial.X j ^ (e j)).degreeOf j :=
            MvPolynomial.degreeOf_mul_le _ _ _
        _ = e j := by
            rw [MvPolynomial.algebraMap_eq, MvPolynomial.degreeOf_C,
              MvPolynomial.degreeOf_X_self_pow, zero_add]
    by_cases hzw : (∑ x ∈ (Finset.univ.erase j).attach,
        (shearExp j D) x.1 * e x.1) = 0
    · have hei_all : ∀ i ∈ Finset.univ.erase j, e i = 0 := by
        intro i hi
        have hle : (shearExp j D) i * e i ≤
            ∑ x ∈ (Finset.univ.erase j).attach,
              (shearExp j D) x.1 * e x.1 := by
          have hadd : (shearExp j D) i * e i +
              ∑ x ∈ (Finset.univ.erase j).attach.erase ⟨i, hi⟩,
                (shearExp j D) x.1 * e x.1 =
              ∑ x ∈ (Finset.univ.erase j).attach,
                (shearExp j D) x.1 * e x.1 :=
            Finset.add_sum_erase _
              (fun x : ↥(Finset.univ.erase j) =>
                (shearExp j D) x.1 * e x.1)
              (Finset.mem_attach _ ⟨i, hi⟩)
          omega
        have h0 : (shearExp j D) i * e i = 0 := by omega
        rcases mul_eq_zero.mp h0 with hd0 | he0
        · exfalso
          have hpos := shearExp_pos_of_mem j D hD i hi
          omega
        · exact he0
      have herase : ((Finset.univ.erase j).pi
          (fun i => Finset.range (e i + 1))).erase (shearTopChoice j) = ∅ := by
        rw [Finset.eq_empty_iff_forall_notMem]
        intro κ hcon
        rw [Finset.mem_erase] at hcon
        have hκeq : κ = shearTopChoice j :=
          funext fun i => funext fun hi => by
            have hmemκ : κ i hi ∈ Finset.range (e i + 1) :=
              Finset.mem_pi.mp hcon.2 i hi
            have hκ0 : κ i hi = 0 := by
              have hlt := Finset.mem_range.mp hmemκ
              rw [hei_all i hi] at hlt
              omega
            exact hκ0
        exact hcon.1 hκeq
      have hR0 : (algebraMap K (MvPolynomial (Fin m) K) c *
          MvPolynomial.X j ^ (e j) *
          (∑ κ ∈ ((Finset.univ.erase j).pi
            (fun i => Finset.range (e i + 1))).erase (shearTopChoice j),
            ∏ x ∈ (Finset.univ.erase j).attach,
              (MvPolynomial.X x.1 ^ (κ x.1 x.2) *
                (MvPolynomial.X j ^ (shearExp j D) x.1) ^ (e x.1 - κ x.1 x.2) *
                ((((e x.1).choose (κ x.1 x.2) : ℕ)) :
                  MvPolynomial (Fin m) K)))) = 0 := by
        rw [herase, Finset.sum_empty, mul_zero]
      rw [hR0, MvPolynomial.degreeOf_zero]
      have hje : 0 < e j := by
        by_contra hcon
        have hje0 : e j = 0 := by omega
        exact he (Finsupp.ext fun i => by
          by_cases hij : i = j
          · rw [hij]
            simpa using hje0
          · have hi : i ∈ Finset.univ.erase j :=
              Finset.mem_erase.mpr ⟨hij, Finset.mem_univ i⟩
            simpa using hei_all i hi)
      rw [hW]
      omega
    · have hplt : ∀ κ ∈ ((Finset.univ.erase j).pi
          (fun i => Finset.range (e i + 1))).erase (shearTopChoice j),
          (∏ x ∈ (Finset.univ.erase j).attach,
            (MvPolynomial.X x.1 ^ (κ x.1 x.2) *
              (MvPolynomial.X j ^ (shearExp j D) x.1) ^ (e x.1 - κ x.1 x.2) *
              ((((e x.1).choose (κ x.1 x.2) : ℕ)) :
                MvPolynomial (Fin m) K))).degreeOf j <
            ∑ x ∈ (Finset.univ.erase j).attach,
              (shearExp j D) x.1 * e x.1 := by
        intro κ hκ
        exact shear_nontop_degree_lt j D hD e κ
          (Finset.mem_of_mem_erase hκ) (Finset.ne_of_mem_erase hκ)
      have hle : ∀ κ ∈ ((Finset.univ.erase j).pi
          (fun i => Finset.range (e i + 1))).erase (shearTopChoice j),
          (∏ x ∈ (Finset.univ.erase j).attach,
            (MvPolynomial.X x.1 ^ (κ x.1 x.2) *
              (MvPolynomial.X j ^ (shearExp j D) x.1) ^ (e x.1 - κ x.1 x.2) *
              ((((e x.1).choose (κ x.1 x.2) : ℕ)) :
                MvPolynomial (Fin m) K))).degreeOf j ≤
            (∑ x ∈ (Finset.univ.erase j).attach,
              (shearExp j D) x.1 * e x.1) - 1 := by
        intro κ hκ
        have hltκ := hplt κ hκ
        omega
      have hsup := Finset.sup_le hle
      have hsum : (∑ κ ∈ ((Finset.univ.erase j).pi
          (fun i => Finset.range (e i + 1))).erase (shearTopChoice j),
          ∏ x ∈ (Finset.univ.erase j).attach,
            (MvPolynomial.X x.1 ^ (κ x.1 x.2) *
              (MvPolynomial.X j ^ (shearExp j D) x.1) ^ (e x.1 - κ x.1 x.2) *
              ((((e x.1).choose (κ x.1 x.2) : ℕ)) :
                MvPolynomial (Fin m) K))).degreeOf j ≤
          (∑ x ∈ (Finset.univ.erase j).attach,
            (shearExp j D) x.1 * e x.1) - 1 := by
        apply le_trans (MvPolynomial.degreeOf_sum_le _ _ _)
        exact hsup
      have hRle : (algebraMap K (MvPolynomial (Fin m) K) c *
          MvPolynomial.X j ^ (e j) *
          (∑ κ ∈ ((Finset.univ.erase j).pi
            (fun i => Finset.range (e i + 1))).erase (shearTopChoice j),
            ∏ x ∈ (Finset.univ.erase j).attach,
              (MvPolynomial.X x.1 ^ (κ x.1 x.2) *
                (MvPolynomial.X j ^ (shearExp j D) x.1) ^ (e x.1 - κ x.1 x.2) *
                ((((e x.1).choose (κ x.1 x.2) : ℕ)) :
                  MvPolynomial (Fin m) K)))).degreeOf j ≤
          e j + ((∑ x ∈ (Finset.univ.erase j).attach,
            (shearExp j D) x.1 * e x.1) - 1) :=
        le_trans (MvPolynomial.degreeOf_mul_le _ _ _)
          (Nat.add_le_add hA hsum)
      rw [hW]
      omega

/-- A prime ideal's nonzero element has non-constant support (else it is a
unit, forcing the prime to `⊤`). -/
theorem exists_nonconst_of_prime {m : ℕ} {K : Type*} [Field K]
    (P : Ideal (MvPolynomial (Fin m) K)) [P.IsPrime]
    (g : MvPolynomial (Fin m) K) (hg : g ∈ P) (hgne : g ≠ 0) :
    ∃ a₁ ∈ g.support, a₁ ≠ 0 := by
  by_contra hcon
  have hall : ∀ a ∈ g.support, a = 0 :=
    fun a ha => by_contra fun h => hcon ⟨a, ha, h⟩
  have hsup_ne : g.support.Nonempty := by
    obtain ⟨d, hd⟩ := MvPolynomial.ne_zero_iff.mp hgne
    exact ⟨d, MvPolynomial.mem_support_iff.mpr hd⟩
  obtain ⟨a, ha⟩ := hsup_ne
  have ha0 : a = 0 := hall a ha
  have h0mem : (0 : Fin m →₀ ℕ) ∈ g.support := by
    rw [← ha0]
    exact ha
  have hc0 : g.coeff 0 ≠ 0 := MvPolynomial.mem_support_iff.mp h0mem
  have hm0 : MvPolynomial.monomial (0 : Fin m →₀ ℕ) (g.coeff 0) =
      MvPolynomial.C (g.coeff 0) :=
    congrFun MvPolynomial.monomial_zero' _
  have hC : g = MvPolynomial.C (g.coeff 0) := by
    conv_lhs => rw [MvPolynomial.as_sum g]
    rw [← hm0]
    refine Finset.sum_eq_single 0 ?_ ?_
    · intro e he hne0
      exact absurd (hall e he) hne0
    · intro h0
      exact absurd h0mem h0
  have h1mem : (1 : MvPolynomial (Fin m) K) ∈ P := by
    have hmem : MvPolynomial.C (g.coeff 0) *
        MvPolynomial.C (g.coeff 0)⁻¹ ∈ P := by
      have hgg := hg
      rw [hC] at hgg
      rw [mul_comm]
      exact Ideal.mul_mem_left P _ hgg
    rwa [← map_mul, mul_inv_cancel₀ hc0, map_one] at hmem
  have htop : P = ⊤ := by
    rw [eq_top_iff]
    intro x _
    have hmemx := P.mul_mem_left x h1mem
    rwa [mul_one] at hmemx
  exact (Ideal.IsPrime.ne_top ‹P.IsPrime›) htop

/-- The maximal weight is positive once some support element is non-constant. -/
theorem production_weight_pos {m : ℕ} {K : Type*} [Field K]
    (j : Fin m) (D : ℕ) (hD : 1 < D)
    (a₁ : Fin m →₀ ℕ) (ha₁ne : a₁ ≠ 0)
    (a₀ : Fin m →₀ ℕ)
    (hWle : shearWeight j (shearExp j D) a₁ ≤
      shearWeight j (shearExp j D) a₀) :
    0 < shearWeight j (shearExp j D) a₀ := by
  have hWa1 : 0 < shearWeight j (shearExp j D) a₁ := by
    rw [shearWeight_recipe_eq]
    by_cases hj : a₁ j = 0
    · obtain ⟨i₀, hi₀ne⟩ : ∃ i, a₁ i ≠ 0 := by
        by_contra hcon
        have hall : ∀ i, a₁ i = 0 :=
          fun i => by_contra fun h => hcon ⟨i, h⟩
        exact ha₁ne (Finsupp.ext fun i => by simp [hall i])
      have hi₀j : i₀ ≠ j := by
        intro h
        rw [h] at hi₀ne
        exact hi₀ne hj
      have hmem₀ : i₀ ∈ Finset.univ.erase j :=
        Finset.mem_erase.mpr ⟨hi₀j, Finset.mem_univ i₀⟩
      have hterm : 1 ≤ a₁ i₀ * D ^ (i₀.val + 1) :=
        Nat.pos_of_ne_zero
          (mul_ne_zero hi₀ne (pow_ne_zero _ (by omega)))
      have hadd : a₁ i₀ * D ^ (i₀.val + 1) +
          ∑ i ∈ (Finset.univ.erase j).erase i₀, a₁ i * D ^ (i.val + 1) =
          ∑ i ∈ Finset.univ.erase j, a₁ i * D ^ (i.val + 1) :=
        Finset.add_sum_erase _ (fun i => a₁ i * D ^ (i.val + 1)) hmem₀
      have hle : a₁ i₀ * D ^ (i₀.val + 1) ≤
          ∑ i ∈ Finset.univ.erase j, a₁ i * D ^ (i.val + 1) := by
        omega
      omega
    · have h1 : 1 ≤ a₁ j := by
        have h := Nat.pos_of_ne_zero hj
        omega
      omega
  exact lt_of_lt_of_le hWa1 hWle

/-- Global strong-monic element (scaled): the sheared polynomial normalizes to
a strong-monic element of the contraction. -/
theorem shear_strongMonic_of_mem {m : ℕ} {K : Type*} [Field K]
    (j : Fin m) (D : ℕ) (hD : 1 < D)
    (P : Ideal (MvPolynomial (Fin m) K))
    (g : MvPolynomial (Fin m) K) (hg : g ∈ P)
    (a₀ : Fin m →₀ ℕ) (ha₀ : a₀ ∈ g.support)
    (hmax : ∀ a ∈ g.support.erase a₀,
      shearWeight j (shearExp j D) a < shearWeight j (shearExp j D) a₀)
    (hW : 0 < shearWeight j (shearExp j D) a₀) :
    ∃ f' : MvPolynomial (Fin m) K, f' ∈ shearContraction j (shearExp j D) P ∧
      f' ≠ 0 ∧
      ∃ e : ℕ, e ≠ 0 ∧ f'.degreeOf j = e ∧
        f'.coeff (Finsupp.single j e) = 1 ∧
          ∀ a ∈ f'.support, a ≠ Finsupp.single j e → a j < e := by
  have hWne : shearWeight j (shearExp j D) a₀ ≠ 0 := by omega
  have hc₀ : g.coeff a₀ ≠ 0 := MvPolynomial.mem_support_iff.mp ha₀
  have ha₀ne : a₀ ≠ 0 := by
    intro hz
    rw [hz] at hW
    have hW0 : shearWeight j (shearExp j D) 0 = 0 := shearWeight_zero j _
    rw [hW0] at hW
    omega
  have hdegW : (shearFwd (K := K) j (shearExp j D) g).degreeOf j =
      shearWeight j (shearExp j D) a₀ :=
    shear_poly_degreeOf_eq_of_unique_top j _ g a₀ ha₀ hmax
  obtain ⟨R₀, hR₀eq, hR₀lt⟩ :=
    shear_monomial_top_decomp (K := K) j D hD a₀ (g.coeff a₀) ha₀ne
  have has : g = ∑ e ∈ g.support, MvPolynomial.monomial e (g.coeff e) :=
    MvPolynomial.as_sum g
  have hfsum : shearFwd (K := K) j (shearExp j D) g =
      ∑ e ∈ g.support,
        shearFwd (K := K) j (shearExp j D)
          (MvPolynomial.monomial e (g.coeff e)) := by
    rw [congrArg (shearFwd (K := K) j (shearExp j D)) has, map_sum]
  have hsplit : (∑ e ∈ g.support,
      shearFwd (K := K) j (shearExp j D)
        (MvPolynomial.monomial e (g.coeff e))) =
      shearFwd (K := K) j (shearExp j D)
        (MvPolynomial.monomial a₀ (g.coeff a₀)) +
      ∑ e ∈ g.support.erase a₀,
        shearFwd (K := K) j (shearExp j D)
          (MvPolynomial.monomial e (g.coeff e)) :=
    (Finset.add_sum_erase _ _ ha₀).symm
  have hfeq : shearFwd (K := K) j (shearExp j D) g =
      MvPolynomial.C (g.coeff a₀) *
        MvPolynomial.X j ^ (shearWeight j (shearExp j D) a₀) +
        (R₀ + ∑ e ∈ g.support.erase a₀,
          shearFwd (K := K) j (shearExp j D)
            (MvPolynomial.monomial e (g.coeff e))) := by
    rw [hfsum, hsplit, hR₀eq, add_assoc]
  have hW0 : shearWeight j (shearExp j D) 0 = 0 := shearWeight_zero j _
  have hdeg_erase : ∀ e ∈ g.support.erase a₀,
      (shearFwd (K := K) j (shearExp j D)
        (MvPolynomial.monomial e (g.coeff e))).degreeOf j <
        shearWeight j (shearExp j D) a₀ := by
    intro e he
    have hmem : e ∈ g.support := Finset.mem_of_mem_erase he
    have hc : g.coeff e ≠ 0 := MvPolynomial.mem_support_iff.mp hmem
    by_cases he0 : e = 0
    · subst he0
      have hex := shear_monomial_degreeOf_eq (K := K) j (shearExp j D) 0
        (g.coeff 0) hc
      rw [hex, hW0]
      exact hW
    · have hex := shear_monomial_degreeOf_eq (K := K) j (shearExp j D) e
        (g.coeff e) hc
      rw [hex]
      exact hmax e he
  have hRlt : (R₀ + ∑ e ∈ g.support.erase a₀,
      shearFwd (K := K) j (shearExp j D)
        (MvPolynomial.monomial e (g.coeff e))).degreeOf j <
      shearWeight j (shearExp j D) a₀ := by
    have hsup_le : ((g.support.erase a₀).sup fun e =>
        (shearFwd (K := K) j (shearExp j D)
          (MvPolynomial.monomial e (g.coeff e))).degreeOf j) ≤
        shearWeight j (shearExp j D) a₀ - 1 :=
      Finset.sup_le (fun e he => by have hlt := hdeg_erase e he; omega)
    have hsum_le : (∑ e ∈ g.support.erase a₀,
        shearFwd (K := K) j (shearExp j D)
          (MvPolynomial.monomial e (g.coeff e))).degreeOf j ≤
        shearWeight j (shearExp j D) a₀ - 1 := by
      apply le_trans (MvPolynomial.degreeOf_sum_le _ _ _)
      exact hsup_le
    calc (R₀ + ∑ e ∈ g.support.erase a₀,
          shearFwd (K := K) j (shearExp j D)
            (MvPolynomial.monomial e (g.coeff e))).degreeOf j
        ≤ max (R₀.degreeOf j) ((∑ e ∈ g.support.erase a₀,
          shearFwd (K := K) j (shearExp j D)
            (MvPolynomial.monomial e (g.coeff e))).degreeOf j) :=
          MvPolynomial.degreeOf_add_le _ _ _
      _ < shearWeight j (shearExp j D) a₀ := by omega
  have htopc : (MvPolynomial.C (g.coeff a₀) *
      MvPolynomial.X j ^ (shearWeight j (shearExp j D) a₀)).coeff
      (Finsupp.single j (shearWeight j (shearExp j D) a₀)) = g.coeff a₀ := by
    rw [MvPolynomial.coeff_C_mul, MvPolynomial.coeff_X_pow]
    simp
  have hRcoeff : (R₀ + ∑ e ∈ g.support.erase a₀,
      shearFwd (K := K) j (shearExp j D)
        (MvPolynomial.monomial e (g.coeff e))).coeff
      (Finsupp.single j (shearWeight j (shearExp j D) a₀)) = 0 := by
    by_contra hne
    have hmem : Finsupp.single j (shearWeight j (shearExp j D) a₀) ∈
        (R₀ + ∑ e ∈ g.support.erase a₀,
          shearFwd (K := K) j (shearExp j D)
            (MvPolynomial.monomial e (g.coeff e))).support :=
      MvPolynomial.mem_support_iff.mpr hne
    have hle := MvPolynomial.monomial_le_degreeOf j hmem
    rw [Finsupp.single_eq_same] at hle
    omega
  have hcoeffW : (shearFwd (K := K) j (shearExp j D) g).coeff
      (Finsupp.single j (shearWeight j (shearExp j D) a₀)) = g.coeff a₀ := by
    rw [hfeq, AddMonoidAlgebra.coeff_add, Finsupp.add_apply, htopc, hRcoeff,
      add_zero]
  have hstrong : ∀ a ∈ (shearFwd (K := K) j (shearExp j D) g).support,
      a ≠ Finsupp.single j (shearWeight j (shearExp j D) a₀) →
        a j < shearWeight j (shearExp j D) a₀ := by
    intro a hamem hne
    by_contra hlt
    have hle : shearWeight j (shearExp j D) a₀ ≤ a j := not_lt.mp hlt
    have hRa : (R₀ + ∑ e ∈ g.support.erase a₀,
        shearFwd (K := K) j (shearExp j D)
          (MvPolynomial.monomial e (g.coeff e))).coeff a = 0 := by
      by_contra hneR
      have hmR := MvPolynomial.monomial_le_degreeOf j
        (MvPolynomial.mem_support_iff.mpr hneR)
      omega
    have hTa : (MvPolynomial.C (g.coeff a₀) *
        MvPolynomial.X j ^ (shearWeight j (shearExp j D) a₀)).coeff a = 0 := by
      rw [MvPolynomial.coeff_C_mul, MvPolynomial.coeff_X_pow]
      simp [Ne.symm hne]
    have hfa : (shearFwd (K := K) j (shearExp j D) g).coeff a = 0 := by
      rw [hfeq, AddMonoidAlgebra.coeff_add, Finsupp.add_apply, hTa, hRa,
        add_zero]
    exact (MvPolynomial.mem_support_iff.mp hamem) hfa
  have htri : (triShear (K := K) j (shearExp j D)) g =
      shearFwd (K := K) j (shearExp j D) g := rfl
  have hmem_con : shearFwd (K := K) j (shearExp j D) g ∈
      shearContraction j (shearExp j D) P := by
    rw [← htri]
    change (triShear (K := K) j (shearExp j D)) g ∈ Ideal.comap
      (triShear (K := K) j (shearExp j D)).symm.toAlgHom.toRingHom P
    rw [Ideal.mem_comap]
    have hback : ((triShear (K := K) j (shearExp j D)).symm.toAlgHom.toRingHom)
        ((triShear (K := K) j (shearExp j D)) g) = g :=
      (triShear (K := K) j (shearExp j D)).symm_apply_apply _
    rw [hback]
    exact hg
  refine ⟨MvPolynomial.C (g.coeff a₀)⁻¹ *
    shearFwd (K := K) j (shearExp j D) g,
    Ideal.mul_mem_left _ _ hmem_con, ?_,
    shearWeight j (shearExp j D) a₀, hWne, ?_, ?_, ?_⟩
  · exact mul_ne_zero (MvPolynomial.C_ne_zero.mpr (inv_ne_zero hc₀))
      (MvPolynomial.ne_zero_iff.mpr
        ⟨Finsupp.single j (shearWeight j (shearExp j D) a₀),
          by rw [hcoeffW]; exact hc₀⟩)
  · have hle : (MvPolynomial.C (g.coeff a₀)⁻¹ *
        shearFwd (K := K) j (shearExp j D) g).degreeOf j ≤
        shearWeight j (shearExp j D) a₀ := by
      have h := MvPolynomial.degreeOf_C_mul_le
        (shearFwd (K := K) j (shearExp j D) g) j (g.coeff a₀)⁻¹
      rw [hdegW] at h
      exact h
    have hge : shearWeight j (shearExp j D) a₀ ≤
        (MvPolynomial.C (g.coeff a₀)⁻¹ *
          shearFwd (K := K) j (shearExp j D) g).degreeOf j := by
      have hc1 : (MvPolynomial.C (g.coeff a₀)⁻¹ *
          shearFwd (K := K) j (shearExp j D) g).coeff
          (Finsupp.single j (shearWeight j (shearExp j D) a₀)) = 1 := by
        rw [MvPolynomial.coeff_C_mul, hcoeffW, inv_mul_cancel₀ hc₀]
      have hmem1 := MvPolynomial.mem_support_iff.mpr
        (by rw [hc1]; exact one_ne_zero)
      have hle2 := MvPolynomial.monomial_le_degreeOf j hmem1
      rwa [Finsupp.single_eq_same] at hle2
    exact le_antisymm hle hge
  · rw [MvPolynomial.coeff_C_mul, hcoeffW, inv_mul_cancel₀ hc₀]
  · intro a hamem hne
    have hca : (shearFwd (K := K) j (shearExp j D) g).coeff a ≠ 0 := by
      have h := MvPolynomial.mem_support_iff.mp hamem
      rw [MvPolynomial.coeff_C_mul] at h
      intro hz
      rw [hz, mul_zero] at h
      exact h rfl
    have hmemf : a ∈ (shearFwd (K := K) j (shearExp j D) g).support :=
      MvPolynomial.mem_support_iff.mpr hca
    exact hstrong a hmemf hne

/-- Fiber production at a given recipe choice: a bounding `D` yields
`fiberPredWeak` from a nonzero element of `P`. -/
theorem fiber_of_production_at {m : ℕ} {K : Type*} [Field K]
    (P : Ideal (MvPolynomial (Fin m) K)) [P.IsPrime]
    (j : Fin m) (D : ℕ) (hD : 1 < D)
    (g : MvPolynomial (Fin m) K) (hg : g ∈ P)
    (hgne : g ≠ 0)
    (hb : ∀ a ∈ g.support, ∀ i : Fin m, a i < D) :
    fiberPredWeak m K P j (shearExp j D) := by
  obtain ⟨a₁, ha₁mem, ha₁ne⟩ := exists_nonconst_of_prime P g hg hgne
  obtain ⟨a₀, ha₀, hmax⟩ :=
    exists_maxWeight_of_bound (K := K) j g D hD hgne hb
  have hWle : shearWeight j (shearExp j D) a₁ ≤
      shearWeight j (shearExp j D) a₀ := by
    by_cases heq : a₁ = a₀
    · rw [heq]
    · have hmem : a₁ ∈ g.support.erase a₀ :=
        Finset.mem_erase.mpr ⟨heq, ha₁mem⟩
      exact le_of_lt (hmax a₁ hmem)
  have hW : 0 < shearWeight j (shearExp j D) a₀ :=
    production_weight_pos (K := K) j D hD a₁ ha₁ne a₀ hWle
  obtain ⟨f', hmem', hne', e, he, hdeg', hcoeff', hstrong'⟩ :=
    shear_strongMonic_of_mem j D hD P g hg a₀ ha₀ hmax hW
  exact fiberPredWeak_of_strongMonic P j (shearExp j D) f' hmem'
    hne' e he hdeg' hcoeff' hstrong'

/-- General fiber production: from prime data alone (`P ≠ ⊥`), some recipe
choice carries `fiberPredWeak` — the `fiber` remainder is closed. -/
theorem fiber_of_production {m : ℕ} {K : Type*} [Field K]
    (P : Ideal (MvPolynomial (Fin m) K)) [P.IsPrime]
    (j : Fin m) (hne : P ≠ ⊥) :
    ∃ D : ℕ, 1 < D ∧ fiberPredWeak m K P j (shearExp j D) := by
  obtain ⟨g, hg, hgne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  obtain ⟨D, hD, hb⟩ := shearExp_bounded j g
  exact ⟨D, hD, fiber_of_production_at P j D hD g hg hgne hb⟩

/-! ## (xxiii) Delete-`j` base chain and exhibit wiring.

Remainder item 2: the delete-`j` reindexing to `Fin (m - 1)`
(`delVar_card`, `delVarEquiv`, `delVarRename`) with base-prime comap
primality (`fiberBasePrime_isPrime`) and the reindexed prime map
(`delVarPrime`, strictly monotone), reindexing of the IH base chain
(`base_chain_reindex`); the fiber-pair going-down bridge
(`goingDown_of_fiber_integrality`, mirror of `goingDown_of_normalization`);
the below-contraction chain (`below_chain_of_goingDown`: `down_step`
strict rung plus `down_lift_below` lift, point inequality via
`asIdeal_lt_asIdeal`); and the wiring callers (`exhibit_of_fiber_base`
feeds `exhibit_of_shear_chain`, `hheight_of_fiber_base` feeds
`hheight_of_production`). The below-chain runs on flat going-down for the
delete-`j` inclusion (hypotheses `[Algebra]` / `[Module.Flat]`);
discharging `Flat` via freeness is the remaining model input (see
`## Obstruction`). -/

/-- Erase-card: deleting `j` leaves `m - 1` variables. -/
theorem delVar_card {m : ℕ} (j : Fin m) :
    Fintype.card {i : Fin m // i ≠ j} = m - 1 := by
  have e : ↥(Finset.univ.erase j) ≃ {i : Fin m // i ≠ j} :=
    Equiv.subtypeEquivRight (fun i =>
      ⟨fun h => (Finset.mem_erase.mp h).1,
        fun h => Finset.mem_erase.mpr ⟨h, Finset.mem_univ i⟩⟩)
  rw [← Fintype.card_congr e, Fintype.card_coe,
    Finset.card_erase_of_mem (Finset.mem_univ j), Finset.card_univ,
    Fintype.card_fin]

/-- Delete-`j` reindexing to `Fin (m - 1)`. -/
noncomputable def delVarEquiv {m : ℕ} (j : Fin m) :
    {i : Fin m // i ≠ j} ≃ Fin (m - 1) :=
  Fintype.equivFinOfCardEq (delVar_card j)

/-- Rename along the delete-`j` reindexing. -/
noncomputable def delVarRename {m : ℕ} {K : Type*} [Field K] (j : Fin m) :
    MvPolynomial {i : Fin m // i ≠ j} K ≃ₐ[K] MvPolynomial (Fin (m - 1)) K :=
  MvPolynomial.renameEquiv K (delVarEquiv j)

/-- Base-prime comap primality along the delete-`j` rename. -/
theorem fiberBasePrime_isPrime {m : ℕ} {K : Type*} [Field K] (j : Fin m)
    (q : Ideal (MvPolynomial (Fin (m - 1)) K)) [q.IsPrime] :
    (q.comap (delVarRename (K := K) j).toRingHom).IsPrime :=
  inferInstance

/-- The delete-`j` prime map: transport of base primes along the rename. -/
noncomputable def delVarPrime {m : ℕ} {K : Type*} [Field K] (j : Fin m) :
    PrimeSpectrum (MvPolynomial (Fin (m - 1)) K) →
      PrimeSpectrum (MvPolynomial {i : Fin m // i ≠ j} K) :=
  fun p => ⟨p.asIdeal.comap (delVarRename (K := K) j).toRingHom, inferInstance⟩

/-- The delete-`j` prime map is strictly monotone (comap along a surjective
map). -/
theorem delVarPrime_strictMono {m : ℕ} {K : Type*} [Field K] (j : Fin m) :
    StrictMono (delVarPrime (K := K) j) := by
  intro a b hab
  have habI : a.asIdeal < b.asIdeal := hab
  have hsurj : Function.Surjective (delVarRename (K := K) j).toRingHom := by
    intro y
    exact ⟨(delVarRename (K := K) j).symm y,
      (delVarRename (K := K) j).apply_symm_apply y⟩
  have h := RingHom.strictMono_comap_of_surjective hsurj habI
  exact h

/-- IH base-chain reindexing: a `Fin (m - 1)`-variable chain maps to the
same-length delete-`j` chain ending at the reindexed last prime. -/
theorem base_chain_reindex {m : ℕ} {K : Type*} [Field K] (j : Fin m)
    (L : LTSeries (PrimeSpectrum (MvPolynomial (Fin (m - 1)) K))) :
    ∃ L' : LTSeries (PrimeSpectrum (MvPolynomial {i : Fin m // i ≠ j} K)),
      L'.length = L.length ∧ L'.last = delVarPrime (K := K) j L.last := by
  refine ⟨L.map (delVarPrime (K := K) j) (delVarPrime_strictMono j), rfl, ?_⟩
  rw [LTSeries.last_map]

/-- Going-down for the fiber pair: fiber integrality over the UFD delete-`j`
base fires the integral-plus-normal-base instance on the contracted
quotient (mirror of `goingDown_of_normalization`). -/
theorem goingDown_of_fiber_integrality {m : ℕ} {K : Type*} [Field K]
    (j : Fin m) (Q : Ideal (MvPolynomial (Fin m) K)) [Q.IsPrime]
    (hinj : Function.Injective (delVarQuot j Q))
    (hint : (delVarQuot j Q).IsIntegral)
    [Algebra (MvPolynomial {i : Fin m // i ≠ j} K)
      (MvPolynomial (Fin m) K ⧸ Q)]
    (hmap : algebraMap (MvPolynomial {i : Fin m // i ≠ j} K)
        (MvPolynomial (Fin m) K ⧸ Q) = (delVarQuot j Q).toRingHom) :
    Algebra.HasGoingDown (MvPolynomial {i : Fin m // i ≠ j} K)
      (MvPolynomial (Fin m) K ⧸ Q) := by
  have hInt : Algebra.IsIntegral (MvPolynomial {i : Fin m // i ≠ j} K)
      (MvPolynomial (Fin m) K ⧸ Q) := by
    rw [← algebraMap_isIntegral_iff, hmap]
    exact hint
  have hfaith : FaithfulSMul (MvPolynomial {i : Fin m // i ≠ j} K)
      (MvPolynomial (Fin m) K ⧸ Q) := by
    rw [faithfulSMul_iff_algebraMap_injective, hmap]
    exact hinj
  exact inferInstance

/-- Below-contraction chain: a delete-`j` base chain of length `m - 1 - s`
ending below the base contraction lifts (flat going-down for the delete-`j`
inclusion) to a same-length big-ring chain ending strictly below the shear
contraction — the `hlt` input of `exhibit_of_shear_chain`. -/
theorem below_chain_of_goingDown {m : ℕ} {K : Type*} [Field K]
    (j : Fin m) (D : ℕ)
    (P : Ideal (MvPolynomial (Fin m) K)) [P.IsPrime]
    (s : ℕ)
    (l : LTSeries (PrimeSpectrum (MvPolynomial {i : Fin m // i ≠ j} K)))
    (hlen : l.length = m - 1 - s)
    (q : Ideal (MvPolynomial {i : Fin m // i ≠ j} K)) [q.IsPrime]
    [Algebra (MvPolynomial {i : Fin m // i ≠ j} K)
      (MvPolynomial (Fin m) K)]
    [Module.Flat (MvPolynomial {i : Fin m // i ≠ j} K)
      (MvPolynomial (Fin m) K)]
    [(shearContraction j (shearExp j D) P).LiesOver q]
    (hplt : l.last.asIdeal < q) :
    ∃ L : LTSeries (PrimeSpectrum (MvPolynomial (Fin m) K)),
      L.length = m - 1 - s ∧
        L.last < ⟨shearContraction j (shearExp j D) P,
          shearContraction_isPrime j (shearExp j D) P⟩ := by
  have : (shearContraction j (shearExp j D) P).IsPrime :=
    shearContraction_isPrime j (shearExp j D) P
  have : Algebra.HasGoingDown (MvPolynomial {i : Fin m // i ≠ j} K)
      (MvPolynomial (Fin m) K) :=
    goingDown_of_flat _ _
  obtain ⟨Q', hQ'lt, hQ'prime, hQ'lo⟩ :=
    down_step_of_goingDown (shearContraction j (shearExp j D) P) hplt
  have := hQ'prime
  have := hQ'lo
  obtain ⟨L, hlenL, hlastL, -⟩ := down_lift_below l Q'
  refine ⟨L, ?_, ?_⟩
  · rw [hlenL, hlen]
  · have hY : L.last.asIdeal = Q' := by rw [hlastL]
    apply (PrimeSpectrum.asIdeal_lt_asIdeal _ _).mpr
    change L.last.asIdeal < shearContraction j (shearExp j D) P
    rw [hY]
    exact hQ'lt

/-- Exhibit assembly from the IH base chain: the reindexed base chain runs
below the contraction, and `exhibit_of_shear_chain` closes `exhibit` — the
shape `hheight_of_production` takes. -/
theorem exhibit_of_fiber_base {m : ℕ} {K : Type*} [Field K] [Infinite K]
    (P : Ideal (MvPolynomial (Fin m) K)) [P.IsPrime]
    (s : ℕ) (hs : s < m) (j : Fin m) (D : ℕ)
    (L_IH : LTSeries (PrimeSpectrum (MvPolynomial (Fin (m - 1)) K)))
    (hlen_IH : L_IH.length = m - 1 - s)
    (q : Ideal (MvPolynomial {i : Fin m // i ≠ j} K)) [q.IsPrime]
    [Algebra (MvPolynomial {i : Fin m // i ≠ j} K)
      (MvPolynomial (Fin m) K)]
    [Module.Flat (MvPolynomial {i : Fin m // i ≠ j} K)
      (MvPolynomial (Fin m) K)]
    [(shearContraction j (shearExp j D) P).LiesOver q]
    (hplt : (delVarPrime (K := K) j L_IH.last).asIdeal < q) :
    ∃ l : LTSeries (PrimeSpectrum (MvPolynomial (Fin m) K)),
      l.length = m - s ∧ l.last = ⟨P, ‹P.IsPrime›⟩ := by
  obtain ⟨l_base, hlen_b, hlast_b⟩ := base_chain_reindex j L_IH
  have hplt' : l_base.last.asIdeal < q := by
    rw [hlast_b]
    exact hplt
  obtain ⟨L, hlenL, hltL⟩ :=
    below_chain_of_goingDown j D P s l_base (by rw [hlen_b, hlen_IH]) q hplt'
  exact exhibit_of_shear_chain P s hs j D L hlenL hltL

/-- `hheight` from fiber production plus the IH base chain: production closes
`fiber`, the reindexed base chain closes `exhibit`, and the recipe-fed datum
feeds `height_of_dpow_datum`. -/
theorem hheight_of_fiber_base (m s : ℕ) (K : Type*) [Field K] [Infinite K]
    (P : Ideal (MvPolynomial (Fin m) K)) [P.IsPrime]
    (normap : MvPolynomial (Fin s) K →ₐ[K] MvPolynomial (Fin m) K ⧸ P)
    (normap_inj : Function.Injective normap)
    (normap_int : normap.IsIntegral)
    (bad : Finset (Fin m → K))
    (dir : (Fin m → K) →ₗ[K] K)
    (dir_ne : ∀ v ∈ bad, dir v ≠ 0)
    (j : Fin m) (D : ℕ) (hD : 1 < D)
    (g : MvPolynomial (Fin m) K) (hg : g ∈ P) (hgne : g ≠ 0)
    (hb : ∀ a ∈ g.support, ∀ i : Fin m, a i < D)
    (hs : s < m)
    (L_IH : LTSeries (PrimeSpectrum (MvPolynomial (Fin (m - 1)) K)))
    (hlen_IH : L_IH.length = m - 1 - s)
    (q : Ideal (MvPolynomial {i : Fin m // i ≠ j} K)) [q.IsPrime]
    [Algebra (MvPolynomial {i : Fin m // i ≠ j} K)
      (MvPolynomial (Fin m) K)]
    [Module.Flat (MvPolynomial {i : Fin m // i ≠ j} K)
      (MvPolynomial (Fin m) K)]
    [(shearContraction j (shearExp j D) P).LiesOver q]
    (hplt : (delVarPrime (K := K) j L_IH.last).asIdeal < q) :
    (((m - s : ℕ)) : WithBot ℕ∞) ≤ (P.height : WithBot ℕ∞) := by
  have hD0 : D ≠ 0 := by omega
  have s_le : s ≤ m := le_of_lt hs
  have fiber : fiberPredWeak m K P j (shearExp j D) :=
    fiber_of_production_at P j D hD g hg hgne hb
  have exhibit := exhibit_of_fiber_base P s hs j D L_IH hlen_IH q hplt
  exact hheight_of_production m s K P s_le normap normap_inj normap_int bad dir
    dir_ne j D hD0 fiber exhibit

/-! ## (xxiv) Delete-`j` flatness via freeness and the induction wrapper.

Item (1): the delete-`j` inclusion
`MvPolynomial {i : Fin m // i ≠ j} K → MvPolynomial (Fin m) K` is flat.
Since `Fin m` is `Option` of the delete-`j` index type
(`Equiv.optionSubtypeNe`), renaming along that index equiv followed by
`MvPolynomial.optionEquivLeft` presents the big ring as univariate
polynomials over the delete-`j` base (`delVarPolyEquiv`), compatibly with the
rename inclusion (`delVar_compat`, by `MvPolynomial.induction_on` from the
generator case `delVar_compat_X`). The identification is `B`-linear
(`delVarLinearEquiv`), so the big ring is free — hence flat — over the base
(`delVarFlat`, via `Module.Flat.of_linearEquiv` and the
`Polynomial.basisMonomials` freeness). With the `Algebra` inclusion and
`Flat` as instances, the proved `below_chain_of_goingDown` /
`exhibit_of_fiber_base` / `hheight_of_fiber_base` fire with no model
hypotheses; `hheight_step_flat` records the narrowed step (production choice
plus below-positioned IH chain in, height bound out) and `hheight_of_eq`
closes the `s = m` base case unconditionally by reusing `exhibit_of_eq`
through the `triangular_monic_chain` height calculation.

## References

* `Mathlib/Algebra/MvPolynomial/Equiv.lean`, `MvPolynomial.renameEquiv`
  (+ `renameEquiv_symm/apply`), `MvPolynomial.optionEquivLeft`
  (+ `optionEquivLeft_X_some`).
* `Mathlib/Logic/Equiv/Option.lean`, `Equiv.optionSubtypeNe`
  (+ `optionSubtypeNe_symm_of_ne`).
* `Mathlib/Algebra/Polynomial/Basis.lean`, `Polynomial.basisMonomials`.
* `Mathlib/RingTheory/Flat/Basic.lean`, `Module.Flat.of_linearEquiv`,
  `Module.Flat.of_free` (instance).
* `Mathlib/Algebra/Algebra/Defs.lean`, `RingHom.toAlgebra`,
  `RingHom.algebraMap_toAlgebra` (rfl).
* `Mathlib/Algebra/MvPolynomial/Basic.lean`, `MvPolynomial.induction_on`,
  `MvPolynomial.algebraMap_eq`.
* `Mathlib/Algebra/MvPolynomial/Rename.lean`, `MvPolynomial.rename_X/C`.
* `Mathlib/Algebra/Polynomial/AlgebraMap.lean`, `Polynomial.algebraMap_eq`.
* `Mathlib/Algebra/Algebra/Tower.lean`, `IsScalarTower.algebraMap_eq`.
* `Mathlib/RingTheory/Ideal/Over.lean`, `Ideal.under`, `IsPrime.under`,
  `Ideal.over_under`.
-/

/-- The delete-`j` inclusion as an `Algebra` instance: a delete-`j` polynomial
maps to itself in the big ring (`MvPolynomial.rename` along `Subtype.val`). -/
noncomputable instance delVarAlgebra {m : ℕ} {K : Type*} [Field K] (j : Fin m) :
    Algebra (MvPolynomial {i : Fin m // i ≠ j} K) (MvPolynomial (Fin m) K) :=
  RingHom.toAlgebra
    (MvPolynomial.rename (fun i : {i : Fin m // i ≠ j} => (i : Fin m))).toRingHom

/-- `algebraMap` of the delete-`j` inclusion is the rename map (rfl-bridge for
rewriting). -/
theorem delVar_algebraMap {m : ℕ} {K : Type*} [Field K] (j : Fin m)
    (b : MvPolynomial {i : Fin m // i ≠ j} K) :
    algebraMap (MvPolynomial {i : Fin m // i ≠ j} K) (MvPolynomial (Fin m) K) b =
      MvPolynomial.rename (fun i : {i : Fin m // i ≠ j} => (i : Fin m)) b := rfl

/-- The delete-`j` polynomial identification: splitting off the deleted
variable presents `MvPolynomial (Fin m) K` as univariate polynomials over the
delete-`j` base. -/
noncomputable def delVarPolyEquiv {m : ℕ} {K : Type*} [Field K] (j : Fin m) :
    MvPolynomial (Fin m) K ≃ₐ[K]
      Polynomial (MvPolynomial {i : Fin m // i ≠ j} K) :=
  (MvPolynomial.renameEquiv K (Equiv.optionSubtypeNe j)).symm.trans
    (MvPolynomial.optionEquivLeft K {i : Fin m // i ≠ j})

/-- Generator compatibility for the identification: the included generator
`Xₙ` maps to `C (Xₙ)`. -/
theorem delVar_compat_X (m : ℕ) (K : Type*) [Field K] (j : Fin m)
    (n : {i : Fin m // i ≠ j}) :
    (delVarPolyEquiv j) (algebraMap (MvPolynomial {i : Fin m // i ≠ j} K)
      (MvPolynomial (Fin m) K) (MvPolynomial.X n)) =
      algebraMap (MvPolynomial {i : Fin m // i ≠ j} K)
        (Polynomial (MvPolynomial {i : Fin m // i ≠ j} K))
        (MvPolynomial.X n) := by
  rw [delVar_algebraMap, MvPolynomial.rename_X]
  simp only [delVarPolyEquiv, AlgEquiv.trans_apply, MvPolynomial.renameEquiv_symm,
    MvPolynomial.renameEquiv_apply, MvPolynomial.rename_X,
    Equiv.optionSubtypeNe_symm_of_ne n.prop, MvPolynomial.optionEquivLeft_X_some,
    Polynomial.algebraMap_eq, Subtype.eta n n.prop]

/-- General compatibility: the identification intertwines the delete-`j`
inclusion with polynomial constants. -/
theorem delVar_compat (m : ℕ) (K : Type*) [Field K] (j : Fin m)
    (b : MvPolynomial {i : Fin m // i ≠ j} K) :
    (delVarPolyEquiv j) (algebraMap (MvPolynomial {i : Fin m // i ≠ j} K)
      (MvPolynomial (Fin m) K) b) =
      algebraMap (MvPolynomial {i : Fin m // i ≠ j} K)
        (Polynomial (MvPolynomial {i : Fin m // i ≠ j} K)) b := by
  induction b using MvPolynomial.induction_on with
  | C a =>
    rw [delVar_algebraMap, MvPolynomial.rename_C]
    have eS : (MvPolynomial.C a : MvPolynomial (Fin m) K) = algebraMap K _ a :=
      DFunLike.congr_fun (MvPolynomial.algebraMap_eq K (Fin m)).symm a
    have eB : (MvPolynomial.C a : MvPolynomial {i : Fin m // i ≠ j} K) =
        algebraMap K _ a :=
      DFunLike.congr_fun
        (MvPolynomial.algebraMap_eq K {i : Fin m // i ≠ j}).symm a
    have hcomm := (delVarPolyEquiv (K := K) j).commutes a
    have htower : (algebraMap (MvPolynomial {i : Fin m // i ≠ j} K)
          (Polynomial (MvPolynomial {i : Fin m // i ≠ j} K))).comp
        (algebraMap K (MvPolynomial {i : Fin m // i ≠ j} K)) =
        algebraMap K (Polynomial (MvPolynomial {i : Fin m // i ≠ j} K)) :=
      (IsScalarTower.algebraMap_eq K (MvPolynomial {i : Fin m // i ≠ j} K)
        (Polynomial (MvPolynomial {i : Fin m // i ≠ j} K))).symm
    rw [eS, eB, hcomm, ← RingHom.comp_apply, htower]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p n hp => simp only [map_mul, hp, delVar_compat_X m K j n]

/-- Inverse compatibility. -/
theorem delVar_compat_symm (m : ℕ) (K : Type*) [Field K] (j : Fin m)
    (b : MvPolynomial {i : Fin m // i ≠ j} K) :
    (delVarPolyEquiv j).symm (algebraMap (MvPolynomial {i : Fin m // i ≠ j} K)
      (Polynomial (MvPolynomial {i : Fin m // i ≠ j} K)) b) =
      algebraMap (MvPolynomial {i : Fin m // i ≠ j} K)
        (MvPolynomial (Fin m) K) b := by
  rw [← delVar_compat m K j b]
  exact (delVarPolyEquiv j).symm_apply_apply _

/-- Forward `B`-linear map of the identification. -/
noncomputable def delVarToLin {m : ℕ} {K : Type*} [Field K] (j : Fin m) :
    MvPolynomial (Fin m) K →ₗ[MvPolynomial {i : Fin m // i ≠ j} K]
      Polynomial (MvPolynomial {i : Fin m // i ≠ j} K) where
  toFun := (delVarPolyEquiv j)
  map_add' := fun x y => map_add (delVarPolyEquiv j) x y
  map_smul' := fun b x => by
    simp only [RingHom.id_apply, Algebra.smul_def, map_mul, delVar_compat m K j b]

/-- Backward `B`-linear map of the identification. -/
noncomputable def delVarInvLin {m : ℕ} {K : Type*} [Field K] (j : Fin m) :
    Polynomial (MvPolynomial {i : Fin m // i ≠ j} K) →ₗ[MvPolynomial {i : Fin m // i ≠ j} K]
      MvPolynomial (Fin m) K where
  toFun := (delVarPolyEquiv j).symm
  map_add' := fun x y => map_add (delVarPolyEquiv j).symm x y
  map_smul' := fun b y => by
    simp only [RingHom.id_apply, Algebra.smul_def, map_mul,
      delVar_compat_symm m K j b]

/-- The `B`-linear equivalence: the big ring is a free (hence flat) module
over the delete-`j` base. -/
noncomputable def delVarLinearEquiv {m : ℕ} {K : Type*} [Field K] (j : Fin m) :
    MvPolynomial (Fin m) K ≃ₗ[MvPolynomial {i : Fin m // i ≠ j} K]
      Polynomial (MvPolynomial {i : Fin m // i ≠ j} K) where
  toLinearMap := delVarToLin j
  invFun := (delVarPolyEquiv j).symm
  left_inv := fun x => (delVarPolyEquiv j).symm_apply_apply x
  right_inv := fun y => (delVarPolyEquiv j).apply_symm_apply y

/-- Flatness of the delete-`j` inclusion: the big ring is `B`-linearly a
univariate polynomial ring, hence free, hence flat. -/
instance delVarFlat {m : ℕ} {K : Type*} [Field K] (j : Fin m) :
    Module.Flat (MvPolynomial {i : Fin m // i ≠ j} K)
      (MvPolynomial (Fin m) K) := by
  have hfree : Module.Free (MvPolynomial {i : Fin m // i ≠ j} K)
      (Polynomial (MvPolynomial {i : Fin m // i ≠ j} K)) :=
    Module.Free.of_basis (Polynomial.basisMonomials _)
  exact Module.Flat.of_linearEquiv (delVarLinearEquiv j)

/-- HilbertFunctionCount base case as an unconditional bound: when `s = m`, the
singleton exhibit (`exhibit_of_eq`) already forces the height inequality
through the `triangular_monic_chain` height calculation. -/
theorem hheight_of_eq (m s : ℕ) (K : Type*) [Field K] [Infinite K]
    (P : Ideal (MvPolynomial (Fin m) K)) [P.IsPrime]
    (h : s = m) :
    (((m - s : ℕ)) : WithBot ℕ∞) ≤ (P.height : WithBot ℕ∞) := by
  obtain ⟨l, hlen, hlast⟩ := exhibit_of_eq K P s h
  have hle : ((l.length : ℕ) : ℕ∞) ≤ P.height :=
    calc ((l.length : ℕ) : ℕ∞) ≤ Order.height l.last :=
            Order.length_le_height_last
        _ = Order.height (⟨P, ‹P.IsPrime›⟩ : PrimeSpectrum _) := by rw [hlast]
        _ = P.height := (PrimeSpectrum.height_eq_orderHeight _).symm
  have hleW : ((((l.length : ℕ) : ℕ∞)) : WithBot ℕ∞) ≤ (P.height : WithBot ℕ∞) :=
    WithBot.coe_le_coe.mpr hle
  rw [WithBot.coe_natCast] at hleW
  rwa [hlen] at hleW

/-- HilbertFunctionCount step with the model inputs discharged: production choice plus a
below-contraction IH chain give the height bound, with the delete-`j`
`Algebra`/`Flat` instances and the contraction's `LiesOver`/primality found
automatically (the contraction is taken as the comap, i.e. `Ideal.under`). -/
theorem hheight_step_flat (m s : ℕ) (K : Type*) [Field K] [Infinite K]
    (P : Ideal (MvPolynomial (Fin m) K)) [P.IsPrime]
    (normap : MvPolynomial (Fin s) K →ₐ[K] MvPolynomial (Fin m) K ⧸ P)
    (normap_inj : Function.Injective normap)
    (normap_int : normap.IsIntegral)
    (bad : Finset (Fin m → K))
    (dir : (Fin m → K) →ₗ[K] K)
    (dir_ne : ∀ v ∈ bad, dir v ≠ 0)
    (j : Fin m) (D : ℕ) (hD : 1 < D)
    (g : MvPolynomial (Fin m) K) (hg : g ∈ P) (hgne : g ≠ 0)
    (hb : ∀ a ∈ g.support, ∀ i : Fin m, a i < D)
    (hs : s < m)
    (L_IH : LTSeries (PrimeSpectrum (MvPolynomial (Fin (m - 1)) K)))
    (hlen_IH : L_IH.length = m - 1 - s)
    (hplt : (delVarPrime (K := K) j L_IH.last).asIdeal <
      (shearContraction j (shearExp j D) P).under
        (MvPolynomial {i : Fin m // i ≠ j} K)) :
    (((m - s : ℕ)) : WithBot ℕ∞) ≤ (P.height : WithBot ℕ∞) := by
  have hQ : (shearContraction j (shearExp j D) P).IsPrime :=
    shearContraction_isPrime j (shearExp j D) P
  exact hheight_of_fiber_base m s K P normap normap_inj normap_int bad dir dir_ne
    j D hD g hg hgne hb hs L_IH hlen_IH
    ((shearContraction j (shearExp j D) P).under
      (MvPolynomial {i : Fin m // i ≠ j} K)) hplt

/-! ## (xxv) Unconditional `hheight` via the extension prime.

The off-by-one in `hheight_step_flat`'s `hplt` (a full-length chain strictly
below the contraction prime `q`, one rung more than `height q = m - 1 - s`
allows) is repaired by gaining the rung in the univariate extension: the
extension prime `qR = q.map C` in `B[X] ≃ R` is prime, lies strictly below
the transported contraction (the strong-monic witness stays monic, hence
outside `qR`), and flat going-down for `C : B → B[X]` lifts the at-`q` IH
chain (length `m - 1 - s`, from strong induction on `m` with length
alignment `s_q = s` via integral dimension preservation) to end at `qR`.
Transport back along `delVarPolyEquiv`, `snoc`, and shear transport
(`exhibit_of_shear_chain`) close the exhibit; `hheight_of_production`
closes the bound. Degenerate cases are explicit: `s = m` by
`hheight_of_eq`; `P = ⊥` forces `s = m` by dimension (`seq_of_bot`);
`m = 1, s = 0` flows through with length-`0` chains (no `hplt` is needed
anywhere below).

## References

* `Mathlib/Order/KrullDimension.lean`, `Order.exists_series_of_le_height`.
* `Mathlib/RingTheory/Polynomial/Basic.lean`,
  `Polynomial.isPrime_map_C_of_isPrime`, `Polynomial.mem_map_C_iff`.
* `Mathlib/RingTheory/Ideal/Quotient/Operations.lean`,
  `Ideal.quotientEquiv`.
* `Mathlib/RingTheory/Ideal/Quotient/Defs.lean`, `Ideal.Quotient.lift`,
  `Ideal.Quotient.lift_mk`, `Ideal.Quotient.mk_surjective`,
  `Ideal.Quotient.eq_zero_iff_mem`.
* `Mathlib/Algebra/MvPolynomial/Equiv.lean`,
  `MvPolynomial.optionEquivLeft_X_some`,
  `MvPolynomial.optionEquivLeft_X_none`.
* `Mathlib/Logic/Equiv/Option.lean`, `Equiv.optionSubtypeNe_symm_self`,
  `Equiv.optionSubtypeNe_symm_of_ne`.
* `Formalization/Appendix_FixedPoint/BezoutChain/Dimension/TriangularChain.lean`,
  `quotient_dim_of_normap`, `normap_of_prime`.
* `Formalization/Appendix_FixedPoint/BezoutChain/
  Dimension/IntegralDimension.lean`, `ringKrullDim_eq_of_isIntegral`.
* `Formalization/Appendix_FixedPoint/BezoutChain/
  Dimension/PolynomialCatenary.lean`, `mvPolynomial_ringKrullDim`.
-/

/-- Normalization index fits in the ambient dimension. -/
theorem sle_of_normap (m s : ℕ) (K : Type*) [Field K]
    (P : Ideal (MvPolynomial (Fin m) K)) [P.IsPrime]
    (normap : MvPolynomial (Fin s) K →ₐ[K] MvPolynomial (Fin m) K ⧸ P)
    (normap_inj : Function.Injective normap)
    (normap_int : normap.IsIntegral) :
    s ≤ m := by
  have hdim : ringKrullDim (MvPolynomial (Fin m) K ⧸ P) =
      ((s : ℕ) : WithBot ℕ∞) :=
    quotient_dim_of_normap m s K P normap normap_inj normap_int
  have hle : ringKrullDim (MvPolynomial (Fin m) K ⧸ P) ≤
      ringKrullDim (MvPolynomial (Fin m) K) := ringKrullDim_quotient_le P
  rw [hdim, mvPolynomial_ringKrullDim] at hle
  exact_mod_cast hle

/-- The bottom prime forces the normalization index to be full: `P = ⊥`
presents `R ⧸ P ≃ R`, so `s = m` by dimension. -/
theorem seq_of_bot (m s : ℕ) (K : Type*) [Field K]
    (P : Ideal (MvPolynomial (Fin m) K)) [P.IsPrime]
    (normap : MvPolynomial (Fin s) K →ₐ[K] MvPolynomial (Fin m) K ⧸ P)
    (normap_inj : Function.Injective normap)
    (normap_int : normap.IsIntegral) (hP : P = ⊥) :
    s = m := by
  have hdim : ringKrullDim (MvPolynomial (Fin m) K ⧸ P) =
      ((s : ℕ) : WithBot ℕ∞) :=
    quotient_dim_of_normap m s K P normap normap_inj normap_int
  rw [hP, ringKrullDim_eq_of_ringEquiv (RingEquiv.quotientBot _),
    mvPolynomial_ringKrullDim] at hdim
  exact_mod_cast hdim.symm

/-- The shear contraction preserves the quotient dimension: the shear
automorphism descends to `R ⧸ Q ≃ R ⧸ P`. -/
theorem quot_dim_shear {m : ℕ} {K : Type*} [Field K]
    (j : Fin m) (D : ℕ)
    (P : Ideal (MvPolynomial (Fin m) K)) [P.IsPrime]
    (s : ℕ)
    (normap : MvPolynomial (Fin s) K →ₐ[K] MvPolynomial (Fin m) K ⧸ P)
    (normap_inj : Function.Injective normap)
    (normap_int : normap.IsIntegral) :
    ringKrullDim
        (MvPolynomial (Fin m) K ⧸ shearContraction j (shearExp j D) P) =
      ((s : ℕ) : WithBot ℕ∞) := by
  have hdimP : ringKrullDim (MvPolynomial (Fin m) K ⧸ P) =
      ((s : ℕ) : WithBot ℕ∞) :=
    quotient_dim_of_normap m s K P normap normap_inj normap_int
  have hcon : shearContraction j (shearExp j D) P =
      P.comap (triShear (K := K) j (shearExp j D)).symm.toAlgHom.toRingHom :=
    rfl
  have hcomp : (triShear (K := K) j (shearExp j D)).symm.toAlgHom.toRingHom.comp
      (triShear (K := K) j (shearExp j D)).toRingHom = RingHom.id _ :=
    RingHom.ext fun x => (triShear (K := K) j (shearExp j D)).symm_apply_apply x
  have hPQ : P = (shearContraction j (shearExp j D) P).map
      (((triShear (K := K) j (shearExp j D)).toRingEquiv.symm :
        MvPolynomial (Fin m) K ≃+* MvPolynomial (Fin m) K) :
        MvPolynomial (Fin m) K →+* MvPolynomial (Fin m) K) := by
    rw [Ideal.map_comap_of_equiv]
    change P = (shearContraction j (shearExp j D) P).comap
      (triShear (K := K) j (shearExp j D)).toRingHom
    rw [hcon, Ideal.comap_comap, hcomp, Ideal.comap_id]
  have e := Ideal.quotientEquiv (shearContraction j (shearExp j D) P) P
    (triShear (K := K) j (shearExp j D)).toRingEquiv.symm hPQ
  rw [ringKrullDim_eq_of_ringEquiv e]
  exact hdimP

/-- Comap of the extension ideal recovers the base ideal. -/
theorem comap_C_map_C {B : Type*} [CommRing B] (q : Ideal B) :
    Ideal.comap (Polynomial.C : B →+* Polynomial B)
      (Ideal.map (Polynomial.C : B →+* Polynomial B) q) = q := by
  ext x
  simp only [Ideal.mem_comap, Ideal.mem_map_C_iff]
  constructor
  · intro h
    have h0 := h 0
    rwa [Polynomial.coeff_C_zero] at h0
  · intro hx n
    by_cases hn : n = 0
    · subst hn
      rwa [Polynomial.coeff_C_zero]
    · rw [Polynomial.coeff_C_of_ne_zero hn]
      exact Submodule.zero_mem q

/-- Bridge: `delVarQuot` applied is the quotient of the renamed polynomial. -/
theorem delVarQuot_mk {m : ℕ} {K : Type*} [Field K] (j : Fin m)
    (Q : Ideal (MvPolynomial (Fin m) K))
    (b : MvPolynomial {i : Fin m // i ≠ j} K) :
    (delVarQuot j Q).toRingHom b =
      Ideal.Quotient.mk Q
        (MvPolynomial.rename (fun i : {i : Fin m // i ≠ j} => (i : Fin m)) b) := by
  simp only [delVarQuot]
  change (Ideal.Quotient.mkₐ K Q)
      (MvPolynomial.rename (fun i : {i : Fin m // i ≠ j} => (i : Fin m)) b) = _
  rw [Ideal.Quotient.mkₐ_eq_mk]

/-- The factored quotient map over the contraction: `delVarQuot` descends to
`B ⧸ q → R ⧸ Q` since its kernel is exactly the contraction. -/
noncomputable def baseQuotMap {m : ℕ} {K : Type*} [Field K] (j : Fin m)
    (Q : Ideal (MvPolynomial (Fin m) K)) [Q.IsPrime] :
    (MvPolynomial {i : Fin m // i ≠ j} K ⧸
      Q.under (MvPolynomial {i : Fin m // i ≠ j} K)) →+*
      (MvPolynomial (Fin m) K ⧸ Q) := by
  refine Ideal.Quotient.lift
    (Q.under (MvPolynomial {i : Fin m // i ≠ j} K))
    (delVarQuot j Q).toRingHom (fun b hb => ?_)
  rw [delVarQuot_mk, Ideal.Quotient.eq_zero_iff_mem]
  have h : algebraMap (MvPolynomial {i : Fin m // i ≠ j} K)
      (MvPolynomial (Fin m) K) b ∈ Q := hb
  rwa [delVar_algebraMap] at h

/-- The factored map unfolds to the lift composed with the quotient. -/
theorem baseQuotMap_comp_mk {m : ℕ} {K : Type*} [Field K] (j : Fin m)
    (Q : Ideal (MvPolynomial (Fin m) K)) [Q.IsPrime] :
    (baseQuotMap j Q).comp
      (Ideal.Quotient.mk (Q.under (MvPolynomial {i : Fin m // i ≠ j} K))) =
      (delVarQuot j Q).toRingHom :=
  Ideal.Quotient.lift_comp_mk _ _ _

/-- The factored map is injective: its kernel is exactly the contraction. -/
theorem baseQuotMap_injective {m : ℕ} {K : Type*} [Field K] (j : Fin m)
    (Q : Ideal (MvPolynomial (Fin m) K)) [Q.IsPrime] :
    Function.Injective (baseQuotMap j Q) := by
  have H : ∀ a : MvPolynomial {i : Fin m // i ≠ j} K,
      a ∈ Q.under (MvPolynomial {i : Fin m // i ≠ j} K) →
      (delVarQuot j Q).toRingHom a = 0 := by
    intro b hb
    rw [delVarQuot_mk, Ideal.Quotient.eq_zero_iff_mem]
    have h : algebraMap (MvPolynomial {i : Fin m // i ≠ j} K)
        (MvPolynomial (Fin m) K) b ∈ Q := hb
    rwa [delVar_algebraMap] at h
  have hI : RingHom.ker (delVarQuot j Q).toRingHom ≤
      Q.under (MvPolynomial {i : Fin m // i ≠ j} K) := by
    intro b hb
    have h0 : (delVarQuot j Q).toRingHom b = 0 := RingHom.mem_ker.mp hb
    rw [delVarQuot_mk, Ideal.Quotient.eq_zero_iff_mem] at h0
    change algebraMap (MvPolynomial {i : Fin m // i ≠ j} K)
      (MvPolynomial (Fin m) K) b ∈ Q
    rw [delVar_algebraMap]
    exact h0
  exact RingHom.lift_injective_of_ker_le_ideal _ H hI

/-- The factored map is integral: integrality descends along the base
quotient (same evaluation equation, mapped coefficients). -/
theorem baseQuotMap_isIntegral {m : ℕ} {K : Type*} [Field K] (j : Fin m)
    (Q : Ideal (MvPolynomial (Fin m) K)) [Q.IsPrime]
    (hint : (delVarQuot j Q).IsIntegral) :
    (baseQuotMap j Q).IsIntegral := by
  intro y
  obtain ⟨p, hmonic, heval⟩ := hint y
  refine ⟨p.map (Ideal.Quotient.mk
    (Q.under (MvPolynomial {i : Fin m // i ≠ j} K))), hmonic.map _, ?_⟩
  rw [Polynomial.eval₂_map, baseQuotMap_comp_mk]
  exact heval

/-- The delete-`j` base quotient has dimension `s`: integral dimension
preservation along the factored map, aligned with the shear quotient. -/
theorem quot_dim_base {m : ℕ} {K : Type*} [Field K] (j : Fin m) (D : ℕ)
    (P : Ideal (MvPolynomial (Fin m) K)) [P.IsPrime]
    (s : ℕ)
    (normap : MvPolynomial (Fin s) K →ₐ[K] MvPolynomial (Fin m) K ⧸ P)
    (normap_inj : Function.Injective normap)
    (normap_int : normap.IsIntegral)
    (hint : (delVarQuot j (shearContraction j (shearExp j D) P)).IsIntegral) :
    ringKrullDim (MvPolynomial {i : Fin m // i ≠ j} K ⧸
      (shearContraction j (shearExp j D) P).under
        (MvPolynomial {i : Fin m // i ≠ j} K)) =
      ((s : ℕ) : WithBot ℕ∞) := by
  have hdimQ : ringKrullDim
      (MvPolynomial (Fin m) K ⧸ shearContraction j (shearExp j D) P) =
      ((s : ℕ) : WithBot ℕ∞) :=
    quot_dim_shear j D P s normap normap_inj normap_int
  have : (shearContraction j (shearExp j D) P).IsPrime :=
    shearContraction_isPrime j (shearExp j D) P
  let : Algebra (MvPolynomial {i : Fin m // i ≠ j} K ⧸
      (shearContraction j (shearExp j D) P).under
        (MvPolynomial {i : Fin m // i ≠ j} K))
      (MvPolynomial (Fin m) K ⧸ shearContraction j (shearExp j D) P) :=
    (baseQuotMap j (shearContraction j (shearExp j D) P)).toAlgebra
  have : Algebra.IsIntegral (MvPolynomial {i : Fin m // i ≠ j} K ⧸
      (shearContraction j (shearExp j D) P).under
        (MvPolynomial {i : Fin m // i ≠ j} K))
      (MvPolynomial (Fin m) K ⧸ shearContraction j (shearExp j D) P) := by
    rw [← algebraMap_isIntegral_iff, RingHom.algebraMap_toAlgebra]
    exact baseQuotMap_isIntegral j _ hint
  have : FaithfulSMul (MvPolynomial {i : Fin m // i ≠ j} K ⧸
      (shearContraction j (shearExp j D) P).under
        (MvPolynomial {i : Fin m // i ≠ j} K))
      (MvPolynomial (Fin m) K ⧸ shearContraction j (shearExp j D) P) := by
    rw [faithfulSMul_iff_algebraMap_injective, RingHom.algebraMap_toAlgebra]
    exact baseQuotMap_injective j _
  have h := ringKrullDim_eq_of_isIntegral (R := MvPolynomial {i : Fin m // i ≠ j} K ⧸
    (shearContraction j (shearExp j D) P).under
      (MvPolynomial {i : Fin m // i ≠ j} K))
    (S := MvPolynomial (Fin m) K ⧸ shearContraction j (shearExp j D) P)
  rw [← h]
  exact hdimQ

/-- The identification sends the distinguished generator to `X`. -/
theorem delVarPolyEquiv_X_j (m : ℕ) (K : Type*) [Field K] (j : Fin m) :
    (delVarPolyEquiv (K := K) j) (MvPolynomial.X j) = Polynomial.X := by
  unfold delVarPolyEquiv
  simp only [AlgEquiv.trans_apply, MvPolynomial.renameEquiv_symm,
    MvPolynomial.renameEquiv_apply, MvPolynomial.rename_X,
    Equiv.optionSubtypeNe_symm_self, MvPolynomial.optionEquivLeft_X_none]

/-- The identification sends off-`j` generators to constants. -/
theorem delVarPolyEquiv_X_ne (m : ℕ) (K : Type*) [Field K] (j : Fin m)
    (i : Fin m) (hij : i ≠ j) :
    (delVarPolyEquiv (K := K) j) (MvPolynomial.X i) =
      Polynomial.C (MvPolynomial.X ⟨i, hij⟩) := by
  unfold delVarPolyEquiv
  simp only [AlgEquiv.trans_apply, MvPolynomial.renameEquiv_symm,
    MvPolynomial.renameEquiv_apply, MvPolynomial.rename_X,
    Equiv.optionSubtypeNe_symm_of_ne hij, MvPolynomial.optionEquivLeft_X_some]

/-- The identification sends scalar constants to constant constants. -/
theorem delVarPolyEquiv_C (m : ℕ) (K : Type*) [Field K] (j : Fin m) (c : K) :
    (delVarPolyEquiv (K := K) j) (MvPolynomial.C c) =
      Polynomial.C (MvPolynomial.C c) := by
  have hR : (MvPolynomial.C c : MvPolynomial (Fin m) K) = algebraMap K _ c :=
    DFunLike.congr_fun (MvPolynomial.algebraMap_eq K (Fin m)).symm c
  have hP : algebraMap K (Polynomial (MvPolynomial {i : Fin m // i ≠ j} K)) c =
      Polynomial.C (MvPolynomial.C c) := by
    rw [IsScalarTower.algebraMap_eq K (MvPolynomial {i : Fin m // i ≠ j} K)
      (Polynomial (MvPolynomial {i : Fin m // i ≠ j} K)), RingHom.comp_apply,
      Polynomial.algebraMap_eq,
      MvPolynomial.algebraMap_eq K {i : Fin m // i ≠ j}]
  rw [hR, (delVarPolyEquiv j).commutes c, hP]

/-- Factored monomial image: each monomial maps to a constant times a pure
`X`-power at its `j`-exponent (off-`j` content collects into the constant
via `delVarPolyEquiv_X_ne`). -/
theorem delVarPolyEquiv_monomial_factor (m : ℕ) (K : Type*) [Field K]
    (j : Fin m) (a : Fin m →₀ ℕ) (c : K) :
    (delVarPolyEquiv (K := K) j) (MvPolynomial.monomial a c) =
      Polynomial.C (MvPolynomial.C c *
        ∏ i ∈ a.support.erase j,
          (if h : i = j then (1 : MvPolynomial {i : Fin m // i ≠ j} K)
            else MvPolynomial.X ⟨i, h⟩ ^ (a i))) *
        Polynomial.X ^ (a j) := by
  have hfac : ∀ i ∈ a.support.erase j,
      (delVarPolyEquiv j) ((MvPolynomial.X i : MvPolynomial (Fin m) K) ^ (a i)) =
        Polynomial.C (if h : i = j then (1 : MvPolynomial {i : Fin m // i ≠ j} K)
          else MvPolynomial.X ⟨i, h⟩ ^ (a i)) := by
    intro i hi
    have hij : i ≠ j := (Finset.mem_erase.mp hi).1
    rw [map_pow, delVarPolyEquiv_X_ne m K j i hij, dite_eq_right hij, ← map_pow]
  have hCprod : ∏ i ∈ a.support.erase j,
      (delVarPolyEquiv j) ((MvPolynomial.X i : MvPolynomial (Fin m) K) ^ (a i)) =
      Polynomial.C (∏ i ∈ a.support.erase j,
        (if h : i = j then (1 : MvPolynomial {i : Fin m // i ≠ j} K)
          else MvPolynomial.X ⟨i, h⟩ ^ (a i))) := by
    rw [Finset.prod_congr rfl (fun i hi => hfac i hi), ← map_prod]
  have hsplit : (∏ i ∈ a.support, (delVarPolyEquiv j)
      ((MvPolynomial.X i : MvPolynomial (Fin m) K) ^ (a i))) =
      (delVarPolyEquiv j) ((MvPolynomial.X j : MvPolynomial (Fin m) K) ^ (a j)) *
        ∏ i ∈ a.support.erase j, (delVarPolyEquiv j)
          ((MvPolynomial.X i : MvPolynomial (Fin m) K) ^ (a i)) := by
    by_cases hj : j ∈ a.support
    · rw [← Finset.mul_prod_erase _ _ hj]
    · have haj0 : a j = 0 := Finsupp.notMem_support_iff.mp hj
      have herase : a.support.erase j = a.support := Finset.erase_eq_of_notMem hj
      rw [herase, haj0, pow_zero, map_one, one_mul]
  rw [MvPolynomial.monomial_eq, map_mul, delVarPolyEquiv_C,
    show (a.prod fun i k => (MvPolynomial.X i : MvPolynomial (Fin m) K) ^ k) =
      ∏ i ∈ a.support, (MvPolynomial.X i : MvPolynomial (Fin m) K) ^ (a i)
      from rfl,
    map_prod, hsplit, map_pow, delVarPolyEquiv_X_j, hCprod,
    mul_comm (Polynomial.X ^ (a j)) _, ← mul_assoc, ← map_mul]

/-- Erasing `j` kills the support of a `j`-single: only the `j`-coordinate
can be nonzero. -/
theorem support_erase_single (m : ℕ) (j : Fin m) (t : ℕ) :
    (Finsupp.single j t).support.erase j = ∅ := by
  rw [Finset.eq_empty_iff_forall_notMem]
  intro x hx
  rw [Finset.mem_erase] at hx
  obtain ⟨hne, hmem⟩ := hx
  exact (Finsupp.notMem_support_iff.mpr (Finsupp.single_eq_of_ne hne)) hmem

/-- Sum form of the identification: every polynomial maps to the sum of its
factored monomial images. -/
theorem delVarPolyEquiv_as_sum (m : ℕ) (K : Type*) [Field K] (j : Fin m)
    (f' : MvPolynomial (Fin m) K) :
    (delVarPolyEquiv (K := K) j) f' =
      ∑ a ∈ f'.support, Polynomial.C (MvPolynomial.C (f'.coeff a) *
        ∏ i ∈ a.support.erase j,
          (if h : i = j then (1 : MvPolynomial {i : Fin m // i ≠ j} K)
            else MvPolynomial.X ⟨i, h⟩ ^ (a i))) *
        Polynomial.X ^ (a j) := by
  conv_lhs => rw [MvPolynomial.as_sum f']
  rw [map_sum]
  exact Finset.sum_congr rfl (fun a ha =>
    delVarPolyEquiv_monomial_factor m K j a (f'.coeff a))

/-- Top coefficient: a strong-monic element maps to a univariate polynomial
with top coefficient `1` (only the top monomial contributes at `X^t`). -/
theorem coeff_delVarPolyEquiv_top (m : ℕ) (K : Type*) [Field K] (j : Fin m)
    (f' : MvPolynomial (Fin m) K) (t : ℕ)
    (hcoeff : f'.coeff (Finsupp.single j t) = 1)
    (hstrong : ∀ a ∈ f'.support, a ≠ Finsupp.single j t → a j < t) :
    ((delVarPolyEquiv (K := K) j) f').coeff t = 1 := by
  have hmem : Finsupp.single j t ∈ f'.support := by
    rw [MvPolynomial.mem_support_iff, hcoeff]
    exact one_ne_zero
  have honly : ∀ a ∈ f'.support, a j = t → a = Finsupp.single j t := by
    intro a ha hajt
    by_contra hne
    have hlt := hstrong a ha hne
    omega
  have h₀ : ∀ b ∈ f'.support, b ≠ Finsupp.single j t →
      (if t = b j then MvPolynomial.C (f'.coeff b) *
        ∏ i ∈ b.support.erase j,
          (if h : i = j then (1 : MvPolynomial {i : Fin m // i ≠ j} K)
            else MvPolynomial.X ⟨i, h⟩ ^ (b i)) else 0) = 0 := by
    intro b hb hbne
    rw [ite_eq_right (fun h => hbne (honly b hb h.symm))]
  have h₁ : Finsupp.single j t ∉ f'.support →
      (if t = (Finsupp.single j t) j then MvPolynomial.C (f'.coeff (Finsupp.single j t)) *
        ∏ i ∈ (Finsupp.single j t).support.erase j,
          (if h : i = j then (1 : MvPolynomial {i : Fin m // i ≠ j} K)
            else MvPolynomial.X ⟨i, h⟩ ^ ((Finsupp.single j t) i)) else 0) = 0 := by
    intro hcon
    exact False.elim (hcon hmem)
  rw [delVarPolyEquiv_as_sum m K j f', Polynomial.finsetSum_coeff]
  simp only [Polynomial.coeff_C_mul_X_pow]
  rw [Finset.sum_eq_single _ h₀ h₁, ite_eq_left (Finsupp.single_eq_same.symm),
    hcoeff, support_erase_single, Finset.prod_empty, MvPolynomial.C_1, one_mul]

/-- The extension prime sits below the transported contraction: constants
of `q` map into `Q` along the identification inverse. -/
theorem extPrime_le (m : ℕ) (K : Type*) [Field K] (j : Fin m)
    (Q : Ideal (MvPolynomial (Fin m) K)) [Q.IsPrime]
    (q : Ideal (MvPolynomial {i : Fin m // i ≠ j} K)) [q.IsPrime]
    (hQq : Q.under (MvPolynomial {i : Fin m // i ≠ j} K) = q) :
    Ideal.map (Polynomial.C : MvPolynomial {i : Fin m // i ≠ j} K →+*
        Polynomial (MvPolynomial {i : Fin m // i ≠ j} K)) q ≤
      Q.comap (delVarPolyEquiv (K := K) j).symm.toRingHom := by
  rw [Ideal.map_le_iff_le_comap]
  have hCe : (delVarPolyEquiv (K := K) j).symm.toRingHom.comp
      (Polynomial.C : MvPolynomial {i : Fin m // i ≠ j} K →+*
        Polynomial (MvPolynomial {i : Fin m // i ≠ j} K)) =
      algebraMap (MvPolynomial {i : Fin m // i ≠ j} K)
        (MvPolynomial (Fin m) K) := by
    apply RingHom.ext
    intro b
    simp only [RingHom.comp_apply]
    change (delVarPolyEquiv (K := K) j).symm (Polynomial.C b) = algebraMap _ _ b
    have h := delVar_compat m K j b
    rw [Polynomial.algebraMap_eq] at h
    rw [← h, AlgEquiv.symm_apply_apply]
  rw [Ideal.comap_comap, hCe, ← hQq]

/-- The monic witness lies in the transported contraction. -/
theorem extPrime_mem (m : ℕ) (K : Type*) [Field K] (j : Fin m)
    (Q : Ideal (MvPolynomial (Fin m) K)) [Q.IsPrime]
    (f' : MvPolynomial (Fin m) K) (hmem' : f' ∈ Q) :
    (delVarPolyEquiv (K := K) j) f' ∈
      Q.comap (delVarPolyEquiv (K := K) j).symm.toRingHom := by
  rw [Ideal.mem_comap]
  have h : (delVarPolyEquiv (K := K) j).symm
      ((delVarPolyEquiv (K := K) j) f') ∈ Q := by
    rw [AlgEquiv.symm_apply_apply]
    exact hmem'
  exact h

/-- The monic witness escapes the extension prime: a monic polynomial has
a unit coefficient outside every proper ideal. -/
theorem extPrime_notmem (m : ℕ) (K : Type*) [Field K] (j : Fin m)
    (q : Ideal (MvPolynomial {i : Fin m // i ≠ j} K)) [q.IsPrime]
    (p : Polynomial (MvPolynomial {i : Fin m // i ≠ j} K))
    (t : ℕ) (hcoeff : p.coeff t = 1) :
    p ∉ Ideal.map (Polynomial.C : MvPolynomial {i : Fin m // i ≠ j} K →+*
      Polynomial (MvPolynomial {i : Fin m // i ≠ j} K)) q := by
  intro hcon
  rw [Ideal.mem_map_C_iff] at hcon
  have h1 : (1 : MvPolynomial {i : Fin m // i ≠ j} K) ∈ q := by
    have h := hcon t
    rwa [hcoeff] at h
  have hne : q ≠ ⊤ := Ideal.IsPrime.ne_top'
  have hiff := Ideal.ne_top_iff_one q
  exact hiff.mp hne h1

/-- The extension prime is strictly below the transported contraction. -/
theorem extPrime_lt (m : ℕ) (K : Type*) [Field K] (j : Fin m)
    (Q : Ideal (MvPolynomial (Fin m) K)) [Q.IsPrime]
    (q : Ideal (MvPolynomial {i : Fin m // i ≠ j} K)) [q.IsPrime]
    (hQq : Q.under (MvPolynomial {i : Fin m // i ≠ j} K) = q)
    (f' : MvPolynomial (Fin m) K) (hmem' : f' ∈ Q)
    (p : Polynomial (MvPolynomial {i : Fin m // i ≠ j} K))
    (hp : (delVarPolyEquiv (K := K) j) f' = p)
    (t : ℕ) (hcoeff : p.coeff t = 1) :
    Ideal.map (Polynomial.C : MvPolynomial {i : Fin m // i ≠ j} K →+*
        Polynomial (MvPolynomial {i : Fin m // i ≠ j} K)) q <
      Q.comap (delVarPolyEquiv (K := K) j).symm.toRingHom := by
  have hle := extPrime_le m K j Q q hQq
  have hmem : (delVarPolyEquiv (K := K) j) f' ∈
      Q.comap (delVarPolyEquiv (K := K) j).symm.toRingHom :=
    extPrime_mem m K j Q f' hmem'
  have hnotmem : (delVarPolyEquiv (K := K) j) f' ∉
      Ideal.map (Polynomial.C : MvPolynomial {i : Fin m // i ≠ j} K →+*
        Polynomial (MvPolynomial {i : Fin m // i ≠ j} K)) q := by
    rw [hp]
    exact extPrime_notmem m K j q p t hcoeff
  apply lt_of_le_of_ne hle
  intro heq
  rw [← heq] at hmem
  exact hnotmem hmem

/-- The extension prime lies over the base prime. -/
theorem extPrime_liesOver (m : ℕ) (K : Type*) [Field K] (j : Fin m)
    (q : Ideal (MvPolynomial {i : Fin m // i ≠ j} K)) [q.IsPrime] :
    (Ideal.map (Polynomial.C : MvPolynomial {i : Fin m // i ≠ j} K →+*
      Polynomial (MvPolynomial {i : Fin m // i ≠ j} K)) q).LiesOver q := by
  refine ⟨?over⟩
  change q = Ideal.comap (algebraMap (MvPolynomial {i : Fin m // i ≠ j} K)
    (Polynomial (MvPolynomial {i : Fin m // i ≠ j} K)))
    (Ideal.map (Polynomial.C : MvPolynomial {i : Fin m // i ≠ j} K →+*
      Polynomial (MvPolynomial {i : Fin m // i ≠ j} K)) q)
  rw [Polynomial.algebraMap_eq, comap_C_map_C]

/-- Unconditional `hheight`, strong-induction auxiliary: the bound holds for
every prime with normalization data (explicit primality for the motive). -/
theorem hheight_uncond_aux (m : ℕ) (K : Type*) [Field K] [Infinite K]
    (s : ℕ) (P : Ideal (MvPolynomial (Fin m) K)) (hP : P.IsPrime)
    (normap : MvPolynomial (Fin s) K →ₐ[K] MvPolynomial (Fin m) K ⧸ P)
    (normap_inj : Function.Injective normap)
    (normap_int : normap.IsIntegral)
    (bad : Finset (Fin m → K))
    (dir : (Fin m → K) →ₗ[K] K)
    (dir_ne : ∀ v ∈ bad, dir v ≠ 0) :
    (((m - s : ℕ)) : WithBot ℕ∞) ≤ (P.height : WithBot ℕ∞) := by
  revert s P hP normap normap_inj normap_int bad dir dir_ne
  induction m using Nat.strongRecOn with
  | ind m IH =>
    intro s P hP normap normap_inj normap_int bad dir dir_ne
    have := hP
    by_cases heq : s = m
    · exact hheight_of_eq m s K P heq
    · have hs : s < m :=
        lt_of_le_of_ne (sle_of_normap m s K P normap normap_inj normap_int) heq
      rcases eq_or_ne P ⊥ with rfl | hne
      · exact absurd (seq_of_bot m s K ⊥ normap normap_inj normap_int rfl) heq
      · set j : Fin m := ⟨s, hs⟩ with hjdef
        obtain ⟨g, hg, hgne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
        obtain ⟨D, hD, hb⟩ := shearExp_bounded j g
        obtain ⟨a₁, ha₁mem, ha₁ne⟩ := exists_nonconst_of_prime P g hg hgne
        obtain ⟨a₀, ha₀, hmax⟩ :=
          exists_maxWeight_of_bound (K := K) j g D hD hgne hb
        have hWle : shearWeight j (shearExp j D) a₁ ≤
            shearWeight j (shearExp j D) a₀ := by
          by_cases heq : a₁ = a₀
          · rw [heq]
          · have hmem : a₁ ∈ g.support.erase a₀ :=
              Finset.mem_erase.mpr ⟨heq, ha₁mem⟩
            exact le_of_lt (hmax a₁ hmem)
        have hW : 0 < shearWeight j (shearExp j D) a₀ :=
          production_weight_pos (K := K) j D hD a₁ ha₁ne a₀ hWle
        obtain ⟨f', hmem', hne', t, ht, hdeg', hcoeff', hstrong'⟩ :=
          shear_strongMonic_of_mem j D hD P g hg a₀ ha₀ hmax hW
        have fiber : fiberPredWeak m K P j (shearExp j D) :=
          fiberPredWeak_of_strongMonic P j (shearExp j D) f' hmem' hne' t ht
            hdeg' hcoeff' hstrong'
        have hint : (delVarQuot j (shearContraction j (shearExp j D) P)).IsIntegral :=
          (fiber hne).2
        have hQp : (shearContraction j (shearExp j D) P).IsPrime :=
          shearContraction_isPrime j (shearExp j D) P
        set Q := shearContraction j (shearExp j D) P with hQdef
        set q := Q.under (MvPolynomial {i : Fin m // i ≠ j} K) with hqdef
        have hqp : q.IsPrime := by rw [hqdef]; infer_instance
        have hdimB : ringKrullDim (MvPolynomial {i : Fin m // i ≠ j} K ⧸ q) =
            ((s : ℕ) : WithBot ℕ∞) :=
          quot_dim_base j D P s normap normap_inj normap_int hint
        set qF := Ideal.comap (delVarRename (K := K) j).symm.toRingHom q
          with hqFdef
        have hqFp : qF.IsPrime := by rw [hqFdef]; infer_instance
        obtain ⟨s_q, hs_q_le, g_q, hinj_q, hint_q⟩ :=
          normap_of_prime (m - 1) K qF
        have hIH := IH (m - 1) (by omega) s_q qF hqFp g_q hinj_q hint_q
          (∅ : Finset (Fin (m - 1) → K)) 0 (by simp)
        have hIJ : q = qF.map ((delVarRename (K := K) j).symm.toRingEquiv :
            MvPolynomial (Fin (m - 1)) K ≃+*
              MvPolynomial {i : Fin m // i ≠ j} K) := by
          apply le_antisymm
          · intro x hx
            have h1 : (delVarRename (K := K) j) x ∈ qF := by
              rw [hqFdef, Ideal.mem_comap]
              change (delVarRename (K := K) j).symm
                ((delVarRename (K := K) j) x) ∈ q
              rw [(delVarRename (K := K) j).symm_apply_apply]
              exact hx
            have h2 : ((delVarRename (K := K) j).symm.toRingEquiv :
                MvPolynomial (Fin (m - 1)) K ≃+*
                  MvPolynomial {i : Fin m // i ≠ j} K)
                ((delVarRename (K := K) j) x) = x := by
              change (delVarRename (K := K) j).symm
                ((delVarRename (K := K) j) x) = x
              exact (delVarRename (K := K) j).symm_apply_apply x
            rw [← h2]
            exact Ideal.mem_map_of_mem _ h1
          · rw [Ideal.map_le_iff_le_comap]
            intro x hx
            change ((delVarRename (K := K) j).symm.toRingEquiv :
              MvPolynomial (Fin (m - 1)) K ≃+*
                MvPolynomial {i : Fin m // i ≠ j} K) x ∈ q
            exact hx
        have eQQ := Ideal.quotientEquiv qF q
          (delVarRename (K := K) j).symm.toRingEquiv hIJ
        have hdimEq : ringKrullDim (MvPolynomial {i : Fin m // i ≠ j} K ⧸ q) =
            ringKrullDim (MvPolynomial (Fin (m - 1)) K ⧸ qF) :=
          (ringKrullDim_eq_of_ringEquiv eQQ).symm
        have hdimBq : ringKrullDim (MvPolynomial (Fin (m - 1)) K ⧸ qF) =
            ((s_q : ℕ) : WithBot ℕ∞) :=
          quotient_dim_of_normap (m - 1) s_q K qF g_q hinj_q hint_q
        have hsq : s_q = s := by
          have hss : ((s : ℕ) : WithBot ℕ∞) = ((s_q : ℕ) : WithBot ℕ∞) := by
            rw [← hdimB, hdimEq]
            exact hdimBq
          exact_mod_cast hss.symm
        subst s_q
        have hleN : ((m - 1 - s : ℕ) : ℕ∞) ≤
            Order.height (⟨qF, hqFp⟩ : PrimeSpectrum (MvPolynomial (Fin (m - 1)) K)) := by
          have h2 : qF.height =
              Order.height (⟨qF, hqFp⟩ : PrimeSpectrum (MvPolynomial (Fin (m - 1)) K)) :=
            PrimeSpectrum.height_eq_orderHeight ⟨qF, hqFp⟩
          rw [h2] at hIH
          rw [← WithBot.coe_natCast] at hIH
          exact WithBot.coe_le_coe.mp hIH
        obtain ⟨cF, hlastF, hlenF⟩ :=
          Order.exists_series_of_le_height
            (⟨qF, hqFp⟩ : PrimeSpectrum (MvPolynomial (Fin (m - 1)) K)) hleN
        have hsurjR : Function.Surjective
            (delVarRename (K := K) j).toRingHom := by
          intro y
          exact ⟨(delVarRename (K := K) j).symm y,
            (delVarRename (K := K) j).apply_symm_apply y⟩
        have hmonoR : StrictMono
            (PrimeSpectrum.comap (delVarRename (K := K) j).toRingHom) :=
          RingHom.strictMono_comap_of_surjective hsurjR
        have hcBlen : (cF.map
            (PrimeSpectrum.comap (delVarRename (K := K) j).toRingHom)
            hmonoR).length = m - 1 - s := hlenF
        have hlastB : (cF.map
            (PrimeSpectrum.comap (delVarRename (K := K) j).toRingHom)
            hmonoR).last.asIdeal = q := by
          rw [LTSeries.last_map, hlastF]
          change Ideal.comap (delVarRename (K := K) j).toRingHom qF = q
          rw [hqFdef, Ideal.comap_comap]
          have hcomp : (delVarRename (K := K) j).symm.toRingHom.comp
              (delVarRename (K := K) j).toRingHom = RingHom.id _ :=
            RingHom.ext fun x =>
              (delVarRename (K := K) j).symm_apply_apply x
          rw [hcomp, Ideal.comap_id]
        have : Module.Free (MvPolynomial {i : Fin m // i ≠ j} K)
            (Polynomial (MvPolynomial {i : Fin m // i ≠ j} K)) :=
          Module.Free.of_basis (Polynomial.basisMonomials _)
        have : Algebra.HasGoingDown (MvPolynomial {i : Fin m // i ≠ j} K)
            (Polynomial (MvPolynomial {i : Fin m // i ≠ j} K)) :=
          goingDown_of_flat _ _
        have : (Ideal.map (Polynomial.C : MvPolynomial {i : Fin m // i ≠ j} K →+*
            Polynomial (MvPolynomial {i : Fin m // i ≠ j} K)) q).LiesOver
            ((cF.map (PrimeSpectrum.comap (delVarRename (K := K) j).toRingHom)
              hmonoR).last.asIdeal) := by
          rw [hlastB]
          exact extPrime_liesOver m K j q
        obtain ⟨cP, hcPlen, hcPlast, -⟩ := down_lift_below
          (cF.map (PrimeSpectrum.comap (delVarRename (K := K) j).toRingHom)
            hmonoR)
          (Ideal.map (Polynomial.C : MvPolynomial {i : Fin m // i ≠ j} K →+*
            Polynomial (MvPolynomial {i : Fin m // i ≠ j} K)) q)
        have hcPlen' : cP.length = m - 1 - s := hcPlen.trans hcBlen
        have hsurjE : Function.Surjective
            (delVarPolyEquiv (K := K) j).toRingHom := by
          intro y
          exact ⟨(delVarPolyEquiv (K := K) j).symm y,
            (delVarPolyEquiv (K := K) j).apply_symm_apply y⟩
        have hmonoE : StrictMono (PrimeSpectrum.comap
            (delVarPolyEquiv (K := K) j).toRingHom) :=
          RingHom.strictMono_comap_of_surjective hsurjE
        have hc := coeff_delVarPolyEquiv_top m K j f' t hcoeff' hstrong'
        have hltP : ((⟨Ideal.map (Polynomial.C :
                MvPolynomial {i : Fin m // i ≠ j} K →+*
                Polynomial (MvPolynomial {i : Fin m // i ≠ j} K)) q,
              inferInstance⟩ : PrimeSpectrum _) <
            ⟨Q.comap (delVarPolyEquiv (K := K) j).symm.toRingHom,
              inferInstance⟩) :=
          (PrimeSpectrum.asIdeal_lt_asIdeal _ _).mpr
            (extPrime_lt m K j Q q hqdef.symm f' hmem' _ rfl t hc)
        have hQback : PrimeSpectrum.comap (delVarPolyEquiv (K := K) j).toRingHom
            (⟨Q.comap (delVarPolyEquiv (K := K) j).symm.toRingHom,
              inferInstance⟩ : PrimeSpectrum _) =
            (⟨Q, hQp⟩ : PrimeSpectrum _) := by
          apply PrimeSpectrum.ext
          change Ideal.comap (delVarPolyEquiv (K := K) j).toRingHom
            (Q.comap (delVarPolyEquiv (K := K) j).symm.toRingHom) = Q
          rw [Ideal.comap_comap]
          have hcomp : (delVarPolyEquiv (K := K) j).symm.toRingHom.comp
              (delVarPolyEquiv (K := K) j).toRingHom = RingHom.id _ :=
            RingHom.ext fun x =>
              (delVarPolyEquiv (K := K) j).symm_apply_apply x
          rw [hcomp, Ideal.comap_id]
        have hltR : (cP.map (PrimeSpectrum.comap
            (delVarPolyEquiv (K := K) j).toRingHom) hmonoE).last <
            (⟨Q, hQp⟩ : PrimeSpectrum _) := by
          have h := hmonoE hltP
          rw [hQback] at h
          rw [LTSeries.last_map, hcPlast]
          exact h
        have hlenR : (cP.map (PrimeSpectrum.comap
            (delVarPolyEquiv (K := K) j).toRingHom) hmonoE).length =
            m - 1 - s := hcPlen'
        obtain ⟨lOut, hlenOut, hlastOut⟩ := exhibit_of_shear_chain P s hs j D
          _ hlenR hltR
        exact hheight_of_production m s K P (le_of_lt hs) normap normap_inj
          normap_int bad dir dir_ne j D (by omega) fiber
          ⟨lOut, hlenOut, hlastOut⟩

/-- Unconditional `hheight`: the normalization data alone force the height
bound (production, exhibit, and flatness all discharged internally). -/
theorem hheight_uncond (m s : ℕ) (K : Type*) [Field K] [Infinite K]
    (P : Ideal (MvPolynomial (Fin m) K)) [P.IsPrime]
    (normap : MvPolynomial (Fin s) K →ₐ[K] MvPolynomial (Fin m) K ⧸ P)
    (normap_inj : Function.Injective normap)
    (normap_int : normap.IsIntegral)
    (bad : Finset (Fin m → K))
    (dir : (Fin m → K) →ₗ[K] K)
    (dir_ne : ∀ v ∈ bad, dir v ≠ 0) :
    (((m - s : ℕ)) : WithBot ℕ∞) ≤ (P.height : WithBot ℕ∞) :=
  hheight_uncond_aux m K s P ‹P.IsPrime› normap normap_inj normap_int bad dir
    dir_ne

end Appendix_FixedPoint.BezoutChain
end EvolutionAlgebras

/-!
## Obstruction

Status: attempt 1 closed — the two remainder items are now
precisely characterized: one general computation proved, the `fiber` route
refuted as stated, the t2b division step reduced to an explicit bridge plus
its exact missing inputs. Previously closed (unchanged, byte-identical): the
`D ^ i` exponent recipe with its `adm` discharge (`shearExp`, `shearExp_at_j`,
`shearExp_adm`, `dpow_lt_of_lt`); the `fiber`-field predicate in verbatim
shape (`fiberPred`, `fiber_of_datum`); the flat going-down set-up with the
single-rung step and the full ending-at-`Q` lift (`goingDown_of_flat`,
`down_step_of_goingDown`, `down_lift_below`); the exact-shape feed into
`hnorm` (`datum_of_dpow_recipe`, `height_of_dpow_datum`); the generator
`degreeOf` lower bound plus recipe separation (`shear_image_degreeOf_ge`,
`shearExp_image_degreeOf_ge`, `shearExp_degreeOf_sep`); the made-monic step
(`fiberPred_of_mem_univariate`); and the exhibit induction skeleton
(`exhibit_of_eq`, `exhibit_extend_down`).

Closed:

1. `degreeOf`-under-shear for general polynomials (item (1),
   computation half): `shearWeight` (the per-monomial weight),
   `shearFwd_generator_degreeOf_eq` / `shear_generator_degreeOf_eq`
   (generator `=` with no `d i ≠ 0` hypothesis),
   `shear_monomial_degreeOf_le` (per-monomial cap via `aeval_monomial`),
   `shear_image_degreeOf_le` (general upper bound: `degreeOf j (σ f)` is at
   most the support-supremum of the weight, via `as_sum` +
   `degreeOf_sum_le`), and `shear_triShear_degreeOf_le` (transfer to
   `triShear`). There is no `degreeOf`-under-`aeval` API in Mathlib (verified
   by grep); the `IsHomogeneous` route does not apply (the shear is not
   graded); the leading-term route via `triShear_backsubst` is subsumed by
   the weight bound.
2. Weight collision for the `D ^ i` recipe: `shearExp_weight_tie` — for
   `2 ≤ m` the recipe weights are never injective (off-`j` index `0` carries
   `D ^ 0 = 1`, the fixed variable's own weight; dually at `j = 0`). Hence
   the `D ^ i` separation cannot isolate a unique maximal-weight term from
   the recipe alone.
3. Fiber refutation as stated (item (1), production half):
   `spanSub_coeff_single`, `no_univariate_in_span_sub`, and
   `fiberPred_false_span_sub` — for `P = span {X₀ - X₁} ⊂ K[X₀, X₁]` and
   every `j : Fin 2`, no nonzero univariate-off-`j` element of `P` exists, so
   the `fiber` field is underivable from shear data for arbitrary prime `P`
   (the datum is uninhabited there). The shear cannot repair this: it fixes
   `Xⱼ`, so `σ⁻¹(P) ∩ K[Xⱼ] = σ⁻¹(P ∩ K[Xⱼ])`.
4. t2b division-step bridge (item (2)):
   `isSMulRegular_of_span_ringEquiv` — regularity of a quotient class
   transfers across any ring equivalence mapping the span-generators, with no
   `Polynomial`/`triG` API (`TriangularRegularity` stays cited, not imported).

Precise remainder — what each route still owes:

1. `fiber`: blocked by finding (3), not by a missing computation. Options:
   (a) restrict to `s = 0` (maximal ideals contain monic univariates
   `Xⱼ - aⱼ`); (b) weaken `fiber` to monic-not-univariate plus integrality
   of `R ⧸ P` over the first-`(m - 1)`-variable quotient (the classical
   vehicle), which changes the `TriangularNormDatum.fiber` field shape in
   `TriangularChain.lean`; (c) a collision-free recipe (e.g. exponents
   `D ^ (i + 1)` off `j`) — repairs finding (2) but not finding (3).
2. Conditional exactness (unique maximal weight `⇒` `degreeOf = W` plus top
   coefficient): not proved; it needs the support-expansion of sheared
   monomials (every non-top summand choice drops the `j`-exponent below `W`).
   Given findings (2)+(3), its hypothesis is undischargeable for `shearExp`
   and its conclusion would not yield `g ∈ P` for general `P` anyway.
3. `exhibit`: the order-theoretic skeleton (`exhibit_of_eq`,
   `exhibit_extend_down`, `down_lift_below`) stands; the model-specific base
   chain (from fiber integrality) inherits the fiber block. The t2b
   instantiation needs, beyond bridge (4): (i) the last-variable isomorphism
   for arbitrary `shear_idx j` (variable permutation plus the
   `MvPolynomial`-to-`Polynomial` identification — not in
   `TriangularRegularity.lean`, whose own follow-ups are explicitly "not claimed
   there"); (ii) the t2b input data (`F₀ = a₀ · L₀`, nonzero minor
   `a₀ · F₁ - a₁ · F₀ ≠ 0`, `Prime a₀`, `¬ a₀ ∣ a₁`) at the sheared fiber
   polynomial.

Suggested next step: settle the datum scope — option (a)
vs (b) under remainder item 1 — before any further computation; the `D ^ i`
recipe plus univariate-`fiber` combination cannot close for general `P`.
The `datum_of_dpow_recipe` / `height_of_dpow_datum` assembly is in place for
whichever datum scope is chosen (feed via `triangular_monic_chain`, thence
to `hheight_uncond` and onwards to `hlow_uncond`,
`height_lower_bound_of_catenary_lower_bound`).

Status: reformulation attempt 1 closed — option (b) taken,
then refuted for the recipe; stopping here, remainder stated precisely.

Scope settled to option (b): `TriangularNormDatum.fiber` is weakened to
monic-not-univariate in the shear contraction plus the going-down
integrality input (`shearContraction`, `delVarQuot` in
`TriangularChain.lean`; mirrored here as `fiberPredWeak` with projection
`fiber_of_datum`). The weakening is principled: going-down induction needs
integrality, and monic-not-univariate plus integrality is exactly its input.

Closed:

1. `goingDown_of_normalization` — "integrality ⇒ going-down" for the
   normalization pair: the injective integral normalization map plus the UFD
   (hence integrally closed) polynomial base fires the
   integral-plus-normal-base going-down instance. Four narrow imports added
   (probed minimal).
2. Second refutation (production from shear data refutes — a result, not a
   failure): `triShear_recipe_span_sub_gen`,
   `contraction_recipe_span_sub`, `no_weakmonic_in_span_x0`, and
   `weakFiberPred_false_span_sub_recipe` — for `P = span {X₀ - X₁}` at
   `j = 1` and every `D`, the recipe contraction is `span {X₀}` (the recipe
   always puts exponent `D ^ 0 = 1` at index `0`, so the shear sends
   `X₀ - X₁ ↦ X₀`), whose every element carries `X₀`-content in each
   monomial, killing all pure-`X₁` coefficients. Hence the weakened fiber is
   uninhabited there too. Mechanism: the shear moves the obstruction rather
   than repairing it (it fixes `Xⱼ`); the `D ^ 0 = 1` collision is the same
   phenomenon as `shearExp_weight_tie`.
3. Mirrored collapse: `triShear_recipe_span_sub_gen_zero`,
   `contraction_recipe_span_sub_zero`, `no_weakmonic_in_span_x1`,
   `weakFiberPred_false_span_sub_recipe_zero` — at `j = 0`, `D = 1` the
   contraction is `span {X₁}` (`X₀ - X₁ ↦ -X₁`), likewise weak-monic-free.
4. Sharp boundary: `weakFiberMonic_escape_of_ne` — a general shear with
   `d 0 ≠ 1` escapes (the carried generator is already weak-monic up to a
   scalar). So the recipe, which forces the colliding exponent `1`, is
   specifically dead; a collision-free shear choice is not ruled out at the
   weak-monic level.

Precise remainder — nothing further is claimed, and no
going-down-to-`exhibit` run is attempted:

1. `fiber` integrality conjunct: unproved from shear data. The weak monic
   (degree pinned + pure coefficient `1`) does not entail integrality over
   the delete-`j` base — that needs the strong monic (all non-top monomials
   below top `j`-degree), i.e. remainder item 2 below. Until then the
   `delVarQuot ….IsIntegral` half of `fiberPredWeak` is an assumption, not
   a production.
2. Conditional exactness (unchanged): unique maximal weight `⇒`
   `degreeOf = W` plus top coefficient still needs the support-expansion of
   sheared monomials.
3. `exhibit`: the order-theoretic skeleton (`exhibit_of_eq`,
   `exhibit_extend_down`, `down_lift_below`) and the normalization-pair
   going-down (`goingDown_of_normalization`) stand; the model-specific base
   chain (from fiber integrality) inherits the fiber block of item 1.
   `height_of_dpow_datum` is unchanged (it passes `hnorm` whole); the
   `datum_of_dpow_recipe` / `height_of_dpow_datum` assembly stays in place
   for a datum scope that can actually be inhabited.
4. The t2b instantiation remainder (last-variable isomorphism plus t2b input
   data) is unchanged.

Suggested next step: either (i) a collision-free shear choice (e.g.
exponents `D ^ (i + 1)` off `j`) plus the strong-monic expansion, to revive
the fiber route for general `P`; or (ii) restrict the datum scope
(e.g. `s = 0`, where maximal ideals contain monic univariates) and re-run
production there. Do not re-attempt the `D ^ i` recipe: findings (2)+(3)
close that route.

Status: attempt 2 closed  — the
`D ^ (i + 1)` recipe replaces the dead `D ^ i` recipe, separation is proved,
the strong-monic expansion is proved, and the weakened fiber is assembled
(both conjuncts) on the diagonal test prime. No third counterexample: within
the recipe's operating range (`1 < D`) the test prime produces rather than
refutes.

Closed:

1. Recipe replacement + separation (item (1)): `shearExp` redefined
   to `D ^ (i.val + 1)` off `j`; `shearExp_adm` re-proved (`pow_ne_zero`);
   `shearWeight_single_off` / `shearWeight_single_at` (generator weights);
   `shearExp_weight_ne_one` (no off-`j` weight is `1` for `1 < D`);
   `shearExp_weight_sep` (distinct off-`j` indices get distinct weights).
   The former `shearExp_weight_tie` is deleted — the tie is killed by
   construction. `shearExp_image_degreeOf_ge` / `shearExp_degreeOf_sep`
   re-proved at the new exponents. One narrow import added
   (`IntegralClosure.Algebra.Basic`, for `IsIntegralElem.add/mul`).
2. Recipe boundary (item (1), refutation check):
   `triShear_recipe_span_sub_gen` now carries `X₀ + X₁ ^ D - X₁`;
   `triShear_recipe_span_sub_gen_one` / `contraction_recipe_span_sub_one` /
   `weakFiberPred_false_new_recipe_one` collapse the old every-`D`
   refutation to its `D = 1` boundary; `weakFiberMonic_new_recipe_of_lt`
   produces the monic conjunct at `1 < D` via the escape lemma. The
   `j = 0`, `D = 1` mirror keeps its statements.
3. Strong-monic expansion (item (2)): `carriedGen_coeff_top` /
   `carriedGen_coeff_x0` / `carriedGen_coeff_sub` /
   `carriedGen_coeff_other` / `carriedGen_support_sub` /
   `carriedGen_degreeOf` / `carriedGen_strong` / `carriedGen_strongMonic` —
   the carried generator is strong-monic (degree `D`, top coefficient `1`,
   all other support strictly below `D`); `carriedGen_mem_recipe` places it
   in the contraction; `delVarQuot_isIntegral_of_strongMonic` lifts any
   strong-monic element to `delVarQuot j Q` integrality (monic equation via
   `monic_X_pow_add`, evaluated through bundled `aeval` against `mk f = 0`,
   extended by `MvPolynomial.induction_on` with `IsIntegralElem` closure);
   `fiberPredWeak_span_sub_recipe_of_lt` assembles both `fiberPredWeak`
   conjuncts for `span {X₀ - X₁}` at `j = 1`, `1 < D`.

Precise remainder — current stopping point:

1. General production (item (2), weak-to-strong upgrade for general
   `P`): unproved. For nonzero `g ∈ P` one must choose `D` above all support
   coordinates (easy: finite support), prove base-`D` weight injectivity on
   the support (digits `< D` over distinct powers — needs a uniqueness
   argument with no direct Mathlib API), and expand sheared monomials to
   isolate the top term with its coefficient (needs the support-expansion of
   sheared monomials: product-of-sums over choice functions via
   `Finset.prod_sum`/`add_pow`, tracking `j`-degrees and off-`j` content —
   remainder item 2 of the previous pass, still open). None of this hits
   missing API; it is long, not blocked — but it is not attempted here.
2. Going-down induction to `exhibit` (item (3)): not run. It needs
   item 1 (production for general `P`, hence the conditional exactness),
   plus an induction architecture (reindexing the delete-`j` base to
   `Fin (m - 1)`, comap primality, `LiesOver`, chain transport along the
   shear automorphism) and the length-gain rung (from a length-`(m - 1 - s)`
   base chain to length-`(m - s)` ending at `P`). `height_of_dpow_datum`
   and the `datum_of_dpow_recipe` assembly stand ready for a datum scope
   that can actually be inhabited.
3. The t2b instantiation remainder (last-variable isomorphism plus t2b input
   data) is unchanged.
4. `TriangularChain.lean` needs no field change: `TriangularNormDatum` is
   byte-identical (only its `## Obstruction` note is updated); the fiber
   field shape already carries both conjuncts the assembly discharges.

Suggested next step: either attempt the general-production
push (base-`D` uniqueness + support-expansion, then the induction), or
restrict the datum scope (e.g. `s = 0`) and re-run production there. The
`D ^ (i + 1)` recipe, the separation lemmas, the lifting lemma, and the
test-prime assembly are banked and reusable either way.

Status: attempt 1 (construction push) — general production
(degree half + expansion statement), the going-down induction architecture,
and the `hheight` closure are proved; two precise remainders stand.

Closed:

1. Base-`D` weight injectivity + per-`P` D-choice (item (1),
   uniqueness half): `weightDigit` / `weightDigits` (explicit digit
   reading), `weight_eq_ofDigits` (weight is `Nat.ofDigits D`),
   `weight_injective_of_bounded` (via Mathlib's `Nat.injOn_ofDigits` — the
   uniqueness argument does hit direct API), `shearExp_bounded` (finite
   support gives `D` above all coordinates).
2. Weight split + monomial exactness (item (1), computation half):
   `shearWeight_recipe_eq`, `shearGen_ne_zero`,
   `shearFwd_monomial_eq_prod` (expansion first step via `aeval_monomial`),
   `degreeOf_pow_eq_of_ne`, `shear_monomial_degreeOf_eq` (`degreeOf = weight`
   per monomial via `degreeOf_prod_eq`, no expansion needed).
3. Unique-top extraction + packaged production (item (1), degree
   half): `degreeOf_sum_unique_max` (via `degreeOf_add_eq_of_degreeOf_lt`),
   `shear_poly_degreeOf_eq_of_unique_top`, `exists_maxWeight_of_bound`,
   `shear_poly_degreeOf_eq_of_bound`, `shear_production_degree` — for nonzero
   `g`, some `D > 1` makes the sheared `j`-degree exactly the maximal support
   weight.
4. Support expansion (item (1), expansion half):
   `shearGen_pow_eq_sum` (binomial factor shape) and
   `shearFwd_monomial_expand` (product-of-sums over choice functions via
   `Finset.prod_sum`).
5. Going-down induction architecture (item (3)):
   `shearContraction_isPrime` (comap primality),
   `shearPrime` / `shearPrime_strictMono` / `shearPrime_contraction`
   (transport proves on `P`), `chain_transport_shear` (same-length chain
   ending at `P`), `exhibit_length_gain` (the `(m - 1 - s) → (m - s)` rung
   via `snoc`), `exhibit_of_shear_chain` (conditional exhibit assembly).
6. Strong-monic assembly + closure: `fiberPredWeak_of_strongMonic` (both
   conjuncts at once) and `hheight_of_production` (recipe-fed datum feeds
   `height_of_dpow_datum`, the `hheight` shape).

Precise remainder:

1. Top-coefficient isolation (item (1), last open piece): from
   `shearFwd_monomial_expand`, show the top choice (`κ = 0` everywhere) carries
   coefficient `c` and every other choice has `j`-degree below the weight
   (needs `d i ≠ 0` off `j`, true at the recipe for `D ≠ 0`). This upgrades
   `shear_production_degree` to a strong-monic `f ∈ shearContraction j d P`,
   and `fiberPredWeak_of_strongMonic` then closes the `fiber` conjunct. Long,
   not API-blocked — not attempted here.
2. Below-contraction base chain (item (2), hypothesis of
   `exhibit_of_shear_chain`): delete-`j` reindexing to `Fin (m - 1)`, comap
   primality of the base prime, `LiesOver`, and the going-down lift of the IH
   chain. With it, `exhibit_of_shear_chain` + `hheight_of_production` close
   `hheight`.
3. The t2b instantiation remainder (last-variable isomorphism plus t2b input
   data) is unchanged.

Status: construction push verified — the six items above now
verify end to end with no warnings.
The eleven key new theorems (`weight_injective_of_bounded`,
`shearExp_bounded`, `shear_monomial_degreeOf_eq`,
`shear_production_degree`, `shearFwd_monomial_expand`,
`shearPrime_contraction`, `chain_transport_shear`, `exhibit_length_gain`,
`exhibit_of_shear_chain`, `fiberPredWeak_of_strongMonic`,
`hheight_of_production`) depend only on `[propext, Classical.choice,
Quot.sound]` (temporary `#print axioms`, removed afterwards).

Fix inventory (mechanical, statement-preserving): §xv's deprecated
`dif_pos`/`dif_neg`/`if_pos`/`if_neg` → `dite_eq_left`/`dite_eq_right`/
`ite_eq_left`/`ite_eq_right` (matching §§xvi–xix); unused binders to
`_j`/`_hij`; `single_eq_of_ne` direction (`hij`, not `Ne.symm hij` — the
lemma reads `a' ≠ a → (single a b) a' = 0`); the `i = j` generator
nonzeroness via `single j 1` (robust for all `e i`); a backwards `symm`
dropped before `Finset.sum_subset`; `Finsupp.mem_support_iff` for finsupp
supports; parenthesized `(PrimeSpectrum.asIdeal_lt_asIdeal _ _).mpr`/`.mp`
(the bare `.mpr` suffix mis-resolves as unknown); `RelSeries.snoc_length`
for the rung; `shearPrime_contraction` via `Ideal.comap_comap` plus a
`RingHom.ext`/`simp` comp computation (the `show`-chain through the equiv
coercions timed out the kernel). Note: a concurrent writer was active in
this file during the session; §§xvi–xix are proved as found and verified
as above, not re-derived here.

Remainder sharpening (for whoever funds item 1): top-term isolation yields
a scalar leading coefficient, not just a monomial one. The maximal-weight
support element `a₀` contributes exactly `c_{a₀} • Xⱼ ^ W` with `c_{a₀} ≠ 0`
(the top choice `κ = 0` carries `∏ C(e i, 0) = 1`; every other choice has
`j`-degree strictly below its own weight when `d i ≠ 0` off `j`; every
other support element has weight `< W`), so dividing by `c_{a₀}` — still in
the contraction ideal — yields a literally monic `Xⱼ`-polynomial whose
remaining support is `j`-below `W`: exactly the input shape of
`delVarQuot_isIntegral_of_strongMonic` + `fiberPredWeak_of_strongMonic`.
What remains is the choice-function bookkeeping, then remainder item 2
(the below-contraction base chain) to fire `exhibit_of_shear_chain` +
`hheight_of_production`.

Status: §xx proved — first half of remainder item 1, with axioms within
`[propext, Classical.choice, Quot.sound]`: `shear_factor_top_eq` (binomial factor at choice `0`
is the pure `Xⱼ`-power), `shear_top_prod_eq` (top-factor product is the
pure power at the off-`j` weight sum, via `prod_pow_eq_pow_sum`),
`shear_factor_degreeOf_le` (per-factor `j`-degree `≤ d i * e i`, `≤`-only:
`degreeOf_X_pow_of_ne` kills the `Xᵢ`-part, `degreeOf_pow_le` +
`degreeOf_X_self` bound the `Xⱼ`-part, `map_natCast` + `degreeOf_C` kill
the binomial cast — no nonzeroness, no characteristic hypothesis), and
`shear_choice_degreeOf_le` (every choice product has `j`-degree at most
the off-`j` weight sum, via `degreeOf_prod_le` + `sum_le_sum` over the
factor lemma). Elaboration lesson (brutally exact): `degreeOf_prod_le _
_ _` and `Finset.sum_le_sum h` fail to synthesize the function argument
against under-binder terms, and spelling the function out as an explicit
lambda makes `whnf` time out on the giant `MvPolynomial` terms; the fix is
to generalize the factor function to a rigid `∀ (F : ↥(erase j) → …)`
(`key`), so every higher-order unification becomes first-order or a
Miller pattern against a free variable — then `exact key _ hfac_le`
infers everything from the concrete hypothesis type.

Remainder item 1 narrowed (second half): per-choice `≤`-bounds are done;
open is the cross-sum assembly — strict `j`-degree drop for non-top
choices (needs `d i ≠ 0` off `j`, true at the recipe for `D ≠ 0`),
coefficient extraction at `single j W` (only `a₀`'s top choice
contributes `c_{a₀} ≠ 0`), and the strong-monic `f` assembly feeding
`fiberPredWeak_of_strongMonic`. Remainder item 2 (below-contraction base
chain) and the t2b remainder are unchanged.

Status: attempt 1 closed (construction push) — both remainder
items are closed end to end: (a) top-coefficient isolation feeds the
strong-monic upgrade and `fiberPredWeak_of_strongMonic` closes `fiber` from
prime data alone; (b) the delete-`j` base chain is reindexed, lifted below
the contraction, and wired through `exhibit_of_shear_chain` into
`hheight_of_production`. Verified: the seven key
theorems depend only on `[propext, Classical.choice, Quot.sound]`. No new imports.

Closed:

1. (xxi)+(xxii): strict top isolation (`shearTopChoice`,
   `shearTopChoice_mem`, `shearExp_of_mem`, `shearExp_pos_of_mem`,
   `sum_attach_erase`, `shearWeight_attach_eq`, `shear_choice_top_eq`,
   `shear_factor_degreeOf_tight`, `shear_nontop_degree_lt`), monomial
   decomposition (`shearWeight_zero`, `shear_monomial_top_decomp`), prime
   support (`exists_nonconst_of_prime`), weight positivity
   (`production_weight_pos`), global scaled strong-monic
   (`shear_strongMonic_of_mem`), and production at a choice plus from prime
   data (`fiber_of_production_at`, `fiber_of_production`).
2. (xxiii): delete-`j` reindexing (`delVar_card`, `delVarEquiv`,
   `delVarRename`, `fiberBasePrime_isPrime`, `delVarPrime`,
   `delVarPrime_strictMono`, `base_chain_reindex`), the fiber-pair
   going-down bridge (`goingDown_of_fiber_integrality`), the
   below-contraction chain (`below_chain_of_goingDown`), and the wiring
   callers (`exhibit_of_fiber_base`, `hheight_of_fiber_base`).

FiniteDimDischarge chains (quoted):

(a) `fiber`: `exists_nonconst_of_prime` (non-constant support element) →
`exists_maxWeight_of_bound` (unique maximal weight) →
`production_weight_pos` (maximal weight positive) →
`shear_strongMonic_of_mem` (scaled strong-monic in the contraction) →
`fiberPredWeak_of_strongMonic` (both conjuncts) → `fiber_of_production`
(`∃ D, 1 < D ∧ fiberPredWeak`, from `P ≠ ⊥` alone).

(b) `exhibit` / `hheight`: `base_chain_reindex` (IH chain to delete-`j`
type) → `below_chain_of_goingDown` (`down_step_of_goingDown` strict rung
plus `down_lift_below` lift, point inequality via `asIdeal_lt_asIdeal`) →
`exhibit_of_shear_chain` (snoc rung plus shear transport, now applied) →
`hheight_of_production` (recipe-fed datum into `height_of_dpow_datum`).

Precise remainder — hypotheses of `hheight_of_fiber_base`, nothing else:

1. The IH base chain (`L_IH`, length `m - 1 - s` over `Fin (m - 1)`) and
   its below-contraction position (`q` prime with the contraction lying
   over it, reindexed last strictly below `q`).
2. Flat going-down inputs for the delete-`j` inclusion (`[Algebra]`,
   `[Module.Flat]`): discharging `Flat` via freeness of the one-variable
   extension is the remaining model input.
3. Scope edges: `s = m` and `P = ⊥` cases (no `by_cases` inside; the
   caller threads `hs : s < m`, production threads `P ≠ ⊥`).
4. The t2b instantiation remainder is unchanged. `TriangularChain.lean`
   needs no field change (byte-identical; only this note is new here).

Fix inventory (mechanical, statement-preserving): `hRle` paren count;
`Ideal.mul_mem_left` argument order via `mul_comm` (keeping
`mul_inv_cancel₀`); `P = ⊤` via `eq_top_iff` (no new import); explicit
function in `Finset.add_sum_erase`; `congrArg`-guarded `map_sum`;
`if_pos` / `if_neg` closers via `simp`; `AddMonoidAlgebra.coeff_add` plus
`Finsupp.add_apply`; `(K := K)` ascription for `production_weight_pos`;
`max` (not `+`) in `degreeOf_add_le` via calc; `zero_add` (not `add_zero`);
`← hS` direction; `mul_assoc` before `← pow_add`; `have` (not `haveI`)
for TC-only Props; dropped unused production inputs from
`exhibit_of_fiber_base`. Elaboration lessons: `Finset.add_sum_erase _ _ h`
forces higher-order `?f` inference — provide `s` and `f` explicitly (this
was the `whnf` timeout at `shear_monomial_top_decomp`); `rw [hW]`-normalize
goals before `omega` when atoms mix a `shearWeight` application with its
expansion.

Status: induction wrapper — item (1)
closed, base case closed unconditionally, step narrowed to the below-chain
input; full unconditional closure not claimed (precise remainder below).
Verified. The five new
theorems (`delVarFlat`, `delVar_compat`, `delVarLinearEquiv`,
`hheight_of_eq`, `hheight_step_flat`) depend only on
`[propext, Classical.choice, Quot.sound]`. Three narrow imports added
(`Algebra.MvPolynomial.Equiv` for `renameEquiv`/`optionEquivLeft`,
`Algebra.Polynomial.Basis` for `basisMonomials`,
`RingTheory.Flat.Basic` for `Module.Flat.of_linearEquiv`/`of_free`).
No existing theorem, definition, or field modified (all byte-identical);
only doc bullets, imports, the new §xxiv, and this note are new.

Closed:

1. Delete-`j` flatness via freeness (item (1), API found by search
   `grep -rn` in `.lake/packages/mathlib` as prescribed — file-search
   misses `.lake/`): `delVarAlgebra` (the rename inclusion as an `Algebra`
   instance, via `RingHom.toAlgebra`), `delVar_algebraMap` (rfl-bridge),
   `delVarPolyEquiv` (index splitting `Equiv.optionSubtypeNe` + renaming +
   `MvPolynomial.optionEquivLeft`: the big ring is `B[X]` over the
   delete-`j` base), `delVar_compat_X` / `delVar_compat` /
   `delVar_compat_symm` (identification intertwines the inclusion with
   polynomial constants; general case by `MvPolynomial.induction_on`),
   `delVarToLin` / `delVarInvLin` / `delVarLinearEquiv` (the `B`-linear
   equivalence), `delVarFlat` (`Module.Flat` via `of_linearEquiv` +
   `of_basis (Polynomial.basisMonomials _)` + `of_free`). With these
   instances, `below_chain_of_goingDown` / `exhibit_of_fiber_base` /
   `hheight_of_fiber_base` fire with no `Algebra`/`Flat` hypotheses.
2. Base case closed unconditionally: `hheight_of_eq` (`s = m` reuses
   `exhibit_of_eq` through the `triangular_monic_chain` height
   calculation — no fiber/datum needed since `m - s = 0`).
3. Narrowed step: `hheight_step_flat` — same hypotheses as
   `hheight_of_fiber_base` minus `[Algebra]`/`[Module.Flat]`/`[LiesOver]`/
   `[IsPrime]` (the contraction is taken as the comap `Ideal.under`, whose
   primality and lying-over are instances). Remaining hypotheses: the
   production choice (`j`, `D`, `g`, `hb`), `hs : s < m`, the normap triple
   + `bad`/`dir`, and exactly the IH input (`L_IH`, `hlen_IH`, `hplt`).

Precise remainder — why the unconditional `hheight` (normap triple +
`bad`/`dir` in, `((m - s : ℕ) : WithBot ℕ∞) ≤ P.height` out, no IH/Flat/
LiesOver) is not closed here (length audit, not a missing computation):

* `hheight_step_flat` needs a delete-`j` base chain of length `m - 1 - s`
  ending strictly below the contraction prime `q`. Since the fiber makes
  `R ⧸ Q` integral over `B ⧸ q`, `dim (B ⧸ q) = dim (R ⧸ Q) = s`; in the
  `(m - 1)`-variable base that forces `height q = m - 1 - s` (catenary +
  equidimensionality), so a strictly-below chain of full length `m - 1 - s`
  would exhibit `height q ≥ m - s` — one rung more than the induction
  hypothesis for `m - 1` supplies (it ends *at* `q`, not below). The
  off-by-one is structural: check `s = 0` (then `q` is maximal and nothing
  sits below a full-length chain) and `m = 1, s = 0` (then the base is `K`,
  `q = ⊥`, and `hplt : ⊥ < ⊥` is false).
* Fix sketch (not attempted): the extension prime `qR = q.map C` in
  `B[X] ≃ R` is prime (quotient `(B ⧸ q)[X]`, a domain) and strictly below
  the transported contraction (the strong-monic witness has unit leading
  coefficient, hence lies outside `qR`); lifting the IH chain ending *at*
  `q` to end at `qR` via `down_lift_below`, then `snoc` + shear transport,
  gains the rung with satisfiable inputs. This needs the IH chain at `q`
  (length alignment via integral dimension preservation,
  `ringKrullDim_eq_of_algHom_isIntegral`, plus `normap_of_prime` for `q`)
  and strong induction on `m` with the motive generalizing over `Fin m`
  primes — the remaining work is that assembly, not flatness.
* Unchanged: scope edges from the previous pass and the t2b remainder.
  `TriangularChain.lean` needs no change (byte-identical; not touched).

Fix inventory (mechanical, statement-preserving): `noncomputable` on the
`Algebra`/equiv/`LinearMap`/`LinearEquiv`/`Flat` constructions (the
`MvPolynomial` commutative-semiring instance is noncomputable);
`LinearMap.map_smul'` is stated with `RingHom.id` on the scalar
(semilinear form — discharge with `RingHom.id_apply` in the `simp only`
pipeline, not by `rw` matching `b •`); fully explicit `algebraMap` types
in `delVar_compat*` statements (bare `algebraMap _ _` leaves `K`
to premature typeclass search: "stuck `CommSemiring ?m`"); explicit
`(m K)` binders on the compatibility lemmas for the same reason; `have`
(not `haveI`) for TC-only Props (per the `haveILetI` linter); equation
side-conditions by `Subtype.eta` and core `dite_eq_*` shapes only.

Status: unconditional hheight proved — `hheight_uncond_aux`
(strong induction on `m`, explicit primality in the motive) plus the public
wrapper `hheight_uncond`: normalization data (`normap` injective/integral
triple + `bad`/`dir`) alone force
`(((m - s : ℕ)) : WithBot ℕ∞) ≤ (P.height : WithBot ℕ∞)`, with production,
exhibit, and flatness all discharged internally. Verified. Both new theorems
depend only on `[propext, Classical.choice, Quot.sound]`. No new imports; no existing theorem,
definition, or field modified.

Assembly (quoted): `s = m` by `hheight_of_eq`; `P = ⊥` forces `s = m` by
`seq_of_bot`; else `j = ⟨s, hs⟩`, production from prime data alone
(`exists_nonconst_of_prime`, `exists_maxWeight_of_bound`,
`production_weight_pos`, `shear_strongMonic_of_mem`,
`fiberPredWeak_of_strongMonic` → `fiber`), contraction `Q` with
`hint`/`hQp`, base dimension `quot_dim_base`, reindex to `qF` over
`Fin (m - 1)` with `hIJ`/`quotientEquiv` dimension alignment `s_q = s`,
strong-IH chain at `qF` via `Order.exists_series_of_le_height`, comap to
the delete-`j` base, `down_lift_below` to the extension prime
(`extPrime_le/lt/liesOver`), transport back (`hQback`), `snoc` rung plus
shear transport (`exhibit_of_shear_chain`), close via
`hheight_of_production`. Degenerate `m = 1, s = 0` flows through with
length-`0` chains; no `hplt` is needed anywhere below.

Fix inventory (mechanical, statement-preserving): `hheight_of_eq m s K P
heq` directly (bare `subst heq` eliminates `m`, not `s`); `infer_instance`
(not `inferInstance`) inside `by` blocks; `rw [hqFdef, Ideal.mem_comap]`
plus `show`-to-`⇑e.symm` before `symm_apply_apply` (the lemma is about
FunLike application, not `.toRingHom` application);
`exact (delVarRename j).symm_apply_apply x` (not dotted `.mp` on the
explicit-`I` constant); `subst s_q` (not `subst hsq`, which eliminates `s`);
explicit `PrimeSpectrum (MvPolynomial (Fin (m - 1)) K)` ascriptions and
`PrimeSpectrum.height_eq_orderHeight ⟨qF, hqFp⟩` (bare `_` times out in
`isDefEq`/`whnf` against the `set`-folded `qF`); forward
`Ideal.comap_comap` (not `←`) to fuse nested comaps; split the `hltR`
rewrite (`rw [hQback] at h`, then `rw [LTSeries.last_map, hcPlast]`,
`exact h` — `LTSeries.last_map` matches the goal, not the `StrictMono`
image `h`).
-/
