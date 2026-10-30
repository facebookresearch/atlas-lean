/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.Probability.Percolation.RSW.Strip

/-!
# Elementary box-crossing bounds on `ℤ²`

Three elementary steps of Russo–Seymour–Welsh theory for a probability measure on bond
configurations of `ℤ²`, each stated with its geometric or correlation input as a hypothesis:

* the square-root trick for two events of equal probability, from the FKG inequality for their
  complements;
* the bound `ℙ(square crossing) ≥ 1/2` from self-duality (every square without an open
  left–right crossing has a dual top–bottom crossing, and the two crossings are equally likely);
  with the library's quarter-turn labelling of the dual, the first hypothesis fails for `n ≥ 2`
  (see `square_crossing_ge_half`);
* the bound `ℙ(crossing of [0, 2n] × [0, n]) ≥ 1/4` for a positively associated measure, from two
  half-crossings meeting at a common point of the middle column, each of probability `≥ 1/2`.

No RSW inequality is proved here: the hypotheses `hrouteLeft`, `hrouteRight` of
`box_crossing_lower_bound` (half-crossing probabilities at least `1/2`) carry the content of the
RSW argument.

## Main definitions

* `StatMech.RSW.BoxCrossing.squareCrossingEvent`, `squareDualCrossingEvent`: the open left–right
  crossing and the dual top–bottom crossing of `[0, n]²`.
* `StatMech.RSW.BoxCrossing.rectangleCrossingEvent`: the open left–right crossing of
  `[0, 2n] × [0, n]`.
* `StatMech.RSW.BoxCrossing.rectLeftHalfEvent`, `rectRightHalfEvent`: open paths from the left
  side of `[0, n] × [0, n]` to a point `z` of the column `x = n`, and from `z` to the right side of
  `[n, 2n] × [0, n]`.

## Main results

* `StatMech.RSW.BoxCrossing.sqrt_trick`: `μ(A) = μ(B)` and `μ(Aᶜ)μ(Bᶜ) ≤ μ(Aᶜ ∩ Bᶜ)` imply
  `1 - √(1 - μ(A ∪ B)) ≤ μ(A)`.
* `StatMech.RSW.BoxCrossing.square_crossing_ge_half`: self-duality gives `ℙ(square crossing) ≥ 1/2`.
* `StatMech.RSW.BoxCrossing.box_crossing_lower_bound`: half-crossings of probability `≥ 1/2` give
  `ℙ(crossing of [0, 2n] × [0, n]) ≥ 1/4`.

## References

* L. Russo, *A note on percolation*, Z. Wahrsch. Verw. Gebiete 43 (1978), 39–48.
* P. D. Seymour, D. J. A. Welsh, *Percolation probabilities on the square lattice*, Ann. Discrete
  Math. 3 (1978), 227–245.
* G. Grimmett, *Percolation*, 2nd ed., Springer, 1999, Chapter 11.
-/

@[expose] public section

open Set MeasureTheory
open scoped ENNReal NNReal

namespace StatMech

namespace RSW

namespace BoxCrossing

open StatMech.Lattice
open StatMech.RSW.Box
open StatMech.RSW.Strip
open StatMech.Universality

/-- Real-number core of the square-root trick: `m ≤ 1` and `(1 - m)² ≤ 1 - s` give
`1 - √(1 - s) ≤ m`.

This is the case `a = b` of `StatMech.Universality.sqrt_trick_max_real`. -/
theorem sqrt_trick_real {m s : ℝ} (hm1 : m ≤ 1)
    (h : (1 - m) ^ 2 ≤ 1 - s) : 1 - Real.sqrt (1 - s) ≤ m := by
  have h1m : (0 : ℝ) ≤ 1 - m := by linarith
  have hsqrt : Real.sqrt ((1 - m) ^ 2) ≤ Real.sqrt (1 - s) := Real.sqrt_le_sqrt h
  rw [Real.sqrt_sq h1m] at hsqrt
  linarith

/-- If the complements of `A` and `B` satisfy the FKG inequality, then
`μ(Aᶜ) μ(Bᶜ) ≤ 1 - μ(A ∪ B)`.

See also `StatMech.Universality.complUnion_fkg_bound`, which derives the same bound (written as
`(1 - μ A)(1 - μ B) ≤ 1 - μ(A ∪ B)`) from positive association for increasing `A`, `B`. -/
theorem complFKG_union_bound {E : Type*} (μ : Measure (ConfigSpace E))
    [IsProbabilityMeasure μ] {A B : Set (ConfigSpace E)}
    (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hFKGc : μ.real Aᶜ * μ.real Bᶜ ≤ μ.real (Aᶜ ∩ Bᶜ)) :
    μ.real Aᶜ * μ.real Bᶜ ≤ 1 - μ.real (A ∪ B) := by
  have hcomplU : μ.real (Aᶜ ∩ Bᶜ) = 1 - μ.real (A ∪ B) := by
    rw [← Set.compl_union, measureReal_compl (hA.union hB), probReal_univ]
  rwa [hcomplU] at hFKGc

/-- The **square-root trick** for two events of equal probability: if `μ(A) = μ(B)` and the
complements satisfy the FKG inequality, then `1 - √(1 - μ(A ∪ B)) ≤ μ(A)`.

See also `StatMech.Universality.rsw_sqrt_trick_eq`, the same conclusion from positive
association for increasing `A`, `B`. -/
theorem sqrt_trick {E : Type*} (μ : Measure (ConfigSpace E)) [IsProbabilityMeasure μ]
    {A B : Set (ConfigSpace E)} (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hm : μ.real A = μ.real B)
    (hFKGc : μ.real Aᶜ * μ.real Bᶜ ≤ μ.real (Aᶜ ∩ Bᶜ)) :
    1 - Real.sqrt (1 - μ.real (A ∪ B)) ≤ μ.real A := by
  set m := μ.real A with hmdef
  have hcomplA : μ.real Aᶜ = 1 - m := by rw [measureReal_compl hA, probReal_univ]
  have hcomplB : μ.real Bᶜ = 1 - m := by rw [measureReal_compl hB, probReal_univ, ← hm]
  have hbound := complFKG_union_bound μ hA hB hFKGc
  rw [hcomplA, hcomplB] at hbound
  have hkey : (1 - m) ^ 2 ≤ 1 - μ.real (A ∪ B) := by nlinarith [hbound]
  exact sqrt_trick_real (by rw [hmdef]; exact measureReal_le_one) hkey

/-- The open left–right crossing of the square `[0, n]²`. -/
def squareCrossingEvent (n : ℤ) : Set (ConfigSpace (Sym2 (Site 2))) :=
  horizontalCrossingEvent 0 n 0 n

/-- The top–bottom crossing of the square `[0, n]²` in the dual configuration. -/
def squareDualCrossingEvent (n : ℤ) : Set (ConfigSpace (Sym2 (Site 2))) :=
  dualVerticalCrossingEvent 0 n 0 n

/-- Self-duality bound for square crossings: if every configuration without an open left–right
crossing of `[0, n]²` has a dual top–bottom crossing (`hdualExists`) and the two crossings have
the same probability (`hselfDual`), then the open crossing has probability at least `1/2`.

Fidelity: `dualConfig` labels dual edges by a quarter turn about the origin, so
`squareDualCrossingEvent n` is not the geometric dual crossing of `[0, n]²`, and `hdualExists` is
false for `n = 2` (`StatMech.Universality.bcc_dichotomy_false`); the same wall configuration
refutes it for every `n ≥ 2` (by hand). The theorem is therefore vacuous for `n ≥ 2`.

See also `StatMech.Universality.rst_selfDual_box_crossing_half`, the same argument for the
self-dual measure with the symmetry stated through vertical crossings. -/
theorem square_crossing_ge_half (μ : Measure (ConfigSpace (Sym2 (Site 2))))
    [IsProbabilityMeasure μ] (n : ℤ)
    (hdualExists : (squareCrossingEvent n)ᶜ ⊆ squareDualCrossingEvent n)
    (hselfDual : μ.real (squareDualCrossingEvent n) = μ.real (squareCrossingEvent n))
    (hmeas : MeasurableSet (squareCrossingEvent n)) :
    (1 : ℝ) / 2 ≤ μ.real (squareCrossingEvent n) := by
  have hcompl : μ.real (squareCrossingEvent n)ᶜ = 1 - μ.real (squareCrossingEvent n) := by
    rw [measureReal_compl hmeas, probReal_univ]
  have hmono : μ.real (squareCrossingEvent n)ᶜ ≤ μ.real (squareDualCrossingEvent n) :=
    measureReal_mono hdualExists
  rw [hselfDual] at hmono
  rw [hcompl] at hmono
  linarith

/-- The open left–right crossing of the rectangle `[0, 2n] × [0, n]`. -/
def rectangleCrossingEvent (n : ℤ) : Set (ConfigSpace (Sym2 (Site 2))) :=
  horizontalCrossingEvent 0 (2 * n) 0 n

/-- An open path inside `[0, n] × [0, n]` from its left side to the point `z` with `z 0 = n`. -/
def rectLeftHalfEvent (n : ℤ) (hn : 0 ≤ n) {z : Site 2} (hz0 : z 0 = n) (hzc : 0 ≤ z 1)
    (hzd : z 1 ≤ n) : Set (ConfigSpace (Sym2 (Site 2))) :=
  leftHalfCrossingEvent 0 n 0 n z
    (rightSide_subset (mem_shared_column (a := 0) (m := n) (b := 2 * n) (c := 0) (d := n)
      hn (by linarith) hz0 hzc hzd).1)

/-- An open path inside `[n, 2n] × [0, n]` from the point `z` with `z 0 = n` to its right side. -/
def rectRightHalfEvent (n : ℤ) (hn : 0 ≤ n) {z : Site 2} (hz0 : z 0 = n) (hzc : 0 ≤ z 1)
    (hzd : z 1 ≤ n) : Set (ConfigSpace (Sym2 (Site 2))) :=
  rightHalfCrossingEvent n (2 * n) 0 n z
    (leftSide_subset (mem_shared_column (a := 0) (m := n) (b := 2 * n) (c := 0) (d := n)
      hn (by linarith) hz0 hzc hzd).2)

/-- For a positively associated probability measure, if the two half-crossings through a common
point `z` of the column `x = n` each have probability at least `1/2`, then `[0, 2n] × [0, n]` is
crossed left to right with probability at least `1/4`. The hypotheses `hrouteLeft` and
`hrouteRight` carry the RSW content; they are not derived here. -/
theorem box_crossing_lower_bound
    (μ : Measure (ConfigSpace (Sym2 (Site 2)))) [IsProbabilityMeasure μ]
    (hpa : PositivelyAssociated μ) (n : ℤ) (hn : 0 ≤ n) {z : Site 2} (hz0 : z 0 = n)
    (hzc : 0 ≤ z 1) (hzd : z 1 ≤ n)
    (hrouteLeft : (1 : ℝ) / 2 ≤ μ.real (rectLeftHalfEvent n hn hz0 hzc hzd))
    (hrouteRight : (1 : ℝ) / 2 ≤ μ.real (rectRightHalfEvent n hn hz0 hzc hzd)) :
    (1 : ℝ) / 4 ≤ μ.real (rectangleCrossingEvent n) := by
  have hprod : (1 : ℝ) / 4
      ≤ μ.real (rectLeftHalfEvent n hn hz0 hzc hzd)
          * μ.real (rectRightHalfEvent n hn hz0 hzc hzd) := by
    have h1 : (0 : ℝ) ≤ μ.real (rectLeftHalfEvent n hn hz0 hzc hzd) := measureReal_nonneg
    nlinarith [hrouteLeft, hrouteRight, h1]
  have hmb : (n : ℤ) ≤ 2 * n := by linarith
  exact le_trans hprod
    (measureReal_horizontalCrossing_ge_halves (a := 0) (m := n) (b := 2 * n) (c := 0) (d := n)
      hn hmb hz0 hzc hzd μ hpa)

/-- Existential form of `box_crossing_lower_bound`. -/
theorem box_crossing_lower_bound_pos
    (μ : Measure (ConfigSpace (Sym2 (Site 2)))) [IsProbabilityMeasure μ]
    (hpa : PositivelyAssociated μ) (n : ℤ) (hn : 0 ≤ n) {z : Site 2} (hz0 : z 0 = n)
    (hzc : 0 ≤ z 1) (hzd : z 1 ≤ n)
    (hrouteLeft : (1 : ℝ) / 2 ≤ μ.real (rectLeftHalfEvent n hn hz0 hzc hzd))
    (hrouteRight : (1 : ℝ) / 2 ≤ μ.real (rectRightHalfEvent n hn hz0 hzc hzd)) :
    ∃ c : ℝ, 0 < c ∧ c ≤ μ.real (rectangleCrossingEvent n) :=
  ⟨1 / 4, by norm_num,
    box_crossing_lower_bound μ hpa n hn hz0 hzc hzd hrouteLeft hrouteRight⟩

end BoxCrossing

end RSW

end StatMech
