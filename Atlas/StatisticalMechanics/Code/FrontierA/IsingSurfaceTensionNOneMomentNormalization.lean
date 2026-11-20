/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierA.IsingSurfaceTensionNOneExponentBounds









open Finset

namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

open StatMech StatMech.Ising

private theorem eval_foldl_add_apply (X Y : Real) (f : Nat -> BiPoly)
    (xs : List Nat) (p : BiPoly) :
    (xs.foldl (fun p x => p.add (f x)) p).eval X Y =
      p.eval X Y + (xs.map fun x => (f x).eval X Y).sum := by
  induction xs generalizing p with
  | nil => simp
  | cons x xs ih =>
      rw [List.foldl_cons, ih]
      change (p + f x).eval X Y + _ = _
      rw [BiPoly.eval_add]
      simp only [List.map_cons, List.sum_cons]
      ring

private theorem list_range_sum_eq_finset_range_sum
    (f : Nat -> Real) (n : Nat) :
    ((List.range n).map f).sum = ∑ i ∈ Finset.range n, f i := by
  induction n with
  | zero => simp
  | succ n ih => simp [List.range_succ, ih, Finset.sum_range_succ]

theorem BiPoly.eval_sumCodes (X Y : Real) (f : Nat -> BiPoly) :
    (BiPoly.sumCodes f).eval X Y =
      ((List.range 512).map fun s => (f s).eval X Y).sum := by
  unfold BiPoly.sumCodes
  rw [eval_foldl_add_apply]
  simp

theorem BiPoly.eval_sumCodes_eq_fin_sum (X Y : Real) (f : Nat -> BiPoly) :
    (BiPoly.sumCodes f).eval X Y =
      ∑ s : Fin 512, (f s).eval X Y := by
  rw [BiPoly.eval_sumCodes, list_range_sum_eq_finset_range_sum]
  exact (Fin.sum_univ_eq_sum_range
    (fun s : Nat => (f s).eval X Y) 512).symm

private theorem spinCode_odd (s k : Nat) : Odd (spinCode s k) := by
  unfold spinCode
  split <;> norm_num

private theorem odd_sum_nine
    {a0 a1 a2 a3 a4 a5 a6 a7 a8 : Int}
    (h0 : Odd a0) (h1 : Odd a1) (h2 : Odd a2) (h3 : Odd a3)
    (h4 : Odd a4) (h5 : Odd a5) (h6 : Odd a6) (h7 : Odd a7)
    (h8 : Odd a8) :
    Odd (a0 + a1 + a2 + a3 + a4 + a5 + a6 + a7 + a8) := by
  have h01 := h0.add_odd h1
  have h012 := h01.add_odd h2
  have h0123 := h012.add_odd h3
  have h01234 := h0123.add_odd h4
  have h012345 := h01234.add_odd h5
  have h0123456 := h012345.add_odd h6
  have h01234567 := h0123456.add_odd h7
  exact h01234567.add_odd h8

private theorem even_sum_twelve
    {a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 : Int}
    (h0 : Odd a0) (h1 : Odd a1) (h2 : Odd a2) (h3 : Odd a3)
    (h4 : Odd a4) (h5 : Odd a5) (h6 : Odd a6) (h7 : Odd a7)
    (h8 : Odd a8) (h9 : Odd a9) (h10 : Odd a10) (h11 : Odd a11) :
    Even (a0 + a1 + a2 + a3 + a4 + a5 + a6 + a7 + a8 + a9 +
      a10 + a11) := by
  have h01 := h0.add_odd h1
  have h012 := h01.add_odd h2
  have h0123 := h012.add_odd h3
  have h01234 := h0123.add_odd h4
  have h012345 := h01234.add_odd h5
  have h0123456 := h012345.add_odd h6
  have h01234567 := h0123456.add_odd h7
  have h012345678 := h01234567.add_odd h8
  have h0123456789 := h012345678.add_odd h9
  have h012345678910 := h0123456789.add_odd h10
  exact h012345678910.add_odd h11

private theorem layerInternalInt_even (s : Nat) :
    Even (layerInternalInt s) := by
  unfold layerInternalInt
  apply even_sum_twelve <;> exact (spinCode_odd _ _).mul (spinCode_odd _ _)

private theorem layerLateralInt_even (s : Nat) :
    Even (layerLateralInt s) := by
  unfold layerLateralInt
  exact ((((((((layerInternalInt_even s).add (even_two_mul _)).add_odd
    (spinCode_odd _ _)).add_even (even_two_mul _)).add_odd
    (spinCode_odd _ _)).add_odd (spinCode_odd _ _)).add_even
    (even_two_mul _)).add_odd (spinCode_odd _ _)).add (even_two_mul _)

private theorem layerFaceInt_odd (s : Nat) : Odd (layerFaceInt s) := by
  unfold layerFaceInt
  exact odd_sum_nine (spinCode_odd _ _) (spinCode_odd _ _)
    (spinCode_odd _ _) (spinCode_odd _ _) (spinCode_odd _ _)
    (spinCode_odd _ _) (spinCode_odd _ _) (spinCode_odd _ _)
    (spinCode_odd _ _)

private theorem layerDotInt_odd (s t : Nat) : Odd (layerDotInt s t) := by
  unfold layerDotInt
  apply odd_sum_nine <;> exact (spinCode_odd _ _).mul (spinCode_odd _ _)

theorem layerLateralInt_halfShift (s : Fin 512) :
    2 * halfShift (layerLateralInt s) 16 = layerLateralInt s + 16 := by
  unfold halfShift
  exact Int.two_mul_ediv_two_of_even ((layerLateralInt_even s).add (by norm_num))

theorem layerEndpointInt_halfShift (q : Fin 512) :
    2 * halfShift (layerLateralInt q + layerFaceInt q) 17 =
      layerLateralInt q + layerFaceInt q + 17 := by
  unfold halfShift
  exact Int.two_mul_ediv_two_of_even
    ((layerLateralInt_even q).add_odd (layerFaceInt_odd q) |>.add_odd (by norm_num))

theorem layerSeamInt_halfShift (s q : Fin 512) :
    2 * halfShift (layerDotInt s q) 9 = layerDotInt s q + 9 := by
  unfold halfShift
  exact Int.two_mul_ediv_two_of_even
    ((layerDotInt_odd s q).add_odd (by norm_num))

theorem layerMiddleInt_halfShift (s v : Fin 512) :
    2 * halfShift
        (layerDotInt s v + layerLateralInt v + layerFaceInt v) 26 =
      layerDotInt s v + layerLateralInt v + layerFaceInt v + 26 := by
  unfold halfShift
  exact Int.two_mul_ediv_two_of_even
    (((layerDotInt_odd s v).add_even (layerLateralInt_even v)).add_odd
      (layerFaceInt_odd v) |>.add (by norm_num))

private theorem eval_rawMomentDirectBlock (X Y : Real)
    (start count : Nat) :
    (rawMomentDirectBlock start count).eval X Y =
      ((List.range count).map fun offset =>
        (rawMomentStatePoly (start + offset)).eval X Y).sum := by
  unfold rawMomentDirectBlock
  rw [eval_foldl_add_apply]
  simp

private theorem list_range_mul_sum_blocks (f : Nat -> Real)
    (blocks width : Nat) :
    ((List.range (blocks * width)).map f).sum =
      ((List.range blocks).map fun block =>
        ((List.range width).map fun offset =>
          f (block * width + offset)).sum).sum := by
  induction blocks with
  | zero => simp
  | succ blocks ih =>
      rw [Nat.succ_mul, List.range_add, List.map_append,
        List.sum_append, ih]
      simp [List.range_succ, Function.comp_def]

private theorem eval_rawMomentPolyStateSum_eq_fin_sum (X Y : Real) :
    rawMomentPolyStateSum.eval X Y =
      ∑ s : Fin 512, (rawMomentStatePoly s).eval X Y := by
  calc
    rawMomentPolyStateSum.eval X Y =
        ((List.range 256).map fun block =>
          (rawMomentDirectBlock (2 * block) 2).eval X Y).sum := by
      unfold rawMomentPolyStateSum
      rw [eval_foldl_add_apply]
      simp
    _ = ((List.range 256).map fun block =>
          ((List.range 2).map fun offset =>
            (rawMomentStatePoly (block * 2 + offset)).eval X Y).sum).sum := by
      apply congrArg List.sum
      apply List.map_congr_left
      intro block hblock
      rw [eval_rawMomentDirectBlock]
      simp only [Nat.mul_comm]
    _ = ((List.range (256 * 2)).map fun s =>
          (rawMomentStatePoly s).eval X Y).sum := by
      rw [list_range_mul_sum_blocks]
    _ = ∑ s : Fin 512, (rawMomentStatePoly s).eval X Y := by
      norm_num
      rw [list_range_sum_eq_finset_range_sum]
      exact (Fin.sum_univ_eq_sum_range
        (fun s : Nat => (rawMomentStatePoly s).eval X Y) 512).symm

set_option maxRecDepth 10000 in


theorem eval_rawMomentPolyStateSum (X Y : Real)
    (hX : X ≠ 0) (hY : Y ≠ 0) :
    rawMomentPolyStateSum.eval X Y =
      ∑ s : Fin 512,
        X ^ halfShift (layerLateralInt s) 16 *
          (∑ v : Fin 512,
            X ^ halfShift
              (layerDotInt s v + layerLateralInt v + layerFaceInt v) 26) *
          (∑ q : Fin 512,
            X ^ halfShift (layerLateralInt q + layerFaceInt q) 17 *
              Y ^ halfShift (layerDotInt s q) 9) := by
  rw [eval_rawMomentPolyStateSum_eq_fin_sum]
  apply Finset.sum_congr rfl
  intro s _
  unfold rawMomentStatePoly
  rw [BiPoly.eval_mul X Y hX hY, BiPoly.eval_mul X Y hX hY,
    BiPoly.eval_monomial, BiPoly.eval_sumCodes_eq_fin_sum,
    BiPoly.eval_sumCodes_eq_fin_sum]
  simp only [BiPoly.eval_monomial, Int.cast_one, one_mul, zpow_zero,
    mul_one]

private theorem real_exp_zpow (x : Real) (z : Int) :
    Real.exp x ^ z = Real.exp ((z : Real) * x) := by
  cases z with
  | ofNat n =>
      change Real.exp x ^ (n : Int) = Real.exp ((n : Real) * x)
      rw [zpow_natCast, ← Real.exp_nat_mul]
  | negSucc n =>
      rw [zpow_negSucc, ← Real.exp_nat_mul, ← Real.exp_neg]
      congr 1
      push_cast
      ring

private noncomputable def normalizedTermWeight (X : Real) (t : BiTerm) : Real :=
  (t.coeff : Real) * X ^ t.ex

private noncomputable def normalizedTermInteraction (t : BiTerm) : Real :=
  (2 * t.ey - 9 : Int)

private theorem normalized_BiTerm_eval_eq (X r : Real) (t : BiTerm) :
    Real.exp (-9 * r) * t.eval X (Real.exp (2 * r)) =
      normalizedTermWeight X t *
        Real.exp (r * normalizedTermInteraction t) := by
  have hexp :
      Real.exp (-9 * r) *
          Real.exp ((t.ey : Real) * (2 * r)) =
        Real.exp (r * normalizedTermInteraction t) := by
    rw [← Real.exp_add]
    congr 1
    unfold normalizedTermInteraction
    push_cast
    ring
  unfold BiTerm.eval normalizedTermWeight
  rw [real_exp_zpow]
  calc
    Real.exp (-9 * r) *
        ((t.coeff : Real) * X ^ t.ex *
          Real.exp ((t.ey : Real) * (2 * r))) =
      (t.coeff : Real) * X ^ t.ex *
        (Real.exp (-9 * r) *
          Real.exp ((t.ey : Real) * (2 * r))) := by ring
    _ = (t.coeff : Real) * X ^ t.ex *
        Real.exp (r * normalizedTermInteraction t) := by rw [hexp]

private theorem hasDerivAt_normalizedTermSum
    (X r : Real) (ts : List BiTerm) :
    HasDerivAt
      (fun u => (ts.map fun t => normalizedTermWeight X t *
        Real.exp (u * normalizedTermInteraction t)).sum)
      ((ts.map fun t => normalizedTermWeight X t *
        (normalizedTermInteraction t *
          Real.exp (r * normalizedTermInteraction t))).sum) r := by
  induction ts with
  | nil => simpa using hasDerivAt_const (x := r) (c := (0 : Real))
  | cons t ts ih =>
      simp only [List.map_cons, List.sum_cons]
      exact (hasDerivAt_weightedSeamExp
        (normalizedTermWeight X t) (normalizedTermInteraction t) r).add ih

private theorem normalized_scaleObservable_eval
    (X r : Real) (p : BiPoly) (power : Nat) :
    Real.exp (-9 * r) *
        (p.scaleObservable power).eval X (Real.exp (2 * r)) =
      (p.terms.map fun t => normalizedTermWeight X t *
        (normalizedTermInteraction t ^ power *
          Real.exp (r * normalizedTermInteraction t))).sum := by
  rw [BiPoly.eval_scaleObservable, ← List.sum_map_mul_left]
  apply congrArg List.sum
  apply List.map_congr_left
  intro t ht
  have h := normalized_BiTerm_eval_eq X r t
  calc
    Real.exp (-9 * r) *
        (((t.coeff * (2 * t.ey - 9) ^ power : Int) : Real) *
          X ^ t.ex * Real.exp (2 * r) ^ t.ey) =
      normalizedTermInteraction t ^ power *
        (Real.exp (-9 * r) * t.eval X (Real.exp (2 * r))) := by
          unfold BiTerm.eval normalizedTermInteraction
          push_cast
          ring
    _ = normalizedTermInteraction t ^ power *
        (normalizedTermWeight X t *
          Real.exp (r * normalizedTermInteraction t)) := by rw [h]
    _ = normalizedTermWeight X t *
        (normalizedTermInteraction t ^ power *
          Real.exp (r * normalizedTermInteraction t)) := by ring

private theorem normalized_scaleObservable_one_eval
    (X r : Real) (p : BiPoly) :
    Real.exp (-9 * r) *
        (p.scaleObservable 1).eval X (Real.exp (2 * r)) =
      (p.terms.map fun t => normalizedTermWeight X t *
        (normalizedTermInteraction t *
          Real.exp (r * normalizedTermInteraction t))).sum := by
  simpa only [pow_one] using normalized_scaleObservable_eval X r p 1

theorem BiPoly.hasDerivAt_normalizedSeamEval
    (X r : Real) (p : BiPoly) :
    HasDerivAt
      (fun u => Real.exp (-9 * u) *
        p.eval X (Real.exp (2 * u)))
      (Real.exp (-9 * r) *
        (p.scaleObservable 1).eval X (Real.exp (2 * r))) r := by
  have h := hasDerivAt_normalizedTermSum X r p.terms
  rw [normalized_scaleObservable_one_eval]
  convert h using 1
  funext u
  unfold BiPoly.eval
  rw [← List.sum_map_mul_left]
  apply congrArg List.sum
  apply List.map_congr_left
  intro t ht
  exact normalized_BiTerm_eval_eq X u t

private theorem hasDerivAt_normalizedTermFirstSum
    (X r : Real) (ts : List BiTerm) :
    HasDerivAt
      (fun u => (ts.map fun t => normalizedTermWeight X t *
        (normalizedTermInteraction t *
          Real.exp (u * normalizedTermInteraction t))).sum)
      ((ts.map fun t => normalizedTermWeight X t *
        (normalizedTermInteraction t ^ 2 *
          Real.exp (r * normalizedTermInteraction t))).sum) r := by
  induction ts with
  | nil => simpa using hasDerivAt_const (x := r) (c := (0 : Real))
  | cons t ts ih =>
      simp only [List.map_cons, List.sum_cons]
      exact (hasDerivAt_weightedSeamFirst
        (normalizedTermWeight X t) (normalizedTermInteraction t) r).add ih

theorem BiPoly.hasDerivAt_normalizedSeamFirstEval
    (X r : Real) (p : BiPoly) :
    HasDerivAt
      (fun u => Real.exp (-9 * u) *
        (p.scaleObservable 1).eval X (Real.exp (2 * u)))
      (Real.exp (-9 * r) *
        (p.scaleObservable 2).eval X (Real.exp (2 * r))) r := by
  have h := hasDerivAt_normalizedTermFirstSum X r p.terms
  rw [normalized_scaleObservable_eval X r p 2]
  convert h using 1
  funext u
  exact normalized_scaleObservable_one_eval X u p

theorem exp_nOneWeight_eq_normalizedMonomial
    (beta r : Real) (s v q : Fin 512) :
    Real.exp (beta *
        ((layerLateralInt s : Real) + layerDotInt s v +
          layerLateralInt v + layerFaceInt v +
          layerLateralInt q + layerFaceInt q) +
      r * (layerDotInt s q : Real)) =
      Real.exp (-59 * beta - 9 * r) *
        Real.exp (2 * beta) ^ halfShift (layerLateralInt s) 16 *
        Real.exp (2 * beta) ^ halfShift
          (layerDotInt s v + layerLateralInt v + layerFaceInt v) 26 *
        Real.exp (2 * beta) ^ halfShift
          (layerLateralInt q + layerFaceInt q) 17 *
        Real.exp (2 * r) ^ halfShift (layerDotInt s q) 9 := by
  have hs := layerLateralInt_halfShift s
  have hv := layerMiddleInt_halfShift s v
  have hq := layerEndpointInt_halfShift q
  have hsq := layerSeamInt_halfShift s q
  have hsR :
      2 * (halfShift (layerLateralInt s) 16 : Real) =
        (layerLateralInt s : Real) + 16 := by
    exact_mod_cast hs
  have hvR :
      2 * (halfShift
        (layerDotInt s v + layerLateralInt v + layerFaceInt v) 26 : Real) =
        (layerDotInt s v : Real) + layerLateralInt v +
          layerFaceInt v + 26 := by
    exact_mod_cast hv
  have hqR :
      2 * (halfShift (layerLateralInt q + layerFaceInt q) 17 : Real) =
        (layerLateralInt q : Real) + layerFaceInt q + 17 := by
    exact_mod_cast hq
  have hsqR :
      2 * (halfShift (layerDotInt s q) 9 : Real) =
        (layerDotInt s q : Real) + 9 := by
    exact_mod_cast hsq
  rw [real_exp_zpow, real_exp_zpow, real_exp_zpow, real_exp_zpow,
    ← Real.exp_add, ← Real.exp_add, ← Real.exp_add,
    ← Real.exp_add]
  congr 1
  linear_combination -beta * hsR - beta * hvR - beta * hqR - r * hsqR

private theorem sum_sum_separable
    {S V Q : Type*} [Fintype S] [Fintype V] [Fintype Q]
    (c : Real) (A : S -> Real) (B : S -> V -> Real)
    (C : S -> Q -> Real) :
    (∑ s : S, ∑ q : Q, ∑ v : V, c * A s * B s v * C s q) =
      c * ∑ s : S, A s * (∑ v : V, B s v) * (∑ q : Q, C s q) := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s _
  calc
    (∑ q : Q, ∑ v : V, c * A s * B s v * C s q) =
        ∑ q : Q, c * A s * (∑ v : V, B s v) * C s q := by
      apply Finset.sum_congr rfl
      intro q _
      rw [Finset.mul_sum, Finset.sum_mul]
    _ = c * (A s * (∑ v : V, B s v) * (∑ q : Q, C s q)) := by
      rw [← Finset.mul_sum]
      ring

set_option maxRecDepth 10000 in


theorem nOneTransferBridgeRawMomentCodeSum_eq_eval_stateSum
    (beta r : Real) :
    nOneTransferBridgeRawMomentCodeSum beta r =
      Real.exp (-59 * beta - 9 * r) *
        rawMomentPolyStateSum.eval (Real.exp (2 * beta))
          (Real.exp (2 * r)) := by
  unfold nOneTransferBridgeRawMomentCodeSum
  rw [eval_rawMomentPolyStateSum (Real.exp (2 * beta))
    (Real.exp (2 * r)) (Real.exp_ne_zero _) (Real.exp_ne_zero _)]
  simp_rw [exp_nOneWeight_eq_normalizedMonomial]
  simpa only [mul_assoc] using (sum_sum_separable
    (Real.exp (-59 * beta - 9 * r))
    (fun s : Fin 512 =>
      Real.exp (2 * beta) ^ halfShift (layerLateralInt s) 16)
    (fun s v : Fin 512 => Real.exp (2 * beta) ^ halfShift
      (layerDotInt s v + layerLateralInt v + layerFaceInt v) 26)
    (fun s q : Fin 512 =>
      Real.exp (2 * beta) ^
          halfShift (layerLateralInt q + layerFaceInt q) 17 *
        Real.exp (2 * r) ^ halfShift (layerDotInt s q) 9))

theorem oddPrismTransferBridgeRawMoment_one_eq_eval_stateSum
    (beta r : Real) :
    oddPrismTransferBridgeRawMoment beta 1 r =
      Real.exp (-59 * beta - 9 * r) *
        rawMomentPolyStateSum.eval (Real.exp (2 * beta))
          (Real.exp (2 * r)) := by
  rw [oddPrismTransferBridgeRawMoment_one_eq_codeSum,
    nOneTransferBridgeRawMomentCodeSum_eq_eval_stateSum]

private theorem BiPoly.hasDerivAt_fullNormalizedSeamEval
    (beta r : Real) (p : BiPoly) :
    HasDerivAt
      (fun u => Real.exp (-59 * beta - 9 * u) *
        p.eval (Real.exp (2 * beta)) (Real.exp (2 * u)))
      (Real.exp (-59 * beta - 9 * r) *
        (p.scaleObservable 1).eval (Real.exp (2 * beta))
          (Real.exp (2 * r))) r := by
  have h := (p.hasDerivAt_normalizedSeamEval
    (Real.exp (2 * beta)) r).const_mul (Real.exp (-59 * beta))
  convert h using 1
  · funext u
    rw [show -59 * beta - 9 * u = -59 * beta + (-9 * u) by ring,
      Real.exp_add]
    ring
  · rw [show -59 * beta - 9 * r = -59 * beta + (-9 * r) by ring,
      Real.exp_add]
    ring

private theorem BiPoly.hasDerivAt_fullNormalizedSeamFirstEval
    (beta r : Real) (p : BiPoly) :
    HasDerivAt
      (fun u => Real.exp (-59 * beta - 9 * u) *
        (p.scaleObservable 1).eval (Real.exp (2 * beta))
          (Real.exp (2 * u)))
      (Real.exp (-59 * beta - 9 * r) *
        (p.scaleObservable 2).eval (Real.exp (2 * beta))
          (Real.exp (2 * r))) r := by
  have h := (p.hasDerivAt_normalizedSeamFirstEval
    (Real.exp (2 * beta)) r).const_mul (Real.exp (-59 * beta))
  convert h using 1
  · funext u
    rw [show -59 * beta - 9 * u = -59 * beta + (-9 * u) by ring,
      Real.exp_add]
    ring
  · rw [show -59 * beta - 9 * r = -59 * beta + (-9 * r) by ring,
      Real.exp_add]
    ring

theorem oddPrismTransferBridgeRawFirst_one_eq_eval_stateSum
    (beta r : Real) :
    oddPrismTransferBridgeRawFirst beta 1 r =
      Real.exp (-59 * beta - 9 * r) *
        (rawMomentPolyStateSum.scaleObservable 1).eval
          (Real.exp (2 * beta)) (Real.exp (2 * r)) := by
  have hraw : HasDerivAt
      (fun u => Real.exp (-59 * beta - 9 * u) *
        rawMomentPolyStateSum.eval (Real.exp (2 * beta))
          (Real.exp (2 * u)))
      (oddPrismTransferBridgeRawFirst beta 1 r) r := by
    convert hasDerivAt_oddPrismTransferBridgeRawMoment beta 1 r using 1
    funext u
    exact (oddPrismTransferBridgeRawMoment_one_eq_eval_stateSum beta u).symm
  exact hraw.unique
    (rawMomentPolyStateSum.hasDerivAt_fullNormalizedSeamEval beta r)

theorem oddPrismTransferBridgeRawSecond_one_eq_eval_stateSum
    (beta r : Real) :
    oddPrismTransferBridgeRawSecond beta 1 r =
      Real.exp (-59 * beta - 9 * r) *
        (rawMomentPolyStateSum.scaleObservable 2).eval
          (Real.exp (2 * beta)) (Real.exp (2 * r)) := by
  have hraw : HasDerivAt
      (fun u => Real.exp (-59 * beta - 9 * u) *
        (rawMomentPolyStateSum.scaleObservable 1).eval
          (Real.exp (2 * beta)) (Real.exp (2 * u)))
      (oddPrismTransferBridgeRawSecond beta 1 r) r := by
    convert hasDerivAt_oddPrismTransferBridgeRawFirst beta 1 r using 1
    funext u
    exact (oddPrismTransferBridgeRawFirst_one_eq_eval_stateSum beta u).symm
  exact hraw.unique
    (rawMomentPolyStateSum.hasDerivAt_fullNormalizedSeamFirstEval beta r)

theorem BiPoly.eval_varianceNumeratorPolyOf
    (p : BiPoly) (X Y : Real) (hX : X ≠ 0) (hY : Y ≠ 0) :
    (varianceNumeratorPolyOf p).eval X Y =
      (p.scaleObservable 2).eval X Y * p.eval X Y -
        (p.scaleObservable 1).eval X Y ^ 2 := by
  unfold varianceNumeratorPolyOf
  rw [BiPoly.eval_sub, BiPoly.eval_mul X Y hX hY,
    BiPoly.eval_mul X Y hX hY]
  ring

theorem BiPoly.eval_reflectedVarianceSkewPolyOf
    (p : BiPoly) (X Y : Real) (hX : X ≠ 0) (hY : Y ≠ 0) :
    (reflectedVarianceSkewPolyOf p).eval X Y =
      (varianceNumeratorPolyOf p).eval X Y * p.eval X Y⁻¹ ^ 2 -
        (varianceNumeratorPolyOf p).eval X Y⁻¹ * p.eval X Y ^ 2 := by
  unfold reflectedVarianceSkewPolyOf
  rw [BiPoly.eval_sub, BiPoly.eval_mul X Y hX hY,
    BiPoly.eval_mul X Y hX hY, BiPoly.eval_mul X Y hX hY,
    BiPoly.eval_mul X Y hX hY, BiPoly.eval_flipY,
    BiPoly.eval_flipY]
  ring

theorem oddPrismTransferBridgeVarianceNumerator_one_eq_eval_stateSum
    (beta r : Real) :
    oddPrismTransferBridgeVarianceNumerator beta 1 r =
      Real.exp (-59 * beta - 9 * r) ^ 2 *
        (varianceNumeratorPolyOf rawMomentPolyStateSum).eval
          (Real.exp (2 * beta)) (Real.exp (2 * r)) := by
  unfold oddPrismTransferBridgeVarianceNumerator
  rw [oddPrismTransferBridgeRawMoment_one_eq_eval_stateSum,
    oddPrismTransferBridgeRawFirst_one_eq_eval_stateSum,
    oddPrismTransferBridgeRawSecond_one_eq_eval_stateSum,
    BiPoly.eval_varianceNumeratorPolyOf _ _ _
      (Real.exp_ne_zero _) (Real.exp_ne_zero _)]
  ring

theorem oddPrismTransferBridgeVarianceSkewNumerator_one_eq_eval_stateSum
    (beta r : Real) :
    oddPrismTransferBridgeVarianceSkewNumerator beta 1 r =
      (Real.exp (-59 * beta - 9 * r) *
        Real.exp (-59 * beta + 9 * r)) ^ 2 *
        (reflectedVarianceSkewPolyOf rawMomentPolyStateSum).eval
          (Real.exp (2 * beta)) (Real.exp (2 * r)) := by
  have hnegY : (Real.exp (2 * r))⁻¹ = Real.exp (2 * (-r)) := by
    rw [← Real.exp_neg]
    congr 1
    ring
  unfold oddPrismTransferBridgeVarianceSkewNumerator
  rw [oddPrismTransferBridgeVarianceNumerator_one_eq_eval_stateSum,
    oddPrismTransferBridgeVarianceNumerator_one_eq_eval_stateSum,
    oddPrismTransferBridgeRawMoment_one_eq_eval_stateSum,
    oddPrismTransferBridgeRawMoment_one_eq_eval_stateSum,
    BiPoly.eval_reflectedVarianceSkewPolyOf _ _ _
      (Real.exp_ne_zero _) (Real.exp_ne_zero _), hnegY]
  ring

set_option maxRecDepth 10000 in


theorem nOneTransferBridgeRawMomentCodeSum_eq_eval_rawMomentPoly
    (beta r : Real) :
    nOneTransferBridgeRawMomentCodeSum beta r =
      Real.exp (-59 * beta - 9 * r) *
        rawMomentPoly.eval (Real.exp (2 * beta))
          (Real.exp (2 * r)) := by
  unfold nOneTransferBridgeRawMomentCodeSum
  rw [BiPoly.eval_rawMomentPoly_eq_fin_stateSum
    (Real.exp (2 * beta)) (Real.exp (2 * r)) (Real.exp_ne_zero _)]
  simp_rw [exp_nOneWeight_eq_normalizedMonomial]
  simpa only [mul_assoc] using (sum_sum_separable
    (Real.exp (-59 * beta - 9 * r))
    (fun s : Fin 512 =>
      Real.exp (2 * beta) ^ halfShift (layerLateralInt s) 16)
    (fun s v : Fin 512 => Real.exp (2 * beta) ^ halfShift
      (layerDotInt s v + layerLateralInt v + layerFaceInt v) 26)
    (fun s q : Fin 512 =>
      Real.exp (2 * beta) ^
          halfShift (layerLateralInt q + layerFaceInt q) 17 *
        Real.exp (2 * r) ^ halfShift (layerDotInt s q) 9))

theorem oddPrismTransferBridgeRawMoment_one_eq_eval_rawMomentPoly
    (beta r : Real) :
    oddPrismTransferBridgeRawMoment beta 1 r =
      Real.exp (-59 * beta - 9 * r) *
        rawMomentPoly.eval (Real.exp (2 * beta))
          (Real.exp (2 * r)) := by
  rw [oddPrismTransferBridgeRawMoment_one_eq_codeSum,
    nOneTransferBridgeRawMomentCodeSum_eq_eval_rawMomentPoly]

theorem oddPrismTransferBridgeRawFirst_one_eq_eval_rawMomentPoly
    (beta r : Real) :
    oddPrismTransferBridgeRawFirst beta 1 r =
      Real.exp (-59 * beta - 9 * r) *
        (rawMomentPoly.scaleObservable 1).eval
          (Real.exp (2 * beta)) (Real.exp (2 * r)) := by
  have hraw : HasDerivAt
      (fun u => Real.exp (-59 * beta - 9 * u) *
        rawMomentPoly.eval (Real.exp (2 * beta))
          (Real.exp (2 * u)))
      (oddPrismTransferBridgeRawFirst beta 1 r) r := by
    convert hasDerivAt_oddPrismTransferBridgeRawMoment beta 1 r using 1
    funext u
    exact (oddPrismTransferBridgeRawMoment_one_eq_eval_rawMomentPoly beta u).symm
  exact hraw.unique
    (rawMomentPoly.hasDerivAt_fullNormalizedSeamEval beta r)

theorem oddPrismTransferBridgeRawSecond_one_eq_eval_rawMomentPoly
    (beta r : Real) :
    oddPrismTransferBridgeRawSecond beta 1 r =
      Real.exp (-59 * beta - 9 * r) *
        (rawMomentPoly.scaleObservable 2).eval
          (Real.exp (2 * beta)) (Real.exp (2 * r)) := by
  have hraw : HasDerivAt
      (fun u => Real.exp (-59 * beta - 9 * u) *
        (rawMomentPoly.scaleObservable 1).eval
          (Real.exp (2 * beta)) (Real.exp (2 * u)))
      (oddPrismTransferBridgeRawSecond beta 1 r) r := by
    convert hasDerivAt_oddPrismTransferBridgeRawFirst beta 1 r using 1
    funext u
    exact (oddPrismTransferBridgeRawFirst_one_eq_eval_rawMomentPoly beta u).symm
  exact hraw.unique
    (rawMomentPoly.hasDerivAt_fullNormalizedSeamFirstEval beta r)

theorem oddPrismTransferBridgeVarianceNumerator_one_eq_eval_rawMomentPoly
    (beta r : Real) :
    oddPrismTransferBridgeVarianceNumerator beta 1 r =
      Real.exp (-59 * beta - 9 * r) ^ 2 *
        varianceNumeratorPoly.eval
          (Real.exp (2 * beta)) (Real.exp (2 * r)) := by
  unfold oddPrismTransferBridgeVarianceNumerator varianceNumeratorPoly
  rw [oddPrismTransferBridgeRawMoment_one_eq_eval_rawMomentPoly,
    oddPrismTransferBridgeRawFirst_one_eq_eval_rawMomentPoly,
    oddPrismTransferBridgeRawSecond_one_eq_eval_rawMomentPoly,
    BiPoly.eval_varianceNumeratorPolyOf _ _ _
      (Real.exp_ne_zero _) (Real.exp_ne_zero _)]
  ring

theorem oddPrismTransferBridgeVarianceSkewNumerator_one_eq_eval_rawMomentPoly
    (beta r : Real) :
    oddPrismTransferBridgeVarianceSkewNumerator beta 1 r =
      (Real.exp (-59 * beta - 9 * r) *
        Real.exp (-59 * beta + 9 * r)) ^ 2 *
        reflectedVarianceSkewPoly.eval
          (Real.exp (2 * beta)) (Real.exp (2 * r)) := by
  have hnegY : (Real.exp (2 * r))⁻¹ = Real.exp (2 * (-r)) := by
    rw [← Real.exp_neg]
    congr 1
    ring
  unfold oddPrismTransferBridgeVarianceSkewNumerator reflectedVarianceSkewPoly
  rw [oddPrismTransferBridgeVarianceNumerator_one_eq_eval_rawMomentPoly,
    oddPrismTransferBridgeVarianceNumerator_one_eq_eval_rawMomentPoly,
    oddPrismTransferBridgeRawMoment_one_eq_eval_rawMomentPoly,
    oddPrismTransferBridgeRawMoment_one_eq_eval_rawMomentPoly,
    BiPoly.eval_reflectedVarianceSkewPolyOf _ _ _
      (Real.exp_ne_zero _) (Real.exp_ne_zero _), hnegY]
  unfold varianceNumeratorPoly
  ring

end StatMech.FrontierA.NOneSymmetricMeanCertificate
