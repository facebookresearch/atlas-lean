/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierA.IsingSurfaceTensionNOnePolynomialSemantics









namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

noncomputable def weightedListEval (weight : Nat -> Real) : List Int -> Real
  | [] => 0
  | coefficient :: coefficients =>
      (coefficient : Real) * weight 0 +
        weightedListEval (fun i => weight (i + 1)) coefficients

@[simp] theorem weightedListEval_nil (weight : Nat -> Real) :
    weightedListEval weight [] = 0 := rfl

@[simp] theorem weightedListEval_cons (weight : Nat -> Real)
    (coefficient : Int) (coefficients : List Int) :
    weightedListEval weight (coefficient :: coefficients) =
      (coefficient : Real) * weight 0 +
        weightedListEval (fun i => weight (i + 1)) coefficients := rfl

theorem updateCoefficient_length (coefficients : List Int) (i : Nat)
    (f : Int -> Int) :
    (updateCoefficient coefficients i f).length = coefficients.length := by
  induction coefficients generalizing i with
  | nil => simp [updateCoefficient]
  | cons coefficient coefficients ih =>
      cases i <;> simp [updateCoefficient, ih]

theorem weightedListEval_update_add (weight : Nat -> Real)
    (coefficients : List Int) (i : Nat) (delta : Int)
    (hi : i < coefficients.length) :
    weightedListEval weight
        (updateCoefficient coefficients i (fun c => c + delta)) =
      weightedListEval weight coefficients + (delta : Real) * weight i := by
  induction coefficients generalizing i weight with
  | nil => simp at hi
  | cons coefficient coefficients ih =>
      cases i with
      | zero =>
          simp [updateCoefficient, weightedListEval]
          ring
      | succ i =>
          have hi' : i < coefficients.length := by simpa using hi
          simp only [updateCoefficient, weightedListEval]
          rw [ih (fun j => weight (j + 1)) i hi']
          push_cast
          ring

theorem weightedListEval_foldl_update
    {alpha : Type*} (weight : Nat -> Real) (xs : List alpha)
    (coefficients : List Int) (index : alpha -> Nat)
    (delta : alpha -> Int)
    (hindex : ∀ x ∈ xs, index x < coefficients.length) :
    weightedListEval weight
        (xs.foldl (fun out x =>
          updateCoefficient out (index x) (fun c => c + delta x))
          coefficients) =
      weightedListEval weight coefficients +
        (xs.map fun x => (delta x : Real) * weight (index x)).sum := by
  induction xs generalizing coefficients with
  | nil => simp
  | cons x xs ih =>
      have hx : index x < coefficients.length := hindex x (by simp)
      have htail : ∀ y ∈ xs,
          index y <
            (updateCoefficient coefficients (index x)
              (fun c => c + delta x)).length := by
        intro y hy
        rw [updateCoefficient_length]
        exact hindex y (by simp [hy])
      simp only [List.foldl_cons, List.map_cons, List.sum_cons]
      rw [ih _ htail,
        weightedListEval_update_add weight coefficients (index x)
          (delta x) hx]
      ring

theorem weightedListEval_replicate_zero (weight : Nat -> Real) (n : Nat) :
    weightedListEval weight (List.replicate n 0) = 0 := by
  induction n generalizing weight with
  | zero => simp
  | succ n ih =>
      rw [List.replicate_succ, weightedListEval_cons, ih]
      norm_num

theorem weightedListEval_eq_sum_getD (weight : Nat -> Real)
    (coefficients : List Int) :
    weightedListEval weight coefficients =
      ∑ i ∈ Finset.range coefficients.length,
        (coefficients.getD i 0 : Real) * weight i := by
  induction coefficients generalizing weight with
  | nil => simp
  | cons coefficient coefficients ih =>
      rw [weightedListEval_cons, ih]
      simp only [List.length_cons, Finset.sum_range_succ',
        List.getD_cons_zero,
        List.getD_cons_succ]
      ring

theorem foldl_length_of_step {alpha : Type*} (xs : List alpha)
    (step : List Int -> alpha -> List Int) (coefficients : List Int)
    (hstep : ∀ out x, (step out x).length = out.length) :
    (xs.foldl step coefficients).length = coefficients.length := by
  induction xs generalizing coefficients with
  | nil => rfl
  | cons x xs ih =>
      rw [List.foldl_cons, ih]
      exact hstep coefficients x

theorem foldl_length_of_invariant {alpha : Type*} (xs : List alpha)
    (step : List Int -> alpha -> List Int) (coefficients : List Int) (n : Nat)
    (hlength : coefficients.length = n)
    (hstep : ∀ out x, out.length = n -> (step out x).length = n) :
    (xs.foldl step coefficients).length = n := by
  induction xs generalizing coefficients with
  | nil => exact hlength
  | cons x xs ih =>
      rw [List.foldl_cons]
      exact ih _ (hstep coefficients x hlength)

theorem weightedListEval_foldl_additive {alpha : Type*}
    (weight : Nat -> Real) (xs : List alpha)
    (step : List Int -> alpha -> List Int) (contribution : alpha -> Real)
    (coefficients : List Int)
    (hstep : ∀ out x, weightedListEval weight (step out x) =
      weightedListEval weight out + contribution x) :
    weightedListEval weight (xs.foldl step coefficients) =
      weightedListEval weight coefficients +
        (xs.map contribution).sum := by
  induction xs generalizing coefficients with
  | nil => simp
  | cons x xs ih =>
      rw [List.foldl_cons, ih, hstep]
      simp only [List.map_cons, List.sum_cons]
      ring

theorem weightedListEval_foldl_additive_of_length {alpha : Type*}
    (weight : Nat -> Real) (xs : List alpha)
    (step : List Int -> alpha -> List Int) (contribution : alpha -> Real)
    (valid : alpha -> Prop) (coefficients : List Int) (n : Nat)
    (hlength : coefficients.length = n)
    (hvalid : ∀ x ∈ xs, valid x)
    (hstepLength : ∀ out x, out.length = n -> (step out x).length = n)
    (hstepEval : ∀ out x, valid x -> out.length = n ->
      weightedListEval weight (step out x) =
        weightedListEval weight out + contribution x) :
    weightedListEval weight (xs.foldl step coefficients) =
      weightedListEval weight coefficients +
        (xs.map contribution).sum := by
  induction xs generalizing coefficients with
  | nil => simp
  | cons x xs ih =>
      have hnext : (step coefficients x).length = n := by
        exact hstepLength coefficients x hlength
      have hx : valid x := hvalid x (by simp)
      have htail : ∀ y ∈ xs, valid y := by
        intro y hy
        exact hvalid y (by simp [hy])
      rw [List.foldl_cons, ih _ hnext htail,
        hstepEval _ _ hx hlength]
      simp only [List.map_cons, List.sum_cons]
      ring

private theorem list_range_sum_eq_finset_range_sum
    (f : Nat -> Real) (n : Nat) :
    ((List.range n).map f).sum = ∑ i ∈ Finset.range n, f i := by
  induction n with
  | zero => simp
  | succ n ih => simp [List.range_succ, ih, Finset.sum_range_succ]

theorem weightedListEval_eq_list_sum_getD (weight : Nat -> Real)
    (coefficients : List Int) :
    weightedListEval weight coefficients =
      ((List.range coefficients.length).map fun i =>
        (coefficients.getD i 0 : Real) * weight i).sum := by
  rw [weightedListEval_eq_sum_getD,
    list_range_sum_eq_finset_range_sum]

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

private theorem list_range_add_sum (f : Nat -> Real) (m n : Nat) :
    ((List.range (m + n)).map f).sum =
      ((List.range m).map f).sum +
        ((List.range n).map fun i => f (m + i)).sum := by
  rw [List.range_add, List.map_append, List.sum_append]
  simp [Function.comp_def]

private noncomputable def denseMomentWeight (X Y : Real) (index : Nat) : Real :=
  X ^ ((index / 10 : Nat) : Int) *
    Y ^ ((index % 10 : Nat) : Int)

private def addRawMomentInteractions (out : List Int) (se : Nat)
    (vCount qCount : List Int) (ev eq : Nat) : List Int :=
  (List.range 10).foldl (fun out iq =>
    let coefficient := vCount.getD ev 0 * qCount.getD (10 * eq + iq) 0
    let index := 10 * (se + ev + eq) + iq
    updateCoefficient out index (fun z => z + coefficient)) out

private def addRawMomentEndpoints (out : List Int) (se : Nat)
    (vCount qCount : List Int) (ev : Nat) : List Int :=
  (List.range 26).foldl (fun out eq =>
    addRawMomentInteractions out se vCount qCount ev eq) out

private def addRawMomentVStates (out : List Int) (se : Nat)
    (vCount qCount : List Int) : List Int :=
  (List.range 35).foldl (fun out ev =>
    addRawMomentEndpoints out se vCount qCount ev) out

private theorem addRawMomentState_eq_addRawMomentVStates
    (out : List Int) (s : Nat) :
    addRawMomentState out s =
      addRawMomentVStates out
        (Int.toNat (halfShift (layerLateralInt s) 16))
        (rawMomentVCounts s) (rawMomentQCounts s) := by
  rfl

private theorem addRawMomentInteractions_length (out : List Int) (se : Nat)
    (vCount qCount : List Int) (ev eq : Nat) :
    (addRawMomentInteractions out se vCount qCount ev eq).length =
      out.length := by
  unfold addRawMomentInteractions
  apply foldl_length_of_step
  intro coefficients iq
  exact updateCoefficient_length _ _ _

private theorem addRawMomentEndpoints_length (out : List Int) (se : Nat)
    (vCount qCount : List Int) (ev : Nat) :
    (addRawMomentEndpoints out se vCount qCount ev).length =
      out.length := by
  unfold addRawMomentEndpoints
  apply foldl_length_of_step
  intro coefficients eq
  exact addRawMomentInteractions_length _ _ _ _ _ _

private theorem addRawMomentVStates_length (out : List Int) (se : Nat)
    (vCount qCount : List Int) :
    (addRawMomentVStates out se vCount qCount).length = out.length := by
  unfold addRawMomentVStates
  apply foldl_length_of_step
  intro coefficients ev
  exact addRawMomentEndpoints_length _ _ _ _ _

theorem weightedListEval_addCoefficientLists (weight : Nat -> Real)
    (left right : List Int) (hlength : left.length = right.length) :
    weightedListEval weight (addCoefficientLists left right) =
      weightedListEval weight left + weightedListEval weight right := by
  induction left generalizing right weight with
  | nil =>
      have hright : right = [] :=
        List.length_eq_zero_iff.mp hlength.symm
      subst right
      simp [addCoefficientLists]
  | cons x xs ih =>
      cases right with
      | nil => simp at hlength
      | cons y ys =>
          simp only [List.length_cons, Nat.succ.injEq] at hlength
          simp only [addCoefficientLists, weightedListEval]
          rw [ih (fun i => weight (i + 1)) ys hlength]
          push_cast
          ring

theorem addCoefficientLists_length_of_eq (left right : List Int)
    (hlength : left.length = right.length) :
    (addCoefficientLists left right).length = left.length := by
  induction left generalizing right with
  | nil =>
      have hright : right = [] := List.length_eq_zero_iff.mp hlength.symm
      subst right
      rfl
  | cons x xs ih =>
      cases right with
      | nil => simp at hlength
      | cons y ys =>
          simp only [List.length_cons, Nat.succ.injEq] at hlength
          simp only [addCoefficientLists, List.length_cons, Nat.succ.injEq]
          exact ih ys hlength

set_option maxRecDepth 10000 in
@[simp] theorem rawMomentStateCoefficientList_length (s : Nat) :
    (rawMomentStateCoefficientList s).length = 800 := by
  unfold rawMomentStateCoefficientList
  rw [addRawMomentState_eq_addRawMomentVStates,
    addRawMomentVStates_length]
  simp

private theorem spinCode_cases (s k : Nat) :
    spinCode s k = 1 ∨ spinCode s k = -1 := by
  unfold spinCode
  split <;> simp

private theorem spinCode_le_one (s k : Nat) : spinCode s k ≤ 1 := by
  rcases spinCode_cases s k with h | h <;> omega

private theorem spinCode_mul_le_one (s t i j : Nat) :
    spinCode s i * spinCode t j ≤ 1 := by
  rcases spinCode_cases s i with hs | hs <;>
    rcases spinCode_cases t j with ht | ht <;> simp [hs, ht]

private theorem layerInternalInt_le (s : Nat) : layerInternalInt s ≤ 12 := by
  unfold layerInternalInt
  have h03 := spinCode_mul_le_one s s 0 3
  have h14 := spinCode_mul_le_one s s 1 4
  have h25 := spinCode_mul_le_one s s 2 5
  have h36 := spinCode_mul_le_one s s 3 6
  have h47 := spinCode_mul_le_one s s 4 7
  have h58 := spinCode_mul_le_one s s 5 8
  have h01 := spinCode_mul_le_one s s 0 1
  have h12 := spinCode_mul_le_one s s 1 2
  have h34 := spinCode_mul_le_one s s 3 4
  have h45 := spinCode_mul_le_one s s 4 5
  have h67 := spinCode_mul_le_one s s 6 7
  have h78 := spinCode_mul_le_one s s 7 8
  omega

private theorem layerLateralInt_le (s : Nat) : layerLateralInt s ≤ 24 := by
  unfold layerLateralInt
  have hi := layerInternalInt_le s
  have h0 := spinCode_le_one s 0
  have h1 := spinCode_le_one s 1
  have h2 := spinCode_le_one s 2
  have h3 := spinCode_le_one s 3
  have h5 := spinCode_le_one s 5
  have h6 := spinCode_le_one s 6
  have h7 := spinCode_le_one s 7
  have h8 := spinCode_le_one s 8
  omega

private theorem layerFaceInt_le (s : Nat) : layerFaceInt s ≤ 9 := by
  unfold layerFaceInt
  have h0 := spinCode_le_one s 0
  have h1 := spinCode_le_one s 1
  have h2 := spinCode_le_one s 2
  have h3 := spinCode_le_one s 3
  have h4 := spinCode_le_one s 4
  have h5 := spinCode_le_one s 5
  have h6 := spinCode_le_one s 6
  have h7 := spinCode_le_one s 7
  have h8 := spinCode_le_one s 8
  omega

private theorem layerDotInt_le (s t : Nat) : layerDotInt s t ≤ 9 := by
  unfold layerDotInt
  have h0 := spinCode_mul_le_one s t 0 0
  have h1 := spinCode_mul_le_one s t 1 1
  have h2 := spinCode_mul_le_one s t 2 2
  have h3 := spinCode_mul_le_one s t 3 3
  have h4 := spinCode_mul_le_one s t 4 4
  have h5 := spinCode_mul_le_one s t 5 5
  have h6 := spinCode_mul_le_one s t 6 6
  have h7 := spinCode_mul_le_one s t 7 7
  have h8 := spinCode_mul_le_one s t 8 8
  omega

theorem rawMomentVIndex_lt (s v : Nat) :
    Int.toNat (halfShift
      (layerDotInt s v + layerLateralInt v + layerFaceInt v) 26) < 35 := by
  have hd := layerDotInt_le s v
  have hl := layerLateralInt_le v
  have hf := layerFaceInt_le v
  unfold halfShift
  omega

theorem rawMomentQEndpointIndex_lt (q : Nat) :
    Int.toNat (halfShift (layerLateralInt q + layerFaceInt q) 17) < 26 := by
  have hl := layerLateralInt_le q
  have hf := layerFaceInt_le q
  unfold halfShift
  omega

theorem rawMomentQInteractionIndex_lt (s q : Nat) :
    Int.toNat (halfShift (layerDotInt s q) 9) < 10 := by
  have hd := layerDotInt_le s q
  unfold halfShift
  omega

theorem rawMomentQIndex_lt (s q : Nat) :
    10 * Int.toNat (halfShift (layerLateralInt q + layerFaceInt q) 17) +
        Int.toNat (halfShift (layerDotInt s q) 9) < 260 := by
  have he := rawMomentQEndpointIndex_lt q
  have hi := rawMomentQInteractionIndex_lt s q
  omega

theorem rawMomentStateIndex_lt (s ev eq iq : Nat)
    (hev : ev < 35) (heq : eq < 26) (hiq : iq < 10) :
    10 * (Int.toNat (halfShift (layerLateralInt s) 16) + ev + eq) + iq <
      800 := by
  have hl := layerLateralInt_le s
  unfold halfShift
  omega

theorem rawMomentStateExponentIndex_lt (s : Nat) :
    Int.toNat (halfShift (layerLateralInt s) 16) < 21 := by
  have hl := layerLateralInt_le s
  unfold halfShift
  omega

private theorem rawMomentDenseIndex_lt (se ev eq iq : Nat)
    (hse : se < 21) (hev : ev < 35) (heq : eq < 26) (hiq : iq < 10) :
    10 * (se + ev + eq) + iq < 800 := by
  omega

set_option maxRecDepth 10000 in
@[simp] theorem rawMomentVCounts_length (s : Nat) :
    (rawMomentVCounts s).length = 35 := by
  unfold rawMomentVCounts
  rw [foldl_length_of_step]
  · simp
  · intro out v
    exact updateCoefficient_length _ _ _

set_option maxRecDepth 10000 in
@[simp] theorem rawMomentQCounts_length (s : Nat) :
    (rawMomentQCounts s).length = 260 := by
  unfold rawMomentQCounts
  rw [foldl_length_of_step]
  · simp
  · intro out q
    exact updateCoefficient_length _ _ _

theorem weightedListEval_rawMomentVCounts_eq_getD (X : Real) (s : Nat) :
    weightedListEval (fun ev => X ^ (ev : Int)) (rawMomentVCounts s) =
      ((List.range 35).map fun ev =>
        (rawMomentVCounts s |>.getD ev 0 : Real) *
          X ^ (ev : Int)).sum := by
  rw [weightedListEval_eq_list_sum_getD, rawMomentVCounts_length]

theorem weightedListEval_rawMomentQCounts_eq_getD (X Y : Real) (s : Nat) :
    weightedListEval (denseMomentWeight X Y) (rawMomentQCounts s) =
      ((List.range 26).map fun eq =>
        ((List.range 10).map fun iq =>
          (rawMomentQCounts s |>.getD (10 * eq + iq) 0 : Real) *
            X ^ (eq : Int) * Y ^ (iq : Int)).sum).sum := by
  rw [weightedListEval_eq_list_sum_getD, rawMomentQCounts_length]
  change ((List.range 260).map fun index =>
      (rawMomentQCounts s |>.getD index 0 : Real) *
        denseMomentWeight X Y index).sum = _
  rw [show 260 = 26 * 10 by norm_num, list_range_mul_sum_blocks]
  apply congrArg List.sum
  apply List.map_congr_left
  intro eq heq
  apply congrArg List.sum
  apply List.map_congr_left
  intro iq hiq
  have hiq' : iq < 10 := List.mem_range.mp hiq
  have hdiv : (eq * 10 + iq) / 10 = eq := by omega
  have hmod : (eq * 10 + iq) % 10 = iq := by omega
  unfold denseMomentWeight
  rw [hdiv, hmod, Nat.mul_comm eq 10]
  ring

private theorem weightedListEval_addRawMomentInteractions
    (X Y : Real) (out : List Int) (se : Nat)
    (vCount qCount : List Int) (ev eq : Nat)
    (hlength : out.length = 800) (hse : se < 21)
    (hev : ev < 35) (heq : eq < 26) :
    weightedListEval (denseMomentWeight X Y)
        (addRawMomentInteractions out se vCount qCount ev eq) =
      weightedListEval (denseMomentWeight X Y) out +
        ((List.range 10).map fun iq =>
          ((vCount.getD ev 0 * qCount.getD (10 * eq + iq) 0 : Int) : Real) *
            denseMomentWeight X Y (10 * (se + ev + eq) + iq)).sum := by
  unfold addRawMomentInteractions
  rw [weightedListEval_foldl_update]
  intro iq hiq
  rw [hlength]
  exact rawMomentDenseIndex_lt _ _ _ _ hse hev heq (List.mem_range.mp hiq)

private theorem weightedListEval_addRawMomentEndpoints
    (X Y : Real) (out : List Int) (se : Nat)
    (vCount qCount : List Int) (ev : Nat)
    (hlength : out.length = 800) (hse : se < 21) (hev : ev < 35) :
    weightedListEval (denseMomentWeight X Y)
        (addRawMomentEndpoints out se vCount qCount ev) =
      weightedListEval (denseMomentWeight X Y) out +
        ((List.range 26).map fun eq =>
          ((List.range 10).map fun iq =>
            ((vCount.getD ev 0 * qCount.getD (10 * eq + iq) 0 : Int) : Real) *
              denseMomentWeight X Y
                (10 * (se + ev + eq) + iq)).sum).sum := by
  unfold addRawMomentEndpoints
  apply weightedListEval_foldl_additive_of_length
      (valid := fun eq => eq < 26) (n := 800) (hlength := hlength)
  · intro eq heq
    exact List.mem_range.mp heq
  · intro coefficients eq hcoefficients
    rw [addRawMomentInteractions_length, hcoefficients]
  · intro coefficients eq heq hcoefficients
    exact weightedListEval_addRawMomentInteractions X Y coefficients se
      vCount qCount ev eq hcoefficients hse hev heq

private theorem weightedListEval_addRawMomentVStates
    (X Y : Real) (out : List Int) (se : Nat)
    (vCount qCount : List Int) (hlength : out.length = 800)
    (hse : se < 21) :
    weightedListEval (denseMomentWeight X Y)
        (addRawMomentVStates out se vCount qCount) =
      weightedListEval (denseMomentWeight X Y) out +
        ((List.range 35).map fun ev =>
          ((List.range 26).map fun eq =>
            ((List.range 10).map fun iq =>
              ((vCount.getD ev 0 * qCount.getD (10 * eq + iq) 0 : Int) : Real) *
                denseMomentWeight X Y
                  (10 * (se + ev + eq) + iq)).sum).sum).sum := by
  unfold addRawMomentVStates
  apply weightedListEval_foldl_additive_of_length
      (valid := fun ev => ev < 35) (n := 800) (hlength := hlength)
  · intro ev hev
    exact List.mem_range.mp hev
  · intro coefficients ev hcoefficients
    rw [addRawMomentEndpoints_length, hcoefficients]
  · intro coefficients ev hev hcoefficients
    exact weightedListEval_addRawMomentEndpoints X Y coefficients se
      vCount qCount ev hcoefficients hse hev

private theorem denseMomentWeight_stateIndex (X Y : Real) (hX : X ≠ 0)
    (se ev eq iq : Nat) (hiq : iq < 10) :
    denseMomentWeight X Y (10 * (se + ev + eq) + iq) =
      X ^ (se : Int) * X ^ (ev : Int) * X ^ (eq : Int) *
        Y ^ (iq : Int) := by
  have hdiv : (10 * (se + ev + eq) + iq) / 10 = se + ev + eq := by
    omega
  have hmod : (10 * (se + ev + eq) + iq) % 10 = iq := by
    omega
  unfold denseMomentWeight
  rw [hdiv, hmod]
  push_cast
  rw [zpow_add₀ hX, zpow_add₀ hX]

private theorem list_sum_map_mul_left {alpha : Type*}
    (xs : List alpha) (f : alpha -> Real) (c : Real) :
    (xs.map fun x => c * f x).sum = c * (xs.map f).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      simp only [List.map_cons, List.sum_cons, ih]
      ring

private theorem list_sum_map_mul_right {alpha : Type*}
    (xs : List alpha) (f : alpha -> Real) (c : Real) :
    (xs.map fun x => f x * c).sum = (xs.map f).sum * c := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      simp only [List.map_cons, List.sum_cons, ih]
      ring

private theorem rawMomentTripleContribution_factor
    (X Y : Real) (hX : X ≠ 0) (se : Nat)
    (vCount qCount : List Int) :
    ((List.range 35).map fun ev =>
      ((List.range 26).map fun eq =>
        ((List.range 10).map fun iq =>
          ((vCount.getD ev 0 * qCount.getD (10 * eq + iq) 0 : Int) : Real) *
            denseMomentWeight X Y
              (10 * (se + ev + eq) + iq)).sum).sum).sum =
      X ^ (se : Int) *
        ((List.range 35).map fun ev =>
          (vCount.getD ev 0 : Real) * X ^ (ev : Int)).sum *
        ((List.range 26).map fun eq =>
          ((List.range 10).map fun iq =>
            (qCount.getD (10 * eq + iq) 0 : Real) *
              X ^ (eq : Int) * Y ^ (iq : Int)).sum).sum := by
  let qSum := ((List.range 26).map fun eq =>
    ((List.range 10).map fun iq =>
      (qCount.getD (10 * eq + iq) 0 : Real) *
        X ^ (eq : Int) * Y ^ (iq : Int)).sum).sum
  calc
    ((List.range 35).map fun ev =>
        ((List.range 26).map fun eq =>
          ((List.range 10).map fun iq =>
            ((vCount.getD ev 0 * qCount.getD (10 * eq + iq) 0 : Int) : Real) *
              denseMomentWeight X Y
                (10 * (se + ev + eq) + iq)).sum).sum).sum =
        ((List.range 35).map fun ev =>
          (X ^ (se : Int) *
            ((vCount.getD ev 0 : Real) * X ^ (ev : Int))) * qSum).sum := by
      apply congrArg List.sum
      apply List.map_congr_left
      intro ev hev
      let c := X ^ (se : Int) *
        ((vCount.getD ev 0 : Real) * X ^ (ev : Int))
      change _ = c * qSum
      calc
        ((List.range 26).map fun eq =>
            ((List.range 10).map fun iq =>
              ((vCount.getD ev 0 * qCount.getD (10 * eq + iq) 0 : Int) : Real) *
                denseMomentWeight X Y
                  (10 * (se + ev + eq) + iq)).sum).sum =
            ((List.range 26).map fun eq =>
              c * ((List.range 10).map fun iq =>
                (qCount.getD (10 * eq + iq) 0 : Real) *
                  X ^ (eq : Int) * Y ^ (iq : Int)).sum).sum := by
          apply congrArg List.sum
          apply List.map_congr_left
          intro eq heq
          rw [← list_sum_map_mul_left]
          apply congrArg List.sum
          apply List.map_congr_left
          intro iq hiq
          unfold c
          rw [denseMomentWeight_stateIndex X Y hX se ev eq iq
            (List.mem_range.mp hiq)]
          push_cast
          ring
        _ = c * qSum := by
          rw [list_sum_map_mul_left]
    _ = (X ^ (se : Int) *
          ((List.range 35).map fun ev =>
            (vCount.getD ev 0 : Real) * X ^ (ev : Int)).sum) * qSum := by
      rw [list_sum_map_mul_right, list_sum_map_mul_left]
    _ = X ^ (se : Int) *
          ((List.range 35).map fun ev =>
            (vCount.getD ev 0 : Real) * X ^ (ev : Int)).sum *
          ((List.range 26).map fun eq =>
            ((List.range 10).map fun iq =>
              (qCount.getD (10 * eq + iq) 0 : Real) *
                X ^ (eq : Int) * Y ^ (iq : Int)).sum).sum := by
      rfl

theorem weightedListEval_addRawMomentState (X Y : Real) (hX : X ≠ 0)
    (out : List Int) (s : Nat) (hlength : out.length = 800) :
    weightedListEval (denseMomentWeight X Y) (addRawMomentState out s) =
      weightedListEval (denseMomentWeight X Y) out +
        X ^ (Int.toNat (halfShift (layerLateralInt s) 16) : Int) *
          weightedListEval (fun ev => X ^ (ev : Int))
            (rawMomentVCounts s) *
          weightedListEval (denseMomentWeight X Y)
            (rawMomentQCounts s) := by
  rw [addRawMomentState_eq_addRawMomentVStates,
    weightedListEval_addRawMomentVStates X Y out
      (Int.toNat (halfShift (layerLateralInt s) 16))
      (rawMomentVCounts s) (rawMomentQCounts s) hlength
      (rawMomentStateExponentIndex_lt s),
    rawMomentTripleContribution_factor X Y hX,
    ← weightedListEval_rawMomentVCounts_eq_getD,
    ← weightedListEval_rawMomentQCounts_eq_getD]

set_option maxRecDepth 10000 in
theorem weightedListEval_rawMomentVCounts (X : Real) (s : Nat) :
    weightedListEval (fun ev => X ^ (ev : Int)) (rawMomentVCounts s) =
      ((List.range 512).map fun v =>
        X ^ (Int.toNat (halfShift
          (layerDotInt s v + layerLateralInt v + layerFaceInt v) 26) : Int)).sum := by
  unfold rawMomentVCounts
  rw [weightedListEval_foldl_update]
  · rw [weightedListEval_replicate_zero]
    simp
  · intro v hv
    exact rawMomentVIndex_lt s v

set_option maxRecDepth 10000 in
theorem weightedListEval_rawMomentQCounts (X Y : Real) (s : Nat) :
    weightedListEval
        (fun index => X ^ ((index / 10 : Nat) : Int) *
          Y ^ ((index % 10 : Nat) : Int))
        (rawMomentQCounts s) =
      ((List.range 512).map fun q =>
        X ^ (Int.toNat
          (halfShift (layerLateralInt q + layerFaceInt q) 17) : Int) *
        Y ^ (Int.toNat (halfShift (layerDotInt s q) 9) : Int)).sum := by
  unfold rawMomentQCounts
  rw [weightedListEval_foldl_update]
  · rw [weightedListEval_replicate_zero]
    simp only [zero_add, Int.cast_one, one_mul]
    apply congrArg List.sum
    apply List.map_congr_left
    intro q hq
    let eq := Int.toNat
      (halfShift (layerLateralInt q + layerFaceInt q) 17)
    let iq := Int.toNat (halfShift (layerDotInt s q) 9)
    have hi : iq < 10 := rawMomentQInteractionIndex_lt s q
    have hdiv : (10 * eq + iq) / 10 = eq := by omega
    have hmod : (10 * eq + iq) % 10 = iq := by omega
    change X ^ (((10 * eq + iq) / 10 : Nat) : Int) *
        Y ^ (((10 * eq + iq) % 10 : Nat) : Int) =
      X ^ (eq : Int) * Y ^ (iq : Int)
    rw [hdiv, hmod]
  · intro q hq
    exact rawMomentQIndex_lt s q

set_option maxRecDepth 10000 in
theorem weightedListEval_rawMomentStateCoefficientList
    (X Y : Real) (hX : X ≠ 0) (s : Nat) :
    weightedListEval (denseMomentWeight X Y)
        (rawMomentStateCoefficientList s) =
      X ^ (Int.toNat (halfShift (layerLateralInt s) 16) : Int) *
        ((List.range 512).map fun v =>
          X ^ (Int.toNat (halfShift
            (layerDotInt s v + layerLateralInt v + layerFaceInt v) 26) :
              Int)).sum *
        ((List.range 512).map fun q =>
          X ^ (Int.toNat
            (halfShift (layerLateralInt q + layerFaceInt q) 17) : Int) *
          Y ^ (Int.toNat (halfShift (layerDotInt s q) 9) : Int)).sum := by
  unfold rawMomentStateCoefficientList
  have hlength : (List.replicate 800 (0 : Int)).length = 800 := by simp
  rw [weightedListEval_addRawMomentState X Y hX
      (List.replicate 800 0) s hlength,
    weightedListEval_replicate_zero,
    zero_add, weightedListEval_rawMomentVCounts]
  have hq := weightedListEval_rawMomentQCounts X Y s
  simpa only [denseMomentWeight] using congrArg
    (fun qSum =>
      X ^ (Int.toNat (halfShift (layerLateralInt s) 16) : Int) *
        ((List.range 512).map fun v =>
          X ^ (Int.toNat (halfShift
            (layerDotInt s v + layerLateralInt v + layerFaceInt v) 26) :
              Int)).sum * qSum) hq

set_option maxRecDepth 10000 in
@[simp] theorem rawMomentCoefficientSmallList_length (start count : Nat) :
    (rawMomentCoefficientSmallList start count).length = 800 := by
  unfold rawMomentCoefficientSmallList
  apply foldl_length_of_invariant (n := 800)
  · simp
  · intro out offset hout
    calc
      (addCoefficientLists out
          (rawMomentStateCoefficientList (start + offset))).length =
          out.length := addCoefficientLists_length_of_eq _ _ (by
            rw [hout, rawMomentStateCoefficientList_length])
      _ = 800 := hout

set_option maxRecDepth 10000 in
theorem weightedListEval_rawMomentCoefficientSmallList
    (X Y : Real) (start count : Nat) :
    weightedListEval (denseMomentWeight X Y)
        (rawMomentCoefficientSmallList start count) =
      ((List.range count).map fun offset =>
        weightedListEval (denseMomentWeight X Y)
          (rawMomentStateCoefficientList (start + offset))).sum := by
  unfold rawMomentCoefficientSmallList
  rw [weightedListEval_foldl_additive_of_length
    (valid := fun _ => True) (n := 800)]
  · rw [weightedListEval_replicate_zero, zero_add]
  · simp
  · intro offset hoffset
    trivial
  · intro out offset hout
    calc
      (addCoefficientLists out
          (rawMomentStateCoefficientList (start + offset))).length =
          out.length := addCoefficientLists_length_of_eq _ _ (by
            rw [hout, rawMomentStateCoefficientList_length])
      _ = 800 := hout
  · intro out offset hoffset hout
    exact weightedListEval_addCoefficientLists _ _ _ (by
      rw [hout, rawMomentStateCoefficientList_length])

set_option maxRecDepth 10000 in
@[simp] theorem rawMomentCoefficientBlockList_length (start count : Nat) :
    (rawMomentCoefficientBlockList start count).length = 800 := by
  induction count using Nat.twoStepInduction generalizing start with
  | zero => simp [rawMomentCoefficientBlockList]
  | one => simp [rawMomentCoefficientBlockList]
  | more count ih0 ih1 =>
      rw [rawMomentCoefficientBlockList]
      have hlength :
          (rawMomentCoefficientSmallList start 2).length =
            (rawMomentCoefficientBlockList (start + 2) count).length := by
        rw [rawMomentCoefficientSmallList_length, ih0]
      rw [addCoefficientLists_length_of_eq _ _ hlength,
        rawMomentCoefficientSmallList_length]

set_option maxRecDepth 10000 in
theorem weightedListEval_rawMomentCoefficientBlockList
    (X Y : Real) (start count : Nat) :
    weightedListEval (denseMomentWeight X Y)
        (rawMomentCoefficientBlockList start count) =
      ((List.range count).map fun offset =>
        weightedListEval (denseMomentWeight X Y)
          (rawMomentStateCoefficientList (start + offset))).sum := by
  induction count using Nat.twoStepInduction generalizing start with
  | zero =>
      rw [rawMomentCoefficientBlockList,
        weightedListEval_replicate_zero]
      rfl
  | one =>
      rw [rawMomentCoefficientBlockList,
        weightedListEval_rawMomentCoefficientSmallList]
  | more count ih0 ih1 =>
      rw [rawMomentCoefficientBlockList,
        weightedListEval_addCoefficientLists _ _ _ (by
          rw [rawMomentCoefficientSmallList_length,
            rawMomentCoefficientBlockList_length]),
        weightedListEval_rawMomentCoefficientSmallList, ih0]
      rw [show count + 2 = 2 + count by omega,
        list_range_add_sum]
      apply congrArg₂ (.+.) rfl
      apply congrArg List.sum
      apply List.map_congr_left
      intro offset hoffset
      congr 2
      omega

set_option maxRecDepth 10000 in
@[simp] theorem rawMomentCoefficientList_length :
    rawMomentCoefficientList.length = 800 := by
  unfold rawMomentCoefficientList
  apply foldl_length_of_invariant (n := 800)
  · simp
  · intro out block hout
    calc
      (addCoefficientLists out
          (rawMomentCoefficientBlockList (32 * block) 32)).length =
          out.length := addCoefficientLists_length_of_eq _ _ (by
            rw [hout, rawMomentCoefficientBlockList_length])
      _ = 800 := hout

set_option maxRecDepth 10000 in
theorem weightedListEval_rawMomentCoefficientList (X Y : Real) :
    weightedListEval (denseMomentWeight X Y) rawMomentCoefficientList =
      ((List.range 512).map fun s =>
        weightedListEval (denseMomentWeight X Y)
          (rawMomentStateCoefficientList s)).sum := by
  let stateEval := fun s => weightedListEval (denseMomentWeight X Y)
    (rawMomentStateCoefficientList s)
  calc
    weightedListEval (denseMomentWeight X Y) rawMomentCoefficientList =
        ((List.range 16).map fun block =>
          weightedListEval (denseMomentWeight X Y)
            (rawMomentCoefficientBlockList (32 * block) 32)).sum := by
      unfold rawMomentCoefficientList
      rw [weightedListEval_foldl_additive_of_length
        (valid := fun _ => True) (n := 800)]
      · rw [weightedListEval_replicate_zero, zero_add]
      · simp
      · intro block hblock
        trivial
      · intro out block hout
        calc
          (addCoefficientLists out
              (rawMomentCoefficientBlockList (32 * block) 32)).length =
              out.length := addCoefficientLists_length_of_eq _ _ (by
                rw [hout, rawMomentCoefficientBlockList_length])
          _ = 800 := hout
      · intro out block hblock hout
        exact weightedListEval_addCoefficientLists _ _ _ (by
          rw [hout, rawMomentCoefficientBlockList_length])
    _ = ((List.range 16).map fun block =>
          ((List.range 32).map fun offset =>
            stateEval (block * 32 + offset)).sum).sum := by
      apply congrArg List.sum
      apply List.map_congr_left
      intro block hblock
      rw [weightedListEval_rawMomentCoefficientBlockList]
      apply congrArg List.sum
      apply List.map_congr_left
      intro offset hoffset
      unfold stateEval
      rw [Nat.mul_comm 32 block]
    _ = ((List.range (16 * 32)).map stateEval).sum := by
      exact (list_range_mul_sum_blocks stateEval 16 32).symm
    _ = ((List.range 512).map fun s =>
          weightedListEval (denseMomentWeight X Y)
            (rawMomentStateCoefficientList s)).sum := by
      norm_num
      rfl

set_option maxRecDepth 10000 in
theorem weightedListEval_rawMomentCoefficientList_stateSum
    (X Y : Real) (hX : X ≠ 0) :
    weightedListEval (denseMomentWeight X Y) rawMomentCoefficientList =
      ((List.range 512).map fun s =>
        X ^ (Int.toNat (halfShift (layerLateralInt s) 16) : Int) *
          ((List.range 512).map fun v =>
            X ^ (Int.toNat (halfShift
              (layerDotInt s v + layerLateralInt v + layerFaceInt v) 26) :
                Int)).sum *
          ((List.range 512).map fun q =>
            X ^ (Int.toNat
              (halfShift (layerLateralInt q + layerFaceInt q) 17) : Int) *
            Y ^ (Int.toNat (halfShift (layerDotInt s q) 9) : Int)).sum).sum := by
  rw [weightedListEval_rawMomentCoefficientList]
  apply congrArg List.sum
  apply List.map_congr_left
  intro s hs
  exact weightedListEval_rawMomentStateCoefficientList X Y hX s

theorem weightedListEval_denseMomentWeight_eq_grid
    (X Y : Real) (coefficients : List Int)
    (hlength : coefficients.length = 800) :
    weightedListEval (denseMomentWeight X Y) coefficients =
      ((List.range 80).map fun ex =>
        ((List.range 10).map fun ey =>
          (coefficients.getD (10 * ex + ey) 0 : Real) *
            X ^ (ex : Int) * Y ^ (ey : Int)).sum).sum := by
  rw [weightedListEval_eq_list_sum_getD, hlength]
  change ((List.range 800).map fun index =>
      (coefficients.getD index 0 : Real) *
        denseMomentWeight X Y index).sum = _
  rw [show 800 = 80 * 10 by norm_num, list_range_mul_sum_blocks]
  apply congrArg List.sum
  apply List.map_congr_left
  intro ex hex
  apply congrArg List.sum
  apply List.map_congr_left
  intro ey hey
  have hey' : ey < 10 := List.mem_range.mp hey
  have hdiv : (ex * 10 + ey) / 10 = ex := by omega
  have hmod : (ex * 10 + ey) % 10 = ey := by omega
  unfold denseMomentWeight
  rw [hdiv, hmod, Nat.mul_comm ex 10]
  ring

private theorem list_sum_flatMap {alpha : Type*}
    (xs : List alpha) (f : alpha -> List Real) :
    (xs.flatMap f).sum = (xs.map fun x => (f x).sum).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp [ih]

theorem BiPoly.eval_rawMomentPolyOfCoefficientList
    (X Y : Real) (coefficients : List Int)
    (hlength : coefficients.length = 800) :
    (rawMomentPolyOfCoefficientList coefficients).eval X Y =
      weightedListEval (denseMomentWeight X Y) coefficients := by
  rw [weightedListEval_denseMomentWeight_eq_grid X Y coefficients hlength]
  unfold rawMomentPolyOfCoefficientList
  rw [BiPoly.eval_ofTerms]
  rw [List.map_flatMap, list_sum_flatMap]
  apply congrArg List.sum
  apply List.map_congr_left
  intro ex hex
  apply congrArg List.sum
  rw [List.map_map]
  apply List.map_congr_left
  intro ey hey
  unfold BiTerm.eval
  rfl

theorem BiPoly.eval_rawMomentPoly (X Y : Real) :
    rawMomentPoly.eval X Y =
      weightedListEval (denseMomentWeight X Y) rawMomentCoefficientList := by
  unfold rawMomentPoly
  exact BiPoly.eval_rawMomentPolyOfCoefficientList X Y _
    rawMomentCoefficientList_length

end StatMech.FrontierA.NOneSymmetricMeanCertificate
