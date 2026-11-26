/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Polynomial.Derivative
public import MathlibExt.Combinatorics.Enumerative.LuckyCars
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Positivity
import all MathlibExt.Combinatorics.Enumerative.PollakPartialParkingFunctions

/-!
# Factorial moments of lucky cars in parking functions

The falling-factorial moments of the lucky-car count are the derivatives of the lucky-car
generating polynomial at one, divided by the number of parking functions.
-/

set_option autoImplicit false

@[expose] public section

namespace MathlibExt.Combinatorics.Enumerative.LuckyCarsWanted

open MetaMathlibExt MetaMathlibExt.PollakPartialParking Polynomial

-- Each car contributes a factor of X if its preferred spot is free on arrival.
private noncomputable def circleWeight {s n : ℕ} (g : Fin s → ZMod (n + 1)) (hs : s ≤ n) :
    Polynomial ℚ :=
  ∏ i : Fin s, if g i ∈ parkOcc s n g hs i.val then 1 else X

private theorem parkOcc_snoc {s n : ℕ} (g : Fin s → ZMod (n + 1)) (a : ZMod (n + 1))
    (hs : s + 1 ≤ n) (k : ℕ) (hk : k ≤ s) :
    parkOcc (s + 1) n (Fin.snoc g a) hs k = parkOcc s n g (by omega) k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have hks : k < s := by omega
    have hks' : k < s + 1 := by omega
    rw [parkOcc_succ_of_lt _ _ _ _ _ hks', parkOcc_succ_of_lt _ _ _ _ _ hks]
    have hocc := ih (by omega)
    have hp : (Fin.snoc g a : Fin (s + 1) → ZMod (n + 1)) ⟨k, hks'⟩ = g ⟨k, hks⟩ :=
      Fin.snoc_castSucc (α := fun _ => ZMod (n + 1)) a g ⟨k, hks⟩
    have ha : parkAssign (s + 1) n (Fin.snoc g a) hs k hks' =
        parkAssign s n g (by omega) k hks := by
      simp [parkAssign, hocc, hp]
    rw [ha, hocc]

private theorem circleWeight_snoc {s n : ℕ} (g : Fin s → ZMod (n + 1)) (a : ZMod (n + 1))
    (hs : s + 1 ≤ n) :
    circleWeight (Fin.snoc g a) hs =
      (if a ∈ parkOcc s n g (by omega) s then 1 else X) * circleWeight g (by omega) := by
  unfold circleWeight
  rw [Fin.prod_univ_castSucc, mul_comm]
  simp only [Fin.snoc_last, Fin.val_last, Fin.snoc_castSucc, Fin.val_castSucc]
  exact congrArg₂ (· * ·)
    (by rw [parkOcc_snoc g a hs s le_rfl])
    (Finset.prod_congr rfl (fun i _ => by
      rw [parkOcc_snoc g a hs i.val i.isLt.le]))

private theorem sum_circleWeight (n s : ℕ) (hs : s ≤ n) :
    (∑ g : Fin s → ZMod (n + 1), circleWeight g hs) =
      ∏ i : Fin s, (C ((n + 1 - i.val : ℕ) : ℚ) * X + C (i.val : ℚ)) := by
  induction s with
  | zero => simp [circleWeight]
  | succ s ih =>
    have hsn : s ≤ n := by omega
    -- A prefix of length s leaves s occupied spots, independently of its preferences.
    have hsum (g : Fin s → ZMod (n + 1)) :
        (∑ a : ZMod (n + 1), (if a ∈ parkOcc s n g hsn s then 1 else X : Polynomial ℚ)) =
          C ((n + 1 - s : ℕ) : ℚ) * X + C (s : ℚ) := by
      rw [Finset.sum_ite, Finset.filter_mem_eq_inter, Finset.univ_inter,
        ← Finset.sdiff_eq_filter, Finset.sum_const, Finset.sum_const,
        card_parkOcc_self, ← parkEmpty, card_parkEmpty]
      simp [nsmul_eq_mul, add_comm]
    calc
      _ = ∑ p : ZMod (n + 1) × (Fin s → ZMod (n + 1)),
          circleWeight (Fin.snoc p.2 p.1) hs :=
        ((Fin.snocEquiv fun _ : Fin (s + 1) => ZMod (n + 1)).sum_comp
          (fun g => circleWeight g hs)).symm
      _ = ∑ g : Fin s → ZMod (n + 1), ∑ a : ZMod (n + 1),
          (if a ∈ parkOcc s n g hsn s then 1 else X) * circleWeight g hsn := by
        rw [← (Equiv.prodComm (Fin s → ZMod (n + 1)) (ZMod (n + 1))).sum_comp,
          Fintype.sum_prod_type]
        simp only [Equiv.prodComm_apply, Prod.swap, circleWeight_snoc]
      _ = _ := by
        simp_rw [← Finset.sum_mul, hsum]
        rw [← Finset.mul_sum, ih hsn, Fin.prod_univ_castSucc, mul_comm]
        rfl

-- On successful linear runs, the list implementation agrees with the circular assignment
-- at each car, with the extra spot left unused.
private theorem parkSpotsFrom_eq_parkAssign {n : ℕ} (f : Fin n → Fin n)
    (hf : LinSuccess n n f) (i : Fin n) (j : ℕ) (hj : j ≤ i.val)
    (occ : {o : Finset (Fin n) // o.card ≤ j})
    (hlin : linOccAux n n f j = some occ)
    (hcir : parkOcc n n (lift n n f) le_rfl j = occ.val.image (emb n)) :
    emb n ((parkSpotsFrom ((List.ofFn f).drop j) occ.val).getD (i.val - j) i) =
      parkAssign n n (lift n n f) le_rfl i.val i.isLt := by
  have hjn : j < n := lt_of_le_of_lt hj i.isLt
  obtain ⟨b, hb⟩ := linTake_some_of_success n n f hf j hjn
  rw [linTake_eq _ _ _ _ _ _ hlin] at hb
  have hnext : nextFreeSpot occ.val (f ⟨j, hjn⟩) = b := by
    unfold linFirstFree at hb
    unfold nextFreeSpot
    simp only [Fin.le_def]
    split_ifs at hb with h
    rw [dite_eq_left h]
    exact Option.some.inj hb
  have hassign : parkAssign n n (lift n n f) le_rfl j hjn = emb n b :=
    bridge_some n occ.val (f ⟨j, hjn⟩) b _ hcir _ hb
  rw [List.drop_eq_getElem_cons (by simpa using hjn), List.getElem_ofFn, parkSpotsFrom, hnext]
  by_cases hji : j = i.val
  · subst j
    simpa using hassign.symm
  · rw [show i.val - j = (i.val - (j + 1)) + 1 by omega, List.getD_cons_succ]
    exact parkSpotsFrom_eq_parkAssign f hf i (j + 1) (by omega) _
      (linOccAux_succ_some _ _ _ _ _ hlin _ _ hb)
      (by rw [parkOcc_succ_of_lt _ _ _ _ _ hjn, hassign, hcir, Finset.image_insert])
termination_by i.val - j

private theorem circleWeight_lift {n : ℕ} (f : Fin n → Fin n) (hf : IsParkingFunction n f) :
    circleWeight (lift n n f) le_rfl = X ^ luckyCount f := by
  have hf' : LinSuccess n n f :=
    (linSuccess_iff_isPartialParkingFunction n n f le_rfl).mpr hf
  have hspot (i : Fin n) : emb n (parkSpots f i) =
      parkAssign n n (lift n n f) le_rfl i.val i.isLt := by
    simpa [parkSpots] using parkSpotsFrom_eq_parkAssign f hf' i 0 (Nat.zero_le _) ⟨∅, by simp⟩
      (linOccAux_zero n n f) (by simp [parkOcc, parkOccAux])
  have hlucky (i : Fin n) :
      parkSpots f i = f i ↔ lift n n f i ∉ parkOcc n n (lift n n f) le_rfl i.val := by
    have hsize := circle_card_lt n n (lift n n f) le_rfl i.val i.isLt.le
    have hassign : parkAssign n n (lift n n f) le_rfl i.val i.isLt =
        firstFree n (parkOcc n n (lift n n f) le_rfl i.val) (lift n n f i) hsize := rfl
    rw [← (emb_injective n).eq_iff, hspot, hassign]
    change firstFree n _ (lift n n f i) _ = lift n n f i ↔ _
    constructor
    · intro h
      rw [← h]
      exact firstFree_not_mem _ _ _ _
    · intro h
      have hzero := Nat.find_min' (ray_free_exists n _ (lift n n f i) hsize) (m := 0)
        (by simpa using h)
      unfold firstFree
      rw [Nat.eq_zero_of_le_zero hzero]
      simp
  unfold circleWeight luckyCount
  conv_rhs => rw [← Finset.prod_const X, ← Fintype.prod_ite_mem]
  refine Finset.prod_congr rfl fun i _ => ?_
  by_cases hi : parkSpots f i = f i
  · simp [hi, (hlucky i).mp hi]
  · have ho : lift n n f i ∈ parkOcc n n (lift n n f) le_rfl i.val :=
      not_not.mp (mt (hlucky i).mpr hi)
    simp [hi, ho]

private theorem circleWeight_translate {n : ℕ} (g : Fin n → ZMod (n + 1))
    (c : ZMod (n + 1)) :
    circleWeight (fun i => g i + c) le_rfl = circleWeight g le_rfl := by
  unfold circleWeight
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [parkOcc_translate]
  simp

-- For each circular run there is one empty spot. Grouping the same weighted runs
-- by that spot gives equal sums, since rotating the circle preserves the weight.
private theorem sum_circleWeight_eq_linear (n : ℕ) :
    (∑ g : Fin n → ZMod (n + 1), circleWeight g le_rfl) =
      C ((n : ℚ) + 1) * ∑ f : {f : Fin n → Fin n // IsParkingFunction n f},
        X ^ luckyCount f.val := by
  classical
  let e := (StoSigma n n le_rfl).symm.trans
    (((Equiv.prodComm (Fin n → ZMod (n + 1)) (ZMod (n + 1))).subtypeEquiv
      (by intro p; rfl)).trans (TtoSigma n n le_rfl))
  have hfixed :
      (∑ g : {g : Fin n → ZMod (n + 1) // extra n ∈ parkEmpty n n g le_rfl},
        circleWeight g.val le_rfl) =
      ∑ f : {f : Fin n → Fin n // IsParkingFunction n f}, X ^ luckyCount f.val := by
    symm
    exact Fintype.sum_equiv (PfEquiv n n le_rfl) _ _
      (fun f => (circleWeight_lift f.val f.property).symm)
  calc
    _ = ∑ g : Fin n → ZMod (n + 1), ∑ _x : ↥(parkEmpty n n g le_rfl),
          circleWeight g le_rfl := by
      simp [Finset.sum_const, card_parkEmpty]
    _ = ∑ x : ZMod (n + 1),
          ∑ g : {g : Fin n → ZMod (n + 1) // x ∈ parkEmpty n n g le_rfl},
            circleWeight g.val le_rfl := by
      simp only [Finset.sum_sigma', Finset.univ_sigma_univ]
      exact Fintype.sum_equiv e _ _ (fun _ => rfl)
    _ = _ := by
      have hfiber (x : ZMod (n + 1)) :
          (∑ g : {g : Fin n → ZMod (n + 1) // x ∈ parkEmpty n n g le_rfl},
            circleWeight g.val le_rfl) =
          ∑ g : {g : Fin n → ZMod (n + 1) // extra n ∈ parkEmpty n n g le_rfl},
            circleWeight g.val le_rfl :=
        Fintype.sum_equiv (fiberEquiv n n le_rfl x) _ _
          (fun g => (circleWeight_translate g.val (extra n - x)).symm)
      simp_rw [hfiber, hfixed]
      simp [Finset.sum_const, ZMod.card, nsmul_eq_mul, add_mul]

private theorem luckyGenPoly_eq_sum_powers (n : ℕ) :
    luckyGenPoly n =
      ∑ f ∈ Finset.univ.filter (fun f : Fin n → Fin n => IsParkingFunction n f),
        X ^ luckyCount f := by
  have h : (n : ℚ) + 1 ≠ 0 := by positivity
  rw [luckyGenPoly, ← sum_circleWeight n n le_rfl, sum_circleWeight_eq_linear,
    ← mul_assoc, ← C_mul, one_div_mul_cancel h, map_one, one_mul]
  symm
  exact Finset.sum_subtype _ (fun f => by simp) _

-- The identity also holds at n = 0. The hypothesis matches the original statement.
set_option linter.unusedVariables false in
/-- **Factorial moments of the number of lucky cars.** Let $n \ge 1$ and $\ell \in \mathbb{N}$, let
$X(f)$ be the number of lucky cars of a parking function $f$ of length $n$, and let
$P_n(x) = \frac{1}{n+1} \prod_{i=0}^{n-1} \bigl((n+1-i)x + i\bigr) \in \mathbb{Q}[x]$. Then
$$\frac{1}{(n+1)^{n-1}} \sum_f X(f)\bigl(X(f)-1\bigr)\cdots\bigl(X(f)-\ell+1\bigr) =
\frac{P_n^{(\ell)}(1)}{(n+1)^{n-1}},$$
where $f$ runs over the parking functions of length $n$ and $P_n^{(\ell)}$ is the $\ell$-th
derivative of $P_n$. Since there are $(n+1)^{n-1}$ parking functions of length $n$, the left side
is the $\ell$-th falling-factorial moment of $X$ for a uniformly random parking function.

Source: Steve Butler et al., "Lucky Cars and Lucky Spots in
Parking Functions", Proposition 6. -/
theorem expected_descFactorial_luckyCount (n ℓ : ℕ)
    (hn : 1 ≤ n) :
    ((∑ f ∈ Finset.univ.filter (fun f : Fin n → Fin n =>
        IsParkingFunction n f),
      ((luckyCount f).descFactorial ℓ : ℚ)) /
        (n + 1 : ℚ) ^ (n - 1) =
      (Polynomial.derivative^[ℓ] (luckyGenPoly n)).eval 1 /
        (n + 1 : ℚ) ^ (n - 1)) := by
  rw [luckyGenPoly_eq_sum_powers, iterate_derivative_sum, eval_finsetSum]
  congr 1
  refine Finset.sum_congr rfl fun f _ => ?_
  rw [iterate_derivative_X_pow_eq_C_mul]
  simp

end MathlibExt.Combinatorics.Enumerative.LuckyCarsWanted
