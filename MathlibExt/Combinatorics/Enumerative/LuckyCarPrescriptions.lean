/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.Enumerative.LuckyCars
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Positivity
import all MathlibExt.Combinatorics.Enumerative.LuckyCarFactorialMoments
import all MathlibExt.Combinatorics.Enumerative.PollakPartialParkingFunctions

/-!
# Parking functions with prescribed lucky and unlucky cars

We count preferences on a circle with one extra spot. Each car contributes a factor counting
its permitted preferences, and rotation shows that exactly one in `n + 1` of the circular
preferences leaves the extra spot empty.

## References

- Steve Butler, Kimberly Hadaway, Victoria Lenius, Preston Martens, and Marshall Moats,
  *Lucky Cars and Lucky Spots in Parking Functions*, J. Integer Seq. 29 (2026),
  Article 26.1.1, Theorem 4.
- The underlying circle-and-rotation argument is due to Pollak, as communicated in
  J. Riordan, *Ballots and trees*, J. Combin. Theory 6 (1969), 408–411.
-/

set_option autoImplicit false

@[expose] public section

namespace MathlibExt.Combinatorics.Enumerative.LuckyCarsWanted

open MetaMathlibExt MetaMathlibExt.PollakPartialParking

open Classical in
private noncomputable def statusWeight (l u lucky : Prop) : ℚ :=
  if (l → lucky) ∧ (u → ¬ lucky) then 1 else 0

private noncomputable def prescribedCircleWeight {s n : ℕ} (g : Fin s → ZMod (n + 1))
    (hs : s ≤ n) (L U : Fin s → Prop) : ℚ :=
  ∏ i : Fin s, statusWeight (L i) (U i) (g i ∉ parkOcc s n g hs i.val)

open Classical in
private noncomputable def preferenceCount (n i : ℕ) (l u : Prop) : ℚ :=
  if l then ((n + 1 - i : ℕ) : ℚ) else if u then (i : ℚ) else (n + 1 : ℚ)

private theorem prescribedCircleWeight_snoc {s n : ℕ} (g : Fin s → ZMod (n + 1))
    (a : ZMod (n + 1)) (hs : s + 1 ≤ n) (L U : Fin (s + 1) → Prop) :
    prescribedCircleWeight (Fin.snoc g a) hs L U =
      prescribedCircleWeight g (by omega) (L ∘ Fin.castSucc) (U ∘ Fin.castSucc) *
        statusWeight (L (Fin.last s)) (U (Fin.last s))
          (a ∉ parkOcc s n g (by omega) s) := by
  unfold prescribedCircleWeight
  rw [Fin.prod_univ_castSucc]
  simp only [Fin.snoc_last, Fin.val_last, Fin.snoc_castSucc, Fin.val_castSucc, Function.comp_apply]
  exact congrArg₂ (· * ·)
    (Finset.prod_congr rfl fun i _ => by rw [parkOcc_snoc g a hs i.val i.isLt.le])
    (by rw [parkOcc_snoc g a hs s le_rfl])

-- The number of allowed preferences for the next car depends only on the prefix length.
private theorem sum_statusWeight {s n : ℕ} (g : Fin s → ZMod (n + 1)) (hs : s ≤ n)
    (l u : Prop) (hlu : ¬ (l ∧ u)) :
    (∑ a : ZMod (n + 1), statusWeight l u (a ∉ parkOcc s n g hs s)) =
      preferenceCount n s l u := by
  classical
  by_cases hl : l
  · have hu : ¬ u := fun h => hlu ⟨hl, h⟩
    simp only [statusWeight, preferenceCount, hl, hu, true_implies, false_implies, and_true,
      ite_true]
    rw [Finset.sum_ite, ← Finset.sdiff_eq_filter, Finset.sum_const, ← parkEmpty, card_parkEmpty]
    simp
  · by_cases hu : u
    · simp only [statusWeight, preferenceCount, hl, hu, false_implies, true_implies, true_and,
        not_not, ite_false, ite_true]
      rw [Finset.sum_ite, Finset.filter_mem_eq_inter, Finset.univ_inter, Finset.sum_const,
        card_parkOcc_self]
      simp
    · simp [statusWeight, preferenceCount, hl, hu, ZMod.card]

private theorem sum_prescribedCircleWeight (n s : ℕ) (hs : s ≤ n) (L U : Fin s → Prop)
    (hLU : ∀ i, ¬ (L i ∧ U i)) :
    (∑ g : Fin s → ZMod (n + 1), prescribedCircleWeight g hs L U) =
      ∏ i : Fin s, preferenceCount n i.val (L i) (U i) := by
  induction s with
  | zero => simp [prescribedCircleWeight]
  | succ s ih =>
    have hsn : s ≤ n := by omega
    calc
      _ = ∑ p : ZMod (n + 1) × (Fin s → ZMod (n + 1)),
          prescribedCircleWeight (Fin.snoc p.2 p.1) hs L U :=
        ((Fin.snocEquiv fun _ : Fin (s + 1) => ZMod (n + 1)).sum_comp
          (fun g => prescribedCircleWeight g hs L U)).symm
      _ = ∑ g : Fin s → ZMod (n + 1), ∑ a : ZMod (n + 1),
          prescribedCircleWeight g hsn (L ∘ Fin.castSucc) (U ∘ Fin.castSucc) *
            statusWeight (L (Fin.last s)) (U (Fin.last s)) (a ∉ parkOcc s n g hsn s) := by
        rw [← (Equiv.prodComm (Fin s → ZMod (n + 1)) (ZMod (n + 1))).sum_comp,
          Fintype.sum_prod_type]
        simp only [Equiv.prodComm_apply, Prod.swap, prescribedCircleWeight_snoc]
      _ = _ := by
        simp_rw [← Finset.mul_sum, sum_statusWeight _ hsn _ _ (hLU (Fin.last s))]
        rw [← Finset.sum_mul, ih hsn (L ∘ Fin.castSucc) (U ∘ Fin.castSucc)
          (fun i => hLU i.castSucc), Fin.prod_univ_castSucc]
        rfl

private theorem isLuckyCar_iff_not_mem_parkOcc {n : ℕ} (f : Fin n → Fin n)
    (hf : IsParkingFunction n f) (i : Fin n) :
    IsLuckyCar f i ↔ lift n n f i ∉ parkOcc n n (lift n n f) le_rfl i.val := by
  have hf' : LinSuccess n n f :=
    (linSuccess_iff_isPartialParkingFunction n n f le_rfl).mpr hf
  have hspot : emb n (parkSpots f i) = parkAssign n n (lift n n f) le_rfl i.val i.isLt := by
    simpa [parkSpots] using parkSpotsFrom_eq_parkAssign f hf' i 0 (Nat.zero_le _) ⟨∅, by simp⟩
      (linOccAux_zero n n f) (by simp [parkOcc, parkOccAux])
  have hsize := circle_card_lt n n (lift n n f) le_rfl i.val i.isLt.le
  unfold IsLuckyCar
  rw [← (emb_injective n).eq_iff, hspot]
  change firstFree n _ (lift n n f i) hsize = lift n n f i ↔ _
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

private theorem prescribedCircleWeight_translate {n : ℕ} (g : Fin n → ZMod (n + 1))
    (L U : Fin n → Prop) (c : ZMod (n + 1)) :
    prescribedCircleWeight (fun i => g i + c) le_rfl L U =
      prescribedCircleWeight g le_rfl L U := by
  unfold prescribedCircleWeight
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [parkOcc_translate]
  simp

open Classical in
private theorem prod_statusWeight {n : ℕ} (L U : Finset (Fin n)) (lucky : Fin n → Prop) :
    (∏ i : Fin n, statusWeight (i ∈ L) (i ∈ U) (lucky i)) =
      if (∀ i ∈ L, lucky i) ∧ (∀ i ∈ U, ¬ lucky i) then 1 else 0 := by
  by_cases h : (∀ i ∈ L, lucky i) ∧ (∀ i ∈ U, ¬ lucky i)
  · rw [ite_eq_left h]
    exact Finset.prod_eq_one fun i _ => ite_eq_left ⟨h.1 i, h.2 i⟩
  · rw [ite_eq_right h]
    have hbad : ∃ i, ¬ ((i ∈ L → lucky i) ∧ (i ∈ U → ¬ lucky i)) := by
      by_contra hc
      simp only [not_exists, not_not] at hc
      exact h ⟨fun i => (hc i).1, fun i => (hc i).2⟩
    obtain ⟨i, hi⟩ := hbad
    exact Finset.prod_eq_zero (Finset.mem_univ i) (ite_eq_right hi)

open Classical in
private theorem sum_linearStatusWeight (n : ℕ) (L U : Finset (Fin n)) :
    (∑ f : {f : Fin n → Fin n // IsParkingFunction n f},
      ∏ i : Fin n, statusWeight (i ∈ L) (i ∈ U) (IsLuckyCar f.val i)) =
      (Nat.card { f : Fin n → Fin n // IsParkingFunction n f ∧
        (∀ i ∈ L, IsLuckyCar f i) ∧ (∀ i ∈ U, ¬ IsLuckyCar f i) } : ℚ) := by
  let ok (f : Fin n → Fin n) := (∀ i ∈ L, IsLuckyCar f i) ∧ (∀ i ∈ U, ¬ IsLuckyCar f i)
  let e : { f : {f : Fin n → Fin n // IsParkingFunction n f} // ok f.val } ≃
      { f : Fin n → Fin n // IsParkingFunction n f ∧ ok f } :=
    { toFun := fun ⟨⟨f, hf⟩, hok⟩ => ⟨f, hf, hok⟩
      invFun := fun ⟨f, hf, hok⟩ => ⟨⟨f, hf⟩, hok⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  simp_rw [prod_statusWeight]
  change (∑ f : {f : Fin n → Fin n // IsParkingFunction n f}, if ok f.val then 1 else 0) = _
  rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const_zero, add_zero, nsmul_eq_mul, mul_one,
    ← Fintype.card_subtype, ← Nat.card_eq_fintype_card, Nat.card_congr e]

-- Split the circular runs by their unique empty spot. Every fiber is a rotation of the
-- fiber over the extra spot, where the circular and linear parking rules agree.
private theorem sum_prescribedCircleWeight_eq_linear (n : ℕ) (L U : Finset (Fin n)) :
    (∑ g : Fin n → ZMod (n + 1), prescribedCircleWeight g le_rfl (· ∈ L) (· ∈ U)) =
      (n + 1 : ℚ) * (Nat.card { f : Fin n → Fin n // IsParkingFunction n f ∧
        (∀ i ∈ L, IsLuckyCar f i) ∧ (∀ i ∈ U, ¬ IsLuckyCar f i) } : ℚ) := by
  classical
  let w (g : Fin n → ZMod (n + 1)) := prescribedCircleWeight g le_rfl (· ∈ L) (· ∈ U)
  let e := (StoSigma n n le_rfl).symm.trans
    (((Equiv.prodComm (Fin n → ZMod (n + 1)) (ZMod (n + 1))).subtypeEquiv
      (by intro p; rfl)).trans (TtoSigma n n le_rfl))
  have hfixed :
      (∑ g : {g : Fin n → ZMod (n + 1) // extra n ∈ parkEmpty n n g le_rfl}, w g.val) =
        ∑ f : {f : Fin n → Fin n // IsParkingFunction n f},
          ∏ i : Fin n, statusWeight (i ∈ L) (i ∈ U) (IsLuckyCar f.val i) := by
    symm
    refine Fintype.sum_equiv (PfEquiv n n le_rfl) _ _ fun f => ?_
    change (∏ i : Fin n, statusWeight (i ∈ L) (i ∈ U) (IsLuckyCar f.val i)) =
      prescribedCircleWeight (lift n n f.val) le_rfl (· ∈ L) (· ∈ U)
    simp_rw [prescribedCircleWeight, isLuckyCar_iff_not_mem_parkOcc f.val f.property]
  calc
    _ = ∑ g : Fin n → ZMod (n + 1), ∑ _x : ↥(parkEmpty n n g le_rfl), w g := by
      simp [w, Finset.sum_const, card_parkEmpty]
    _ = ∑ x : ZMod (n + 1), ∑ g : {g : Fin n → ZMod (n + 1) // x ∈ parkEmpty n n g le_rfl},
          w g.val := by
      simp only [Finset.sum_sigma', Finset.univ_sigma_univ]
      exact Fintype.sum_equiv e _ _ (fun _ => rfl)
    _ = _ := by
      have hfiber (x : ZMod (n + 1)) :
          (∑ g : {g : Fin n → ZMod (n + 1) // x ∈ parkEmpty n n g le_rfl}, w g.val) =
            ∑ g : {g : Fin n → ZMod (n + 1) // extra n ∈ parkEmpty n n g le_rfl}, w g.val :=
        Fintype.sum_equiv (fiberEquiv n n le_rfl x) _ _
          (fun g => (prescribedCircleWeight_translate g.val (· ∈ L) (· ∈ U) (extra n - x)).symm)
      simp_rw [hfiber, hfixed, sum_linearStatusWeight, Finset.sum_const, Finset.card_univ,
        ZMod.card, nsmul_eq_mul, Nat.cast_add, Nat.cast_one]

open Classical in
private theorem prod_preferenceCount (n : ℕ) (L U : Finset (Fin n)) (hLU : Disjoint L U) :
    (∏ i : Fin n, preferenceCount n i.val (i ∈ L) (i ∈ U)) =
      (∏ i ∈ L, ((n + 1 - i.val : ℕ) : ℚ)) * (∏ i ∈ U, (i.val : ℚ)) *
        (n + 1 : ℚ) ^ (L ∪ U)ᶜ.card := by
  rw [← Finset.prod_const (s := (L ∪ U)ᶜ), ← Fintype.prod_ite_mem L, ← Fintype.prod_ite_mem U,
    ← Fintype.prod_ite_mem (L ∪ U)ᶜ, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  by_cases hl : i ∈ L
  · have hu : i ∉ U := fun hu => Finset.disjoint_left.mp hLU hl hu
    simp [preferenceCount, hl, hu]
  · by_cases hu : i ∈ U <;> simp [preferenceCount, hl, hu]

/-- **Parking functions with prescribed lucky and unlucky cars.** Number the cars and spots
$0, \dots, n-1$, and let $L$ and $U$ be disjoint sets of cars. The number of parking functions
of length $n$ in which every car in $L$ is lucky and no car in $U$ is lucky equals
$$\prod_{i \in L} (n + 1 - i) \cdot \prod_{i \in U} i \cdot (n + 1)^{n - |L| - |U| - 1},$$
where the power is taken in $\mathbb{Q}$, so the exponent may be negative.

In the paper's numbering of cars from $1$, the factors are $n + 2 - i$ and $i - 1$.

Source: Steve Butler et al., "Lucky Cars and Lucky Spots in
Parking Functions", Theorem 4. -/
theorem card_parking_lucky_on (n : ℕ) (L U : Finset (Fin n))
    (hLU : Disjoint L U) :
    (Nat.card { f : Fin n → Fin n // IsParkingFunction n f ∧
        (∀ i ∈ L, IsLuckyCar f i) ∧
          (∀ i ∈ U, ¬ IsLuckyCar f i) } : ℚ) =
      (∏ i ∈ L, ((n + 1 - i.val : ℕ) : ℚ)) *
        (∏ i ∈ U, (i.val : ℚ)) *
        ((n + 1 : ℚ)) ^ ((n : ℤ) - L.card - U.card - 1) := by
  classical
  have hb : (n + 1 : ℚ) ≠ 0 := by positivity
  have hk : ((L ∪ U)ᶜ.card : ℤ) = (n : ℤ) - L.card - U.card := by
    have h := Finset.card_compl_add_card (L ∪ U)
    rw [Finset.card_union_of_disjoint hLU, Fintype.card_fin] at h
    omega
  calc
    _ = (∑ g : Fin n → ZMod (n + 1), prescribedCircleWeight g le_rfl (· ∈ L) (· ∈ U)) /
          (n + 1 : ℚ) := by
      rw [sum_prescribedCircleWeight_eq_linear, mul_comm, mul_div_cancel_right₀ _ hb]
    _ = _ := by
      rw [sum_prescribedCircleWeight n n le_rfl _ _
          (fun i h => Finset.disjoint_left.mp hLU h.1 h.2), prod_preferenceCount n L U hLU,
        div_eq_mul_inv, mul_assoc, ← zpow_natCast, ← zpow_neg_one, ← zpow_add₀ hb, hk,
        sub_eq_add_neg (_ - _ - _) (1 : ℤ)]

end MathlibExt.Combinatorics.Enumerative.LuckyCarsWanted
