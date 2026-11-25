/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import CSLibExt.Computability.Complexity.Classes

/-!
# Parity is not in AC0

The parity language is not in `AC0`: no polynomial-size, constant-depth, unbounded fan-in
AND/OR/NOT circuit family computes parity. `AC0` and `parityDec` are the shared definitions.

The main result is `parity_not_in_ac0`. Its proof is the polynomial method of Razborov and
Smolensky over `ZMod 3`, for the flat circuits of `AC0` (lists of gates, each gate reading only
earlier gates):

* **Approximation.** Fix `l ≥ 1` and a family `r` of `l` sets of gates. An OR gate whose inputs
  have approximations `u_a` (`a ∈ A`) is approximated by `1 - ∏ i, (1 - (∑ a ∈ A ∩ r i, u_a) ^ 2)`,
  and an AND gate by its De Morgan dual. The approximation of a gate of depth `t` is a function of
  degree at most `(2 l) ^ t` on the cube, and it equals the value of the gate on every input where
  no gate's approximation fails. For a fixed input and a fixed gate, at most one family `r` in
  `2 ^ l` makes this gate fail (toggling one true input of the gate in a set changes the count by
  one), so averaging over `r` gives a family that fails on at most an `s / 2 ^ l` fraction of the
  inputs, where `s` is the number of gates.
* **Smolensky's bound.** In the `±1` basis parity is the character `χ_univ`. On the set where a
  function `f` of degree at most `D` agrees with `χ_univ`, every character `χ_I` with
  `|I| > n / 2 + D` agrees with `f * χ_{Iᶜ}`, so every function on that set agrees there with a
  function of degree at most `n / 2 + D`. A dimension count bounds the set by the number of subsets
  of size at most `n / 2 + D`, fewer than three quarters of all points when `n` is even and
  `16 (D + 1) ^ 2 < n + 1`.
* **Parameters.** If the circuit on `n` inputs has at most `p(n)` gates and depth at most `d`,
  then for `n = 2 ^ t` it has at most `c n ^ e` gates, where `c = p(1)` and `e` is the degree of
  `p`. Taking `l = t e + c + 2` makes the approximation fail on at most a quarter of the inputs,
  and for large `t` the degree `D = (2 l) ^ d` satisfies `16 (D + 1) ^ 2 < n + 1`.

Sources for the method: A. A. Razborov, "Lower bounds on the size of bounded depth networks over
a complete basis with logical addition", Mat. Zametki 41 (1987), 598-607; English translation
Math. Notes 41 (1987), 333-338; R. Smolensky, "Algebraic methods in the theory of lower bounds
for Boolean circuit complexity", Proceedings of the Nineteenth Annual ACM Symposium on Theory of
Computing (STOC 1987), 77-82.

Source:
M. Furst, J. Saxe, and M. Sipser, "Parity, circuits, and the polynomial-time hierarchy",
Mathematical Systems Theory 17 (1984), 13-27; M. Ajtai, "Σ₁¹-formulae on finite structures",
Annals of Pure and Applied Logic 24 (1983), 1-48; J. Håstad, "Almost optimal lower bounds for
small depth circuits", Proceedings of the Eighteenth Annual ACM Symposium on Theory of
Computing (STOC 1986), 6-20.
-/

@[expose] public section

namespace MetaMathlibExt.Complexity.KeyTheorems.ParityNotInAC0

open Cslib.Complexity.Classes
open MetaMathlibExt.ComplexityTheory

/-! ### Flat circuits as left folds -/

private theorem foldl_snoc_prefix {α β : Type*} (f : List β → α → β) (C : List α)
    (acc : List β) : ∃ t, C.foldl (fun vs g => vs ++ [f vs g]) acc = acc ++ t := by
  induction C generalizing acc with
  | nil => exact ⟨[], by simp⟩
  | cons g C ih =>
    obtain ⟨t, ht⟩ := ih (acc ++ [f acc g])
    exact ⟨[f acc g] ++ t, by simp [List.foldl_cons, ht]⟩

private theorem length_foldl_snoc {α β : Type*} (f : List β → α → β) (C : List α)
    (acc : List β) :
    (C.foldl (fun vs g => vs ++ [f vs g]) acc).length = acc.length + C.length := by
  induction C generalizing acc with
  | nil => simp
  | cons g C ih => simp [ih]; omega

private theorem getD_foldl_snoc {α β : Type*} (f : List β → α → β) (C : List α) (d : β)
    {j : ℕ} (hj : j < C.length) :
    (C.foldl (fun vs g => vs ++ [f vs g]) []).getD j d =
      f ((C.foldl (fun vs g => vs ++ [f vs g]) []).take j) C[j] := by
  set P := (C.take j).foldl (fun vs g => vs ++ [f vs g]) [] with hP
  have hPlen : P.length = j := by
    simp [hP, length_foldl_snoc, List.length_take, Nat.min_eq_left hj.le]
  obtain ⟨t, ht⟩ := foldl_snoc_prefix f (C.drop (j + 1)) (P ++ [f P C[j]])
  have key : C.foldl (fun vs g => vs ++ [f vs g]) [] = P ++ [f P C[j]] ++ t := by
    calc C.foldl (fun vs g => vs ++ [f vs g]) []
        = (C.take j ++ C.drop j).foldl (fun vs g => vs ++ [f vs g]) [] := by
          rw [List.take_append_drop]
      _ = (C.drop j).foldl (fun vs g => vs ++ [f vs g]) P := List.foldl_append ..
      _ = (C.drop (j + 1)).foldl (fun vs g => vs ++ [f vs g]) (P ++ [f P C[j]]) := by
          rw [List.drop_eq_getElem_cons hj, List.foldl_cons]
      _ = _ := ht
  rw [key]
  have htake : (P ++ [f P C[j]] ++ t).take j = P := by
    rw [List.append_assoc, List.take_append_of_le_length (by omega), List.take_of_length_le
      (by omega)]
  rw [htake]
  simp [List.getD_eq_getElem?_getD, hPlen]

/-! ### Functions of low degree over `ZMod 3` -/

/-- The `±1` encoding of a bit in `ZMod 3`. -/
private def sgn (b : Bool) : ZMod 3 := if b then -1 else 1

/-- The character `χ_I(x) = ∏_{i ∈ I} (-1)^{x_i}` over `ZMod 3`. -/
private def chi {n : ℕ} (I : Finset (Fin n)) (x : Fin n → Bool) : ZMod 3 := ∏ i ∈ I, sgn (x i)

/-- Functions of degree at most `k`: the span of the characters `χ_I` with `|I| ≤ k`. -/
private def degLE (n k : ℕ) : Submodule (ZMod 3) ((Fin n → Bool) → ZMod 3) :=
  Submodule.span (ZMod 3) (Set.range fun I : {I : Finset (Fin n) // I.card ≤ k} => chi I.1)

private theorem sgn_mul_self (b : Bool) : sgn b * sgn b = 1 := by
  cases b <;> decide

private theorem chi_mem_degLE {n k : ℕ} (I : Finset (Fin n)) (hI : I.card ≤ k) :
    chi I ∈ degLE n k :=
  Submodule.subset_span ⟨⟨I, hI⟩, rfl⟩

private theorem degLE_mono {n a b : ℕ} (h : a ≤ b) : degLE n a ≤ degLE n b :=
  Submodule.span_mono (by rintro _ ⟨⟨I, hI⟩, rfl⟩; exact ⟨⟨I, hI.trans h⟩, rfl⟩)

private theorem one_mem_degLE {n : ℕ} (k : ℕ) : (1 : (Fin n → Bool) → ZMod 3) ∈ degLE n k := by
  have h : chi (∅ : Finset (Fin n)) = 1 := by funext x; simp [chi]
  rw [← h]
  exact chi_mem_degLE ∅ (by simp)

private theorem const_mem_degLE {n : ℕ} (c : ZMod 3) (k : ℕ) :
    (fun _ : Fin n → Bool => c) ∈ degLE n k := by
  have h : (fun _ : Fin n → Bool => c) = c • (1 : (Fin n → Bool) → ZMod 3) := by
    funext x; simp
  rw [h]
  exact Submodule.smul_mem _ _ (one_mem_degLE k)

private theorem sgn_mul_chi {n : ℕ} (i : Fin n) (K : Finset (Fin n)) :
    ∃ K' : Finset (Fin n), K'.card ≤ K.card + 1 ∧ (fun x => sgn (x i)) * chi K = chi K' := by
  by_cases hi : i ∈ K
  · refine ⟨K.erase i, by rw [Finset.card_erase_of_mem hi]; omega, ?_⟩
    funext x
    simp only [Pi.mul_apply, chi]
    rw [← Finset.mul_prod_erase K _ hi, ← mul_assoc, sgn_mul_self, one_mul]
  · refine ⟨insert i K, by simp [Finset.card_insert_of_notMem hi], ?_⟩
    funext x
    simp only [Pi.mul_apply, chi]
    rw [Finset.prod_insert hi]

private theorem chi_mul_chi {n : ℕ} (I J : Finset (Fin n)) :
    ∃ K : Finset (Fin n), K.card ≤ I.card + J.card ∧ chi I * chi J = chi K := by
  induction I using Finset.induction_on with
  | empty => exact ⟨J, by simp, by funext x; simp [chi]⟩
  | insert i I hi ih =>
    obtain ⟨K₁, hK₁, hK₁e⟩ := ih
    obtain ⟨K₂, hK₂, hK₂e⟩ := sgn_mul_chi i K₁
    refine ⟨K₂, by rw [Finset.card_insert_of_notMem hi]; omega, ?_⟩
    have hins : chi (insert i I) = (fun x => sgn (x i)) * chi I := by
      funext x; simp [chi, Finset.prod_insert hi]
    rw [hins, mul_assoc, hK₁e, hK₂e]

private theorem mul_mem_degLE {n a b : ℕ} {f g : (Fin n → Bool) → ZMod 3}
    (hf : f ∈ degLE n a) (hg : g ∈ degLE n b) : f * g ∈ degLE n (a + b) := by
  have h := Submodule.mul_mem_mul hf hg
  rw [degLE, degLE, Submodule.span_mul_span] at h
  refine Submodule.span_mono ?_ h
  rintro _ ⟨_, ⟨⟨I, hI⟩, rfl⟩, _, ⟨⟨J, hJ⟩, rfl⟩, rfl⟩
  obtain ⟨K, hK, hKe⟩ := chi_mul_chi I J
  exact ⟨⟨K, by omega⟩, hKe.symm⟩

private theorem prod_mem_degLE {n : ℕ} {ι : Type*} (s : Finset ι)
    (f : ι → (Fin n → Bool) → ZMod 3) (k : ℕ) (h : ∀ i ∈ s, f i ∈ degLE n k) :
    ∏ i ∈ s, f i ∈ degLE n (s.card * k) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using one_mem_degLE 0
  | insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.card_insert_of_notMem hi]
    have := mul_mem_degLE (h i (by simp)) (ih fun j hj => h j (by simp [hj]))
    exact degLE_mono (by rw [Nat.succ_mul, Nat.add_comm]) this

/-- The `0/1` indicator of a bit, in `ZMod 3`. -/
private def b2z (b : Bool) : ZMod 3 := if b then 1 else 0

private theorem var_mem_degLE {n : ℕ} (i : Fin n) :
    (fun x : Fin n → Bool => b2z (x i)) ∈ degLE n 1 := by
  have h : (fun x : Fin n → Bool => b2z (x i)) =
      (fun _ => (2 : ZMod 3)) - (2 : ZMod 3) • chi {i} := by
    funext x
    simp only [chi, Finset.prod_singleton, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    cases x i <;> decide
  rw [h]
  exact Submodule.sub_mem _ (const_mem_degLE 2 1)
    (Submodule.smul_mem _ _ (chi_mem_degLE {i} (by simp)))

/-- Every function on the cube has degree at most `n`. -/
private theorem mem_degLE_self {n : ℕ} (h : (Fin n → Bool) → ZMod 3) : h ∈ degLE n n := by
  classical
  have hdelta : ∀ a : Fin n → Bool,
      (fun x : Fin n → Bool => if x = a then (1 : ZMod 3) else 0) ∈ degLE n n := by
    intro a
    have heq : (fun x : Fin n → Bool => if x = a then (1 : ZMod 3) else 0) =
        ∏ i : Fin n, ((fun _ => (2 : ZMod 3)) + (2 * sgn (a i)) • chi {i}) := by
      funext x
      rw [Finset.prod_apply]
      have hfac : ∀ i : Fin n, (((fun _ => (2 : ZMod 3)) + (2 * sgn (a i)) • chi {i} :
          (Fin n → Bool) → ZMod 3) x) = if x i = a i then 1 else 0 := by
        intro i
        simp only [chi, Finset.prod_singleton, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
        cases x i <;> cases a i <;> decide
      simp only [hfac, Finset.prod_boole, Finset.mem_univ, true_implies]
      simp [funext_iff]
    rw [heq]
    have := prod_mem_degLE (Finset.univ : Finset (Fin n))
      (fun i => (fun _ => (2 : ZMod 3)) + (2 * sgn (a i)) • chi {i}) 1 (fun i _ =>
        Submodule.add_mem _ (const_mem_degLE 2 1)
          (Submodule.smul_mem _ _ (chi_mem_degLE {i} (by simp))))
    simpa using this
  have hsum : h = ∑ a : Fin n → Bool,
      h a • (fun x : Fin n → Bool => if x = a then (1 : ZMod 3) else 0) := by
    funext x
    simp [Finset.sum_apply]
  rw [hsum]
  exact Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ (hdelta a)

private theorem chi_univ_mul_chi_compl {n : ℕ} (I : Finset (Fin n)) (x : Fin n → Bool) :
    chi Finset.univ x * chi Iᶜ x = chi I x := by
  classical
  have hsq : chi Iᶜ x * chi Iᶜ x = 1 := by
    simp only [chi, ← Finset.prod_mul_distrib, sgn_mul_self, Finset.prod_const_one]
  have huniv : chi Finset.univ x = chi I x * chi Iᶜ x :=
    (Finset.prod_mul_prod_compl I (fun i => sgn (x i))).symm
  rw [huniv, mul_assoc, hsq, mul_one]

/-- **Smolensky's bound.** A function of degree at most `D` agrees with the parity character
`χ_univ` on at most as many points as there are sets of size at most `n / 2 + D`. -/
private theorem card_agree_le {n D : ℕ} (f : (Fin n → Bool) → ZMod 3) (hf : f ∈ degLE n D) :
    (Finset.univ.filter fun x => f x = chi Finset.univ x).card ≤
      (Finset.univ.filter fun I : Finset (Fin n) => I.card ≤ n / 2 + D).card := by
  classical
  set G := Finset.univ.filter fun x => f x = chi Finset.univ x with hG
  set k := n / 2 + D with hk
  let ρ : ((Fin n → Bool) → ZMod 3) →ₗ[ZMod 3] (G → ZMod 3) :=
    LinearMap.funLeft (ZMod 3) (ZMod 3) (Subtype.val : G → (Fin n → Bool))
  have hρ : ∀ I : Finset (Fin n), ρ (chi I) ∈ (degLE n k).map ρ := by
    intro I
    by_cases hI : I.card ≤ k
    · exact Submodule.mem_map_of_mem (chi_mem_degLE I hI)
    · have hcompl : Iᶜ.card ≤ n / 2 := by
        rw [Finset.card_compl, Fintype.card_fin]
        omega
      have hw : f * chi Iᶜ ∈ degLE n k :=
        degLE_mono (by omega) (mul_mem_degLE hf (chi_mem_degLE Iᶜ hcompl))
      refine ⟨f * chi Iᶜ, hw, ?_⟩
      funext x
      obtain ⟨x, hx⟩ := x
      have hfx : f x = chi Finset.univ x := (Finset.mem_filter.1 hx).2
      change f x * chi Iᶜ x = chi I x
      rw [hfx, chi_univ_mul_chi_compl]
  have htop : (⊤ : Submodule (ZMod 3) (G → ZMod 3)) ≤ (degLE n k).map ρ := by
    intro g _
    obtain ⟨h, rfl⟩ := LinearMap.funLeft_surjective_of_injective (ZMod 3) (ZMod 3)
      (Subtype.val : G → (Fin n → Bool)) Subtype.val_injective g
    have hmem : h ∈ degLE n n := mem_degLE_self h
    have hle : (degLE n n).map ρ ≤ (degLE n k).map ρ := by
      rw [degLE, Submodule.map_span, Submodule.span_le]
      rintro _ ⟨_, ⟨⟨I, _⟩, rfl⟩, rfl⟩
      exact hρ I
    exact hle (Submodule.mem_map_of_mem hmem)
  calc G.card = Fintype.card G := (Fintype.card_coe G).symm
    _ = Module.finrank (ZMod 3) (G → ZMod 3) := (Module.finrank_fintype_fun_eq_card _).symm
    _ = Module.finrank (ZMod 3) (⊤ : Submodule (ZMod 3) (G → ZMod 3)) := finrank_top _ _ |>.symm
    _ ≤ Module.finrank (ZMod 3) ((degLE n k).map ρ) := Submodule.finrank_mono htop
    _ ≤ Module.finrank (ZMod 3) (degLE n k) := Submodule.finrank_map_le _ _
    _ ≤ Fintype.card {I : Finset (Fin n) // I.card ≤ k} := finrank_range_le_card _
    _ = _ := Fintype.card_subtype _

/-! ### Counting the subsets of small size -/

/-- `C(2m, m)² (2m + 1) ≤ 16^m`. -/
private theorem centralBinom_sq_mul_le (m : ℕ) : m.centralBinom ^ 2 * (2 * m + 1) ≤ 16 ^ m := by
  induction m with
  | zero => simp
  | succ m ih =>
    have hrec := Nat.succ_mul_centralBinom_succ m
    have hpos : 0 < (m + 1) ^ 2 := by positivity
    refine Nat.le_of_mul_le_mul_left ?_ hpos
    calc (m + 1) ^ 2 * ((m + 1).centralBinom ^ 2 * (2 * (m + 1) + 1))
        = ((m + 1) * (m + 1).centralBinom) ^ 2 * (2 * m + 3) := by ring
      _ = (2 * (2 * m + 1) * m.centralBinom) ^ 2 * (2 * m + 3) := by rw [hrec]
      _ = 4 * ((2 * m + 1) * (2 * m + 3)) * (m.centralBinom ^ 2 * (2 * m + 1)) := by ring
      _ ≤ 4 * ((2 * m + 1) * (2 * m + 3)) * 16 ^ m := Nat.mul_le_mul_left _ ih
      _ ≤ 4 * (4 * (m + 1) ^ 2) * 16 ^ m := by
          refine Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ ?_)
          nlinarith
      _ = (m + 1) ^ 2 * 16 ^ (m + 1) := by ring

/-- Sets of size at most `m + D` in a set of size `2m` are fewer than three quarters of all
subsets once `16 (D + 1)² < 2m + 1`. -/
private theorem four_mul_card_small_lt (m D : ℕ) (hD : 16 * (D + 1) ^ 2 < 2 * m + 1) :
    4 * (Finset.univ.filter fun I : Finset (Fin (2 * m)) => I.card ≤ m + D).card <
      3 * 4 ^ m := by
  classical
  set A := Finset.univ.filter fun I : Finset (Fin (2 * m)) => I.card < m with hA
  set B := Finset.univ.filter fun I : Finset (Fin (2 * m)) => m < I.card with hB
  set M := Finset.univ.filter fun I : Finset (Fin (2 * m)) => m ≤ I.card ∧ I.card ≤ m + D
    with hM
  have hcard_univ : (Finset.univ : Finset (Finset (Fin (2 * m)))).card = 4 ^ m := by
    rw [Finset.card_univ, Fintype.card_finset, Fintype.card_fin, pow_mul]; norm_num
  -- `2 |A| ≤ 4^m`, by complementation `A → B`
  have hAB : A.card ≤ B.card := by
    refine Finset.card_le_card_of_injOn (fun I => Iᶜ) ?_ ?_
    · intro I hI
      simp only [hA, hB, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hI ⊢
      rw [Finset.card_compl, Fintype.card_fin]
      omega
    · intro I _ J _ h
      exact compl_injective h
  have hdisj : Disjoint A B := by
    rw [Finset.disjoint_filter]
    intro I _ h1 h2
    omega
  have hAB' : A.card + B.card ≤ 4 ^ m := by
    rw [← Finset.card_union_of_disjoint hdisj, ← hcard_univ]
    exact Finset.card_le_univ _
  -- `|M| ≤ (D + 1) C(2m, m)`
  have hMle : M.card ≤ (D + 1) * m.centralBinom := by
    have hsub : M ⊆ (Finset.Icc m (m + D)).biUnion fun i => Finset.powersetCard i Finset.univ := by
      intro I hI
      simp only [hM, Finset.mem_filter, Finset.mem_univ, true_and] at hI
      simp only [Finset.mem_biUnion, Finset.mem_Icc, Finset.mem_powersetCard]
      exact ⟨I.card, hI, Finset.subset_univ _, rfl⟩
    calc M.card ≤ _ := Finset.card_le_card hsub
      _ ≤ ∑ i ∈ Finset.Icc m (m + D), (Finset.powersetCard i
            (Finset.univ : Finset (Fin (2 * m)))).card := Finset.card_biUnion_le
      _ ≤ ∑ _i ∈ Finset.Icc m (m + D), m.centralBinom := by
          refine Finset.sum_le_sum fun i _ => ?_
          rw [Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin,
            Nat.centralBinom_eq_two_mul_choose]
          have := Nat.choose_le_middle i (2 * m)
          rwa [Nat.mul_div_cancel_left m two_pos] at this
      _ = (D + 1) * m.centralBinom := by
          simp only [Finset.sum_const, Nat.card_Icc, smul_eq_mul]
          congr 1
          omega
  have hsplit : (Finset.univ.filter fun I : Finset (Fin (2 * m)) => I.card ≤ m + D).card ≤
      A.card + M.card := by
    refine (Finset.card_le_card ?_).trans (Finset.card_union_le A M)
    intro I hI
    simp only [hA, hM, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union] at hI ⊢
    omega
  -- `4 (D + 1) C(2m, m) < 4^m`
  have hcb : 4 * ((D + 1) * m.centralBinom) < 4 ^ m := by
    have hc := centralBinom_sq_mul_le m
    have hpos := m.centralBinom_pos
    rw [← Nat.pow_lt_pow_iff_left (two_ne_zero)]
    calc (4 * ((D + 1) * m.centralBinom)) ^ 2
        = 16 * (D + 1) ^ 2 * m.centralBinom ^ 2 := by ring
      _ < (2 * m + 1) * m.centralBinom ^ 2 :=
          Nat.mul_lt_mul_of_pos_right hD (by positivity)
      _ = m.centralBinom ^ 2 * (2 * m + 1) := by ring
      _ ≤ 16 ^ m := hc
      _ = (4 ^ m) ^ 2 := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
  omega

/-! ### Razborov's approximation of OR gates -/


/-- Razborov's approximation of an OR. -/
private def orApprox {l : ℕ} (r : Fin l → Finset ℕ) (A : Finset ℕ) (u : ℕ → ZMod 3) : ZMod 3 :=
  1 - ∏ i, (1 - (∑ a ∈ A ∩ r i, u a) ^ 2)

private theorem sq_eq_one_of_ne_zero (z : ZMod 3) (hz : z ≠ 0) : z ^ 2 = 1 := by
  revert z; decide

private theorem orApprox_b2z {l : ℕ} (r : Fin l → Finset ℕ) (A : Finset ℕ) (v : ℕ → Bool)
    (h : ¬ ((A.filter fun a => v a = true).Nonempty ∧
      ∀ i, ((A.filter fun a => v a = true) ∩ r i).card % 3 = 0)) :
    orApprox r A (fun a => b2z (v a)) = b2z (decide (A.filter fun a => v a = true).Nonempty) := by
  classical
  set T := A.filter fun a => v a = true with hTdef
  have hsum : ∀ i, ∑ a ∈ A ∩ r i, b2z (v a) = ((T ∩ r i).card : ZMod 3) := by
    intro i
    simp only [b2z]
    rw [Finset.sum_boole]
    congr 2
    ext a
    simp only [hTdef, Finset.mem_filter, Finset.mem_inter]
    tauto
  by_cases hT : T.Nonempty
  · obtain ⟨i, hi⟩ : ∃ i, (T ∩ r i).card % 3 ≠ 0 := by
      by_contra hcon
      exact h ⟨hT, fun i => by_contra fun hi => hcon ⟨i, hi⟩⟩
    have hz : ((T ∩ r i).card : ZMod 3) ≠ 0 := by
      rw [Ne, ZMod.natCast_eq_zero_iff]
      omega
    rw [orApprox, Finset.prod_eq_zero (Finset.mem_univ i)
      (by rw [hsum, sq_eq_one_of_ne_zero _ hz, sub_self])]
    simp [b2z, hT]
  · rw [Finset.not_nonempty_iff_eq_empty] at hT
    have h0 : ∀ i, ∑ a ∈ A ∩ r i, b2z (v a) = 0 := by simp [hsum, hT]
    simp only [orApprox, h0]
    simp [b2z, hT]

/-- For a nonempty `T ⊆ U`, at most half of the subsets `S ⊆ U` meet `T` in a multiple of three
elements. -/
private theorem two_mul_card_bad_le (U T : Finset ℕ) (hTU : T ⊆ U) (hT : T.Nonempty) :
    2 * (U.powerset.filter fun S => (T ∩ S).card % 3 = 0).card ≤ 2 ^ U.card := by
  classical
  obtain ⟨a, ha⟩ := hT
  set φ : Finset ℕ → Finset ℕ := fun S => if a ∈ S then S.erase a else insert a S with hφ
  have hφφ : ∀ S, φ (φ S) = S := by
    intro S
    by_cases h : a ∈ S
    · simp [hφ, h]
    · simp [hφ, h]
  have hcard : ∀ S, (T ∩ S).card % 3 = 0 → (T ∩ φ S).card % 3 ≠ 0 := by
    intro S hS
    by_cases h : a ∈ S
    · have hmem : a ∈ T ∩ S := Finset.mem_inter.2 ⟨ha, h⟩
      have hpos := Finset.card_pos.2 ⟨a, hmem⟩
      simp only [hφ, h, ↓reduceIte, Finset.inter_erase, Finset.card_erase_of_mem hmem]
      omega
    · have hnmem : a ∉ T ∩ S := fun h' => h (Finset.mem_inter.1 h').2
      simp only [hφ, h, ↓reduceIte, Finset.inter_insert_of_mem ha,
        Finset.card_insert_of_notMem hnmem]
      omega
  have hle : (U.powerset.filter fun S => (T ∩ S).card % 3 = 0).card ≤
      (U.powerset.filter fun S => ¬ (T ∩ S).card % 3 = 0).card := by
    refine Finset.card_le_card_of_injOn φ ?_ ?_
    · intro S hS
      simp only [Finset.coe_filter, Finset.mem_powerset, Set.mem_ofPred_eq] at hS ⊢
      refine ⟨?_, hcard S hS.2⟩
      by_cases h : a ∈ S
      · simp only [hφ, h, ↓reduceIte]
        exact (Finset.erase_subset a S).trans hS.1
      · simp only [hφ, h, ↓reduceIte]
        exact Finset.insert_subset (hTU ha) hS.1
    · intro S _ S' _ hSS'
      rw [← hφφ S, ← hφφ S']
      exact congrArg φ hSS'
  have htot := Finset.card_filter_add_card_filter_not (s := U.powerset)
    (fun S => (T ∩ S).card % 3 = 0)
  rw [Finset.card_powerset] at htot
  omega

/-- Probability of failure of an approximated gate: at most one in `2 ^ l` families
`r : Fin l → 𝒫 U` are bad. -/
private theorem card_fail_le (l : ℕ) (U T : Finset ℕ) (hTU : T ⊆ U) :
    2 ^ l * ((Fintype.piFinset fun _ : Fin l => U.powerset).filter
      fun r => T.Nonempty ∧ ∀ i, (T ∩ r i).card % 3 = 0).card ≤ (2 ^ U.card) ^ l := by
  classical
  by_cases hT : T.Nonempty
  · have heq : ((Fintype.piFinset fun _ : Fin l => U.powerset).filter
        fun r => T.Nonempty ∧ ∀ i, (T ∩ r i).card % 3 = 0) =
        Fintype.piFinset fun _ : Fin l => U.powerset.filter fun S => (T ∩ S).card % 3 = 0 := by
      ext r
      simp only [Finset.mem_filter, Fintype.mem_piFinset, hT, true_and]
      constructor
      · rintro ⟨h1, h2⟩ i
        exact ⟨h1 i, h2 i⟩
      · intro h
        exact ⟨fun i => (h i).1, fun i => (h i).2⟩
    rw [heq, Fintype.card_piFinset, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
      ← mul_pow]
    exact Nat.pow_le_pow_left (two_mul_card_bad_le U T hTU hT) l
  · simp [hT]

/-! ### The approximating functions of a circuit -/

private theorem getD_take_of_lt {α : Type*} (l : List α) (d : α) {j a : ℕ} (h : a < j) :
    (l.take j).getD a d = l.getD a d := by
  simp [List.getD_eq_getElem?_getD, h]

private theorem all_congr_of_mem {α : Type*} (L : List α) {p q : α → Bool}
    (h : ∀ a ∈ L, p a = q a) : L.all p = L.all q := by
  induction L with
  | nil => rfl
  | cons b L ih =>
    simp only [List.all_cons, h b (by simp), ih fun a ha => h a (by simp [ha])]

private theorem any_congr_of_mem {α : Type*} (L : List α) {p q : α → Bool}
    (h : ∀ a ∈ L, p a = q a) : L.any p = L.any q := by
  induction L with
  | nil => rfl
  | cons b L ih =>
    simp only [List.any_cons, h b (by simp), ih fun a ha => h a (by simp [ha])]

private theorem gateValue_take {n : ℕ} (vs : List Bool) (x : Fin n → Bool) (g : ACGate n)
    {j : ℕ} (h : ∀ a ∈ gateInputs g, a < j) : gateValue (vs.take j) x g = gateValue vs x g := by
  cases g with
  | var i => rfl
  | const b => rfl
  | notGate a =>
    simp only [gateValue]
    rw [getD_take_of_lt _ _ (h a (by simp [gateInputs]))]
  | andGate L =>
    exact all_congr_of_mem L fun a ha => getD_take_of_lt _ _ (h a (by simpa [gateInputs]))
  | orGate L =>
    exact any_congr_of_mem L fun a ha => getD_take_of_lt _ _ (h a (by simpa [gateInputs]))
  | modGate m L =>
    simp only [gateValue]
    rw [List.filter_congr fun a ha => getD_take_of_lt vs false (h a (by simpa [gateInputs]))]

private theorem gateDepthOf_take {n : ℕ} (ds : List ℕ) (g : ACGate n) {j : ℕ}
    (h : ∀ a ∈ gateInputs g, a < j) : gateDepthOf (ds.take j) g = gateDepthOf ds g := by
  cases g with
  | var i => rfl
  | const b => rfl
  | notGate a =>
    simp only [gateDepthOf]
    rw [getD_take_of_lt _ _ (h a (by simp [gateInputs]))]
  | andGate L =>
    simp only [gateDepthOf]
    rw [List.map_congr_left fun a ha => getD_take_of_lt ds 0 (h a (by simpa [gateInputs]))]
  | orGate L =>
    simp only [gateDepthOf]
    rw [List.map_congr_left fun a ha => getD_take_of_lt ds 0 (h a (by simpa [gateInputs]))]
  | modGate m L =>
    simp only [gateDepthOf]
    rw [List.map_congr_left fun a ha => getD_take_of_lt ds 0 (h a (by simpa [gateInputs]))]

private theorem orApprox_congr {l : ℕ} (r : Fin l → Finset ℕ) (A : Finset ℕ)
    {u u' : ℕ → ZMod 3} (h : ∀ a ∈ A, u a = u' a) : orApprox r A u = orApprox r A u' := by
  simp only [orApprox]
  congr 1
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [Finset.sum_congr rfl fun a ha => h a (Finset.mem_inter.1 ha).1]

/-- The approximating function of a gate, given those of the earlier gates: an OR gate is
replaced by Razborov's approximation `orApprox` with the sets `r`, and an AND gate by its
De Morgan dual. -/
private def approxGate {n l : ℕ} (r : Fin l → Finset ℕ) (Ps : List ((Fin n → Bool) → ZMod 3)) :
    ACGate n → (Fin n → Bool) → ZMod 3
  | .var i => fun x => b2z (x i)
  | .const b => fun _ => b2z b
  | .notGate a => fun x => 1 - Ps.getD a 0 x
  | .andGate L => fun x => 1 - orApprox r L.toFinset (fun a => 1 - Ps.getD a 0 x)
  | .orGate L => fun x => orApprox r L.toFinset (fun a => Ps.getD a 0 x)
  | .modGate _ _ => 0

/-- The approximating functions of all gates of a circuit. -/
private def approxList {n l : ℕ} (r : Fin l → Finset ℕ) (C : List (ACGate n)) :
    List ((Fin n → Bool) → ZMod 3) :=
  C.foldl (fun Ps g => Ps ++ [approxGate r Ps g]) []

private theorem approxGate_take {n l : ℕ} (r : Fin l → Finset ℕ)
    (Ps : List ((Fin n → Bool) → ZMod 3)) (g : ACGate n) {j : ℕ}
    (h : ∀ a ∈ gateInputs g, a < j) : approxGate r (Ps.take j) g = approxGate r Ps g := by
  cases g with
  | var i => rfl
  | const b => rfl
  | notGate a =>
    funext x
    simp only [approxGate]
    rw [getD_take_of_lt _ _ (h a (by simp [gateInputs]))]
  | andGate L =>
    funext x
    simp only [approxGate]
    rw [orApprox_congr r _ fun a ha => by
      rw [getD_take_of_lt _ _ (h a (by simpa [gateInputs] using ha))]]
  | orGate L =>
    funext x
    simp only [approxGate]
    rw [orApprox_congr r _ fun a ha => by
      rw [getD_take_of_lt _ _ (h a (by simpa [gateInputs] using ha))]]
  | modGate m L => rfl

/-- The children of a gate whose value makes Razborov's approximation of that gate fail: the
true inputs of an OR gate, and the false inputs of an AND gate. -/
private def witness {n : ℕ} (V : List Bool) : ACGate n → Finset ℕ
  | .andGate L => L.toFinset.filter fun a => (!V.getD a false) = true
  | .orGate L => L.toFinset.filter fun a => V.getD a false = true
  | _ => ∅

/-- The approximation of gate `g` fails for the gate values `V` and the sets `r`. -/
private def Fails {n l : ℕ} (r : Fin l → Finset ℕ) (V : List Bool) (g : ACGate n) : Prop :=
  (witness V g).Nonempty ∧ ∀ i, ((witness V g) ∩ r i).card % 3 = 0

private theorem one_sub_b2z (b : Bool) : 1 - b2z b = b2z (!b) := by
  cases b <;> decide

/-- Off the failure set, the approximating functions compute the circuit. -/
private theorem approx_correct {n l : ℕ} (r : Fin l → Finset ℕ) {C : List (ACGate n)}
    (hWF : WellFormedCircuit C) (hMF : IsModFree C) (x : Fin n → Bool)
    (hgood : ∀ j (hj : j < C.length), ¬ Fails r (circuitEval C x) C[j]) :
    ∀ j < C.length, (approxList r C).getD j 0 x = b2z ((circuitEval C x).getD j false) := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
  intro hj
  set V := circuitEval C x with hVdef
  set P := approxList r C with hPdef
  have hin : ∀ a ∈ gateInputs C[j], a < j := hWF j hj
  have hV : V.getD j false = gateValue V x C[j] := by
    rw [hVdef, circuitEval, getD_foldl_snoc _ _ _ hj, gateValue_take _ _ _ hin]
  have hP : P.getD j 0 = approxGate r P C[j] := by
    rw [hPdef, approxList, getD_foldl_snoc _ _ _ hj, approxGate_take _ _ _ hin]
  have ihc : ∀ a ∈ gateInputs C[j], P.getD a 0 x = b2z (V.getD a false) :=
    fun a ha => ih a (hin a ha) ((hin a ha).trans hj)
  have hmf := hMF C[j] (List.getElem_mem hj)
  have hg := hgood j hj
  rw [hP, hV]
  generalize C[j] = g at hin ihc hmf hg
  cases g with
  | var i => rfl
  | const b => rfl
  | notGate a =>
    simp only [approxGate, gateValue]
    rw [ihc a (by simp [gateInputs]), one_sub_b2z]
  | orGate L =>
    simp only [approxGate, gateValue]
    rw [orApprox_congr r L.toFinset (u' := fun a => b2z (V.getD a false))
      fun a ha => ihc a (by simpa [gateInputs] using ha)]
    rw [orApprox_b2z r L.toFinset (fun a => V.getD a false) hg]
    congr 1
    simp only [Finset.filter_nonempty_iff, List.mem_toFinset]
    rw [Bool.eq_iff_iff, decide_eq_true_iff, List.any_eq_true]
  | andGate L =>
    simp only [approxGate, gateValue]
    rw [orApprox_congr r L.toFinset (u' := fun a => b2z (!V.getD a false))
      fun a ha => by rw [ihc a (by simpa [gateInputs] using ha), one_sub_b2z]]
    rw [orApprox_b2z r L.toFinset (fun a => !V.getD a false) hg, one_sub_b2z]
    congr 1
    simp only [Finset.filter_nonempty_iff, List.mem_toFinset, Bool.not_eq_true']
    rw [Bool.eq_iff_iff, Bool.not_eq_true', decide_eq_false_iff_not, List.all_eq_true]
    simp
  | modGate m L => exact hmf.elim

private theorem orApprox_mem_degLE {n l : ℕ} (r : Fin l → Finset ℕ) (A : Finset ℕ)
    (u : ℕ → (Fin n → Bool) → ZMod 3) (k : ℕ) (hu : ∀ a ∈ A, u a ∈ degLE n k) :
    (fun x => orApprox r A (fun a => u a x)) ∈ degLE n (l * (2 * k)) := by
  have heq : (fun x => orApprox r A (fun a => u a x)) =
      1 - ∏ i, (1 - (∑ a ∈ A ∩ r i, u a) ^ 2) := by
    funext x
    simp [orApprox, Finset.prod_apply, Finset.sum_apply]
  rw [heq]
  refine Submodule.sub_mem _ (one_mem_degLE _) ?_
  have := prod_mem_degLE Finset.univ (fun i => 1 - (∑ a ∈ A ∩ r i, u a) ^ 2) (2 * k)
    fun i _ => by
      refine Submodule.sub_mem _ (one_mem_degLE _) ?_
      have hs : ∑ a ∈ A ∩ r i, u a ∈ degLE n k :=
        Submodule.sum_mem _ fun a ha => hu a (Finset.mem_inter.1 ha).1
      rw [pow_two, two_mul]
      exact mul_mem_degLE hs hs
  simpa using this

private theorem le_foldr_max {L : List ℕ} {a : ℕ} (h : a ∈ L) : a ≤ L.foldr max 0 := by
  induction L with
  | nil => simp at h
  | cons b L ih =>
    simp only [List.foldr_cons]
    rcases List.mem_cons.1 h with rfl | h
    · exact le_max_left _ _
    · exact (ih h).trans (le_max_right _ _)

/-- The approximating function of a gate of depth `t` has degree at most `(2 l) ^ t`. -/
private theorem approx_degree {n l : ℕ} (hl : 1 ≤ l) (r : Fin l → Finset ℕ)
    {C : List (ACGate n)} (hWF : WellFormedCircuit C) :
    ∀ j < C.length,
      (approxList r C).getD j 0 ∈ degLE n ((2 * l) ^ ((circuitDepths C).getD j 0)) := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
  intro hj
  set D := circuitDepths C with hDdef
  set P := approxList r C with hPdef
  have hin : ∀ a ∈ gateInputs C[j], a < j := hWF j hj
  have hD : D.getD j 0 = gateDepthOf D C[j] := by
    rw [hDdef, circuitDepths, getD_foldl_snoc _ _ _ hj, gateDepthOf_take _ _ hin]
  have hP : P.getD j 0 = approxGate r P C[j] := by
    rw [hPdef, approxList, getD_foldl_snoc _ _ _ hj, approxGate_take _ _ _ hin]
  have ihc : ∀ a ∈ gateInputs C[j], P.getD a 0 ∈ degLE n ((2 * l) ^ (D.getD a 0)) :=
    fun a ha => ih a (hin a ha) ((hin a ha).trans hj)
  have h2l : 1 ≤ 2 * l := by omega
  rw [hP, hD]
  generalize C[j] = g at hin ihc
  cases g with
  | var i => simpa [approxGate, gateDepthOf] using var_mem_degLE i
  | const b => exact const_mem_degLE _ _
  | notGate a =>
    simp only [approxGate, gateDepthOf]
    have h := ihc a (by simp [gateInputs])
    have heq : (fun x => 1 - P.getD a 0 x) = 1 - P.getD a 0 := rfl
    rw [heq]
    exact Submodule.sub_mem _ (one_mem_degLE _)
      (degLE_mono (Nat.pow_le_pow_right h2l (Nat.le_succ _)) h)
  | orGate L =>
    simp only [approxGate, gateDepthOf]
    have h := orApprox_mem_degLE r L.toFinset (fun a => P.getD a 0)
      ((2 * l) ^ List.foldr max 0 (L.map fun a => D.getD a 0)) fun a ha => by
        have ha' : a ∈ L := by simpa using ha
        exact degLE_mono (Nat.pow_le_pow_right h2l (le_foldr_max (List.mem_map_of_mem ha')))
          (ihc a (by simpa [gateInputs] using ha'))
    rw [pow_succ]
    convert h using 2
    ring
  | andGate L =>
    simp only [approxGate, gateDepthOf]
    have h := orApprox_mem_degLE r L.toFinset (fun a => 1 - P.getD a 0)
      ((2 * l) ^ List.foldr max 0 (L.map fun a => D.getD a 0)) fun a ha => by
        have ha' : a ∈ L := by simpa using ha
        exact Submodule.sub_mem _ (one_mem_degLE _)
          (degLE_mono (Nat.pow_le_pow_right h2l (le_foldr_max (List.mem_map_of_mem ha')))
          (ihc a (by simpa [gateInputs] using ha')))
    have heq : (fun x => 1 - orApprox r L.toFinset (fun a => 1 - P.getD a 0 x)) =
        1 - (fun x => orApprox r L.toFinset (fun a => (1 - P.getD a 0) x)) := rfl
    rw [heq, pow_succ]
    refine Submodule.sub_mem _ (one_mem_degLE _) ?_
    convert h using 2
    ring
  | modGate m L => exact Submodule.zero_mem _


/-! ### Averaging over the random sets -/

/-- The witness set of a gate of a well-formed circuit consists of earlier gates. -/
private theorem witness_subset {n : ℕ} {C : List (ACGate n)} (hWF : WellFormedCircuit C)
    (V : List Bool) {j : ℕ} (hj : j < C.length) :
    witness V C[j] ⊆ Finset.range C.length := by
  have hin := hWF j hj
  have key : ∀ a ∈ witness V C[j], a ∈ gateInputs C[j] := by
    generalize C[j] = g
    intro a ha
    cases g <;> simp_all [witness, gateInputs]
  intro a ha
  exact Finset.mem_range.2 ((hin a (key a ha)).trans hj)

/-- **Averaging.** For some family `r` of `l` sets of gates, the approximation of some gate fails
on at most a `C.length / 2 ^ l` fraction of the inputs. -/
private theorem exists_good_family {n : ℕ} (l : ℕ) {C : List (ACGate n)}
    (hWF : WellFormedCircuit C) :
    ∃ r : Fin l → Finset ℕ, ∃ B : Finset (Fin n → Bool), 2 ^ l * B.card ≤ 2 ^ n * C.length ∧
      ∀ x ∉ B, ∀ j (hj : j < C.length), ¬ Fails r (circuitEval C x) C[j] := by
  classical
  set Ω := Fintype.piFinset fun _ : Fin l => (Finset.range C.length).powerset with hΩdef
  let bad : (Fin l → Finset ℕ) → (Fin n → Bool) → Prop :=
    fun r x => ∃ j : Fin C.length, Fails r (circuitEval C x) (C[j.1]'j.2)
  have hΩ : Ω.card = (2 ^ C.length) ^ l := by
    simp [hΩdef, Fintype.card_piFinset, Finset.card_powerset]
  have hsum : ∑ r ∈ Ω, 2 ^ l * (Finset.univ.filter (bad r)).card ≤ ∑ _r ∈ Ω, 2 ^ n * C.length := by
    calc ∑ r ∈ Ω, 2 ^ l * (Finset.univ.filter (bad r)).card
        = 2 ^ l * ∑ x : Fin n → Bool, (Ω.filter fun r => bad r x).card := by
          rw [← Finset.mul_sum]
          congr 1
          simp only [Finset.card_filter]
          exact Finset.sum_comm
      _ ≤ 2 ^ l * ∑ x : Fin n → Bool, ∑ j : Fin C.length,
            (Ω.filter fun r => Fails r (circuitEval C x) (C[j.1]'j.2)).card := by
          gcongr with x
          calc (Ω.filter fun r => bad r x).card
              = (Finset.univ.biUnion fun j : Fin C.length =>
                  Ω.filter fun r => Fails r (circuitEval C x) (C[j.1]'j.2)).card := by
                congr 1
                ext r
                simp [bad, Finset.mem_biUnion]
            _ ≤ _ := Finset.card_biUnion_le
      _ = ∑ x : Fin n → Bool, ∑ j : Fin C.length,
            2 ^ l * (Ω.filter fun r => Fails r (circuitEval C x) (C[j.1]'j.2)).card := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun x _ => ?_
          rw [Finset.mul_sum]
      _ ≤ ∑ _x : Fin n → Bool, ∑ _j : Fin C.length, (2 ^ C.length) ^ l := by
          gcongr with x _ j
          have := card_fail_le l (Finset.range C.length) (witness (circuitEval C x) (C[j.1]'j.2))
            (witness_subset hWF _ j.2)
          simpa [hΩdef, Fails] using this
      _ = ∑ _r ∈ Ω, 2 ^ n * C.length := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, Fintype.card_fun,
            Fintype.card_bool, hΩ, smul_eq_mul]
          ring
  have hne : Ω.Nonempty := ⟨fun _ => ∅, by simp [hΩdef]⟩
  obtain ⟨r, -, hr⟩ := Finset.exists_le_of_sum_le hne hsum
  refine ⟨r, Finset.univ.filter (bad r), hr, fun x hx j hj hf => hx ?_⟩
  exact Finset.mem_filter.2 ⟨Finset.mem_univ _, ⟨j, hj⟩, hf⟩

/-! ### Parity and the character `χ_univ` -/

private theorem prod_map_sgn (L : List Bool) :
    (L.map sgn).prod = 1 + b2z (decide ((L.filter fun b => b).length % 2 = 1)) := by
  induction L with
  | nil => decide
  | cons b L ih =>
    cases b with
    | false => simpa [sgn] using ih
    | true =>
      have hf : ((true :: L).filter fun b => b) = true :: L.filter fun b => b := by
        simp
      rw [List.map_cons, List.prod_cons, ih, hf, List.length_cons]
      rcases Nat.mod_two_eq_zero_or_one (L.filter fun b => b).length with h | h
      · have h' : ((L.filter fun b => b).length + 1) % 2 = 1 := by omega
        rw [h, h']
        decide
      · have h' : ((L.filter fun b => b).length + 1) % 2 = 0 := by omega
        rw [h, h']
        decide

private theorem chi_univ_eq {n : ℕ} (x : Fin n → Bool) :
    chi Finset.univ x = 1 + b2z (parityDec (List.ofFn x)) := by
  rw [chi, ← List.prod_ofFn, parityDec, ← prod_map_sgn, List.map_ofFn]
  rfl

private theorem length_circuitEval {n : ℕ} (C : List (ACGate n)) (x : Fin n → Bool) :
    (circuitEval C x).length = C.length := by
  simp [circuitEval, length_foldl_snoc]

/-! ### The lower bound for one input length -/

/-- **Razborov–Smolensky at one input length.** A well-formed circuit without mod gates, with
`s ≥ 1` gates and depth at most `d` on `2 m` inputs, does not compute parity (at its last gate)
when `4 s ≤ 2 ^ l` and `16 ((2 l) ^ d + 1) ^ 2 < 2 m + 1`. -/
private theorem not_computes_parity {m d l : ℕ} (hl : 1 ≤ l) {C : List (ACGate (2 * m))}
    (hWF : WellFormedCircuit C) (hMF : IsModFree C) (hdepth : circuitDepth C ≤ d)
    (hs : 1 ≤ C.length) (hsl : 4 * C.length ≤ 2 ^ l)
    (hm : 16 * ((2 * l) ^ d + 1) ^ 2 < 2 * m + 1) :
    ¬ ∀ x : Fin (2 * m) → Bool,
      (circuitEval C x).getD (C.length - 1) false = parityDec (List.ofFn x) := by
  intro hpar
  classical
  obtain ⟨r, B, hB, hgood⟩ := exists_good_family l hWF
  set F : (Fin (2 * m) → Bool) → ZMod 3 := 1 + (approxList r C).getD (C.length - 1) 0 with hF
  have hFdeg : F ∈ degLE (2 * m) ((2 * l) ^ d) := by
    refine Submodule.add_mem _ (one_mem_degLE _) ?_
    have h := approx_degree hl r hWF (C.length - 1) (by omega)
    refine degLE_mono (Nat.pow_le_pow_right (by omega) ?_) h
    have hlen : (circuitDepths C).length = C.length := by
      simp [circuitDepths, length_foldl_snoc]
    have hmem : (circuitDepths C).getD (C.length - 1) 0 ∈ circuitDepths C := by
      rw [List.getD_eq_getElem _ _ (by omega)]
      exact List.getElem_mem _
    exact (le_foldr_max hmem).trans hdepth
  have hagree : ∀ x ∉ B, F x = chi Finset.univ x := by
    intro x hx
    have h := approx_correct r hWF hMF x (hgood x hx) (C.length - 1) (by omega)
    rw [hF, Pi.add_apply, Pi.one_apply, h, hpar x, chi_univ_eq]
  have hG : (Finset.univ \ B).card ≤
      (Finset.univ.filter fun x => F x = chi Finset.univ x).card := by
    apply Finset.card_le_card
    intro x hx
    simp only [Finset.mem_sdiff, Finset.mem_univ, true_and] at hx
    simp [hagree x hx]
  have hsm := card_agree_le F hFdeg
  have hn2 : 2 * m / 2 = m := by omega
  rw [hn2] at hsm
  have hbin := four_mul_card_small_lt m ((2 * l) ^ d) hm
  have hpow : 2 ^ (2 * m) = 4 ^ m := by rw [pow_mul]; norm_num
  have hcardB : (Finset.univ \ B).card = 4 ^ m - B.card := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ, Fintype.card_fun,
      Fintype.card_bool, Fintype.card_fin, hpow]
  have h4B : 4 * B.card ≤ 4 ^ m := by
    have h1 : 4 * C.length * B.card ≤ 4 ^ m * C.length := by
      rw [← hpow]
      exact (Nat.mul_le_mul_right _ hsl).trans hB
    have h2 : C.length * (4 * B.card) ≤ C.length * 4 ^ m := by
      calc C.length * (4 * B.card) = 4 * C.length * B.card := by ring
        _ ≤ 4 ^ m * C.length := h1
        _ = C.length * 4 ^ m := by ring
    exact Nat.le_of_mul_le_mul_left h2 (by omega)
  omega

/-! ### Choosing the parameters -/

private theorem eval_le_eval_one_mul_pow (p : Polynomial ℕ) {N : ℕ} (hN : 1 ≤ N) :
    p.eval N ≤ p.eval 1 * N ^ p.natDegree := by
  rw [Polynomial.eval_eq_sum_range, Polynomial.eval_eq_sum_range, Finset.sum_mul]
  refine Finset.sum_le_sum fun i hi => ?_
  simp only [one_pow, mul_one]
  exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hN (by simpa [Nat.lt_succ_iff] using hi))

private theorem exists_mul_pow_lt_two_pow (K k : ℕ) : ∃ t : ℕ, 1 ≤ t ∧ K * t ^ k < 2 ^ t := by
  have h := tendsto_pow_const_div_const_pow_of_one_lt k (one_lt_two : (1 : ℝ) < 2)
  have hK : (0 : ℝ) < 1 / ((K : ℝ) + 1) := by positivity
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 (h.eventually (gt_mem_nhds hK))
  refine ⟨N + 1, by omega, ?_⟩
  have h1 := hN (N + 1) (by omega)
  have h2 : (0 : ℝ) < 2 ^ (N + 1) := by positivity
  rw [div_lt_iff₀ h2] at h1
  have h3 : ((K * (N + 1) ^ k : ℕ) : ℝ) < ((2 ^ (N + 1) : ℕ) : ℝ) := by
    push_cast at h1 ⊢
    have hpos : (0 : ℝ) ≤ ((N : ℝ) + 1) ^ k := by positivity
    calc (K : ℝ) * ((N : ℝ) + 1) ^ k ≤ ((K : ℝ) + 1) * ((N : ℝ) + 1) ^ k := by
          gcongr; linarith
      _ < ((K : ℝ) + 1) * (1 / ((K : ℝ) + 1) * 2 ^ (N + 1)) := by
          gcongr
      _ = 2 ^ (N + 1) := by field_simp
  exact_mod_cast h3

/-- **Parity is not in AC0.** The parity language, which accepts a bitstring exactly when an odd
number of its entries are true, is not in the class $\mathsf{AC}^0$.

Source: M. Furst, J. Saxe, and M. Sipser, "Parity, circuits, and the polynomial-time hierarchy",
Mathematical Systems Theory 17 (1984), 13-27; M. Ajtai, "Σ₁¹-formulae on finite structures",
Annals of Pure and Applied Logic 24 (1983), 1-48; J. Håstad, "Almost optimal lower bounds for
small depth circuits", Proceedings of the Eighteenth Annual ACM Symposium on Theory of
Computing (STOC 1986), 6-20. -/
public theorem parity_not_in_ac0 :
    parityDec ∉ AC0 := by
  rintro ⟨d, p, C, hC⟩
  set c := p.eval 1 with hc
  set e := p.natDegree with he
  set K₀ := 2 * (e + c + 2) with hK₀
  obtain ⟨t, ht1, ht⟩ := exists_mul_pow_lt_two_pow (16 * (K₀ ^ d + 1) ^ 2) (2 * d)
  set m := 2 ^ (t - 1) with hmdef
  have hn : 2 * m = 2 ^ t := by
    rw [hmdef, ← pow_succ']
    congr 1
    omega
  obtain ⟨hWF, hMF, hlen, hdepth, hcorr⟩ := hC (2 * m)
  set l := t * e + c + 2 with hldef
  have hl : 1 ≤ l := by omega
  have hs : 1 ≤ (C (2 * m)).length := by
    by_contra h0
    have hnil : C (2 * m) = [] := List.eq_nil_of_length_eq_zero (by omega)
    have hm1 : 1 ≤ 2 * m := by rw [hn]; exact Nat.one_le_two_pow
    have hx := (hcorr (true :: List.replicate (2 * m - 1) false) (by simp; omega)).1
      (by simp [parityDec])
    rw [hnil] at hx
    simp [circuitEval] at hx
  have hsl : 4 * (C (2 * m)).length ≤ 2 ^ l := by
    have h1 : (C (2 * m)).length ≤ c * (2 * m) ^ e :=
      hlen.trans (eval_le_eval_one_mul_pow p (by rw [hn]; exact Nat.one_le_two_pow))
    have h2 : c ≤ 2 ^ c := (Nat.lt_two_pow_self).le
    calc 4 * (C (2 * m)).length ≤ 4 * (c * (2 * m) ^ e) := Nat.mul_le_mul_left _ h1
      _ ≤ 4 * (2 ^ c * (2 ^ t) ^ e) := by rw [hn]; gcongr
      _ = 2 ^ l := by rw [hldef, ← pow_mul, pow_add, pow_add]; ring
  have hm : 16 * ((2 * l) ^ d + 1) ^ 2 < 2 * m + 1 := by
    have h2l : 2 * l ≤ K₀ * t := by rw [hldef, hK₀]; nlinarith
    have hpow : (2 * l) ^ d + 1 ≤ (K₀ ^ d + 1) * t ^ d := by
      have hone := Nat.one_le_pow d t ht1
      calc (2 * l) ^ d + 1 ≤ (K₀ * t) ^ d + 1 := by gcongr
        _ = K₀ ^ d * t ^ d + 1 := by rw [mul_pow]
        _ ≤ K₀ ^ d * t ^ d + t ^ d := by omega
        _ = (K₀ ^ d + 1) * t ^ d := by ring
    calc 16 * ((2 * l) ^ d + 1) ^ 2 ≤ 16 * ((K₀ ^ d + 1) * t ^ d) ^ 2 := by gcongr
      _ = 16 * (K₀ ^ d + 1) ^ 2 * t ^ (2 * d) := by ring
      _ < 2 ^ t := ht
      _ = 2 * m := hn.symm
      _ < 2 * m + 1 := by omega
  refine not_computes_parity hl hWF hMF hdepth hs hsl hm fun x => ?_
  have hx := hcorr (List.ofFn x) (by simp)
  have hassign : (fun i : Fin (2 * m) => (List.ofFn x).getD i false) = x := by
    funext i
    simp
  rw [hassign] at hx
  have hlast : (circuitEval (C (2 * m)) x).getLast? =
      some ((circuitEval (C (2 * m)) x).getD ((C (2 * m)).length - 1) false) := by
    rw [List.getLast?_eq_getElem?, length_circuitEval,
      List.getD_eq_getElem _ _ (by rw [length_circuitEval]; omega)]
    simp [List.getElem?_eq_getElem (by rw [length_circuitEval]; omega : (C (2 * m)).length - 1 <
      (circuitEval (C (2 * m)) x).length)]
  rw [hlast, Option.some.injEq] at hx
  exact (Bool.eq_iff_iff.2 hx).symm

end MetaMathlibExt.Complexity.KeyTheorems.ParityNotInAC0
