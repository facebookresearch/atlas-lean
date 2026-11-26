/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.CountingAppearancesProgressions
import MathlibExt.NumberTheory.CountingAppearancesProgressionsFreeCount
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Data.Fin.SuccPred
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Nat.GCD.BigOperators
import Mathlib.Data.Nat.ModEq
import Mathlib.Tactic.Ring

/-!
# Available integers for distinct primes

For pairwise distinct primes `p : Fin k → ℕ` with `2 ≤ k` and any residues `r`, the number
of available integers in `[1, ∏ i, p i]` equals the ones-diagonal determinant. The count
satisfies the Chinese remainder recurrence in the last prime, the free count is the product
of the decremented primes, and the determinant satisfies the same recurrence; induction from
the two-prime case gives the equality.

## Main statements

* `availableCount_distinct_primes`: for distinct primes, the available count equals
  `onesDiagDet`.

The statement comes from Florian Pausinger, *Counting Appearances of Integers in Sets of
Arithmetic Progressions*, INTEGERS 26 (2026), Article A50 (preprint arXiv:2512.16358).
-/

set_option autoImplicit false

@[expose] public section

namespace MathlibExt.NumberTheory.CountingAppearancesProgressionsWanted

private def intervalRep (m n : ℕ) : ℕ :=
  if n % m = 0 then m else n % m

private theorem intervalRep_mem (m n : ℕ) (hm : 0 < m) :
    intervalRep m n ∈ Finset.Icc 1 m := by
  rw [intervalRep, Finset.mem_Icc]
  split_ifs with h
  · exact ⟨hm, le_rfl⟩
  · exact ⟨Nat.pos_of_ne_zero h, (Nat.mod_lt n hm).le⟩

private theorem intervalRep_modEq (m n : ℕ) : intervalRep m n ≡ n [MOD m] := by
  rw [intervalRep]
  split_ifs with h
  · exact (Nat.modEq_zero_iff_dvd.mpr dvd_rfl).trans (h ▸ Nat.mod_modEq n m)
  · exact Nat.mod_modEq n m

private theorem eq_of_modEq_of_mem_Icc {m a b : ℕ} (ha : a ∈ Finset.Icc 1 m)
    (hb : b ∈ Finset.Icc 1 m) (h : a ≡ b [MOD m]) : a = b := by
  obtain ⟨ha₁, ha₂⟩ := Finset.mem_Icc.mp ha
  obtain ⟨hb₁, hb₂⟩ := Finset.mem_Icc.mp hb
  apply h.eq_of_abs_lt
  rw [abs_lt]
  constructor <;> omega

private theorem card_filter_crt {m q : ℕ} (hm : 0 < m) (hq : 0 < q) (hcop : m.Coprime q)
    (ok : ℕ → ℕ → Prop) [DecidableRel ok] :
    ((Finset.Icc 1 (m * q)).filter (fun n => ok (intervalRep m n) (n % q))).card =
      ((Finset.Icc 1 m ×ˢ Finset.range q).filter (fun ab => ok ab.1 ab.2)).card := by
  refine Finset.card_nbij (fun n => (intervalRep m n, n % q)) ?_ ?_ ?_
  · intro n hn
    exact Finset.mem_filter.mpr ⟨Finset.mk_mem_product (intervalRep_mem m n hm)
      (Finset.mem_range.mpr (Nat.mod_lt n hq)), (Finset.mem_filter.mp hn).2⟩
  · intro a ha b hb hab
    have hrep : intervalRep m a = intervalRep m b := congrArg Prod.fst hab
    have h₁ : a ≡ b [MOD m] := by
      apply (intervalRep_modEq m a).symm.trans
      rw [hrep]
      exact intervalRep_modEq m b
    have h₂ : a ≡ b [MOD q] := congrArg Prod.snd hab
    exact eq_of_modEq_of_mem_Icc (Finset.mem_filter.mp ha).1 (Finset.mem_filter.mp hb).1
      ((Nat.modEq_and_modEq_iff_modEq_mul hcop).mp ⟨h₁, h₂⟩)
  · rintro ⟨a, b⟩ hab
    obtain ⟨ha, hb⟩ := Finset.mem_product.mp (Finset.mem_filter.mp hab).1
    let c := Nat.chineseRemainder hcop a b
    let n := intervalRep (m * q) c
    have hn := intervalRep_modEq (m * q) c
    have hna : intervalRep m n = a := eq_of_modEq_of_mem_Icc (intervalRep_mem m n hm) ha
      ((intervalRep_modEq m n).trans ((hn.of_mul_right q).trans c.prop.1))
    have hnb : n % q = b := calc
      n % q = b % q := (hn.of_mul_left m).trans c.prop.2
      _ = b := Nat.mod_eq_of_lt (Finset.mem_range.mp hb)
    refine ⟨n, Finset.mem_filter.mpr ⟨intervalRep_mem (m * q) c (Nat.mul_pos hm hq), ?_⟩,
      Prod.ext hna hnb⟩
    simpa only [hna, hnb] using (Finset.mem_filter.mp hab).2

private theorem residueHitCount_modEq {k : ℕ} (p r : Fin k → ℕ) {a b : ℕ}
    (hab : a ≡ b [MOD ∏ i, p i]) : residueHitCount p r a = residueHitCount p r b := by
  unfold residueHitCount
  congr 1
  exact Finset.filter_congr (fun i _ => by
    have hi : a % p i = b % p i := hab.of_dvd (Finset.dvd_prod_of_mem p (Finset.mem_univ i))
    rw [hi])

private theorem card_available_pairs (m q b : ℕ) (hb : b < q) (hits : ℕ → ℕ) :
    ((Finset.Icc 1 m ×ˢ Finset.range q).filter
      (fun ab => hits ab.1 + (if ab.2 = b then 1 else 0) ≤ 1)).card =
    (q - 1) * ((Finset.Icc 1 m).filter (fun a => hits a ≤ 1)).card +
      ((Finset.Icc 1 m).filter (fun a => hits a = 0)).card := by
  let available := (Finset.Icc 1 m).filter (fun a => hits a ≤ 1)
  let free := (Finset.Icc 1 m).filter (fun a => hits a = 0)
  let other := (Finset.range q).erase b
  have hsplit : ((Finset.Icc 1 m ×ˢ Finset.range q).filter
      (fun ab => hits ab.1 + (if ab.2 = b then 1 else 0) ≤ 1)) =
      (available ×ˢ other) ∪ (free ×ˢ {b}) := by
    ext ⟨x, y⟩
    by_cases hy : y = b
    · subst y
      simp [available, free, other, Finset.mem_range.mpr hb]
    · simp [available, free, other, hy, Ne.symm hy, and_left_comm, and_comm]
  have hd : Disjoint (available ×ˢ other) (free ×ˢ {b}) := by
    rw [Finset.disjoint_left]
    intro ab ha hb'
    have hne := (Finset.mem_erase.mp (Finset.mem_product.mp ha).2).1
    exact hne (Finset.mem_singleton.mp (Finset.mem_product.mp hb').2)
  rw [hsplit, Finset.card_union_of_disjoint hd, Finset.card_product, Finset.card_product,
    Finset.card_singleton, mul_one, mul_comm available.card]
  simp [available, free, other, Finset.card_erase_of_mem (Finset.mem_range.mpr hb)]

private theorem availableCount_succ {k : ℕ} (p : Fin (k + 1) → ℕ) (r : Fin (k + 1) → ℕ)
    (hP : 0 < ∏ i, p (Fin.castSucc i)) (hq : 0 < p (Fin.last k))
    (hcop : (∏ i, p (Fin.castSucc i)).Coprime (p (Fin.last k))) :
    availableCount p r =
      (p (Fin.last k) - 1) * availableCount (p ∘ Fin.castSucc) (r ∘ Fin.castSucc) +
        freeCount (p ∘ Fin.castSucc) (r ∘ Fin.castSucc) := by
  let P := ∏ i, p (Fin.castSucc i)
  let q := p (Fin.last k)
  let hits := residueHitCount (p ∘ Fin.castSucc) (r ∘ Fin.castSucc)
  have hprod : ∏ i, p i = P * q := Fin.prod_univ_castSucc _
  have hsplit (n : ℕ) : residueHitCount p r n =
      hits (intervalRep P n) + (if n % q = r (Fin.last k) % q then 1 else 0) := by
    have hrep : hits (intervalRep P n) = hits n :=
      residueHitCount_modEq _ _ (intervalRep_modEq P n)
    rw [hrep]
    dsimp only [hits, residueHitCount]
    rw [Finset.card_filter, Finset.card_filter, Fin.sum_univ_castSucc]
    rfl
  simpa only [availableCount, freeCount, hprod, hsplit, q, P, hits,
    Function.comp_apply] using
    (card_filter_crt hP hq hcop
      (fun a b => hits a + (if b = r (Fin.last k) % q then 1 else 0) ≤ 1)).trans
    (card_available_pairs P q (r (Fin.last k) % q) (Nat.mod_lt _ hq) hits)

private theorem card_free_pairs (m q b : ℕ) (hb : b < q) (hits : ℕ → ℕ) :
    ((Finset.Icc 1 m ×ˢ Finset.range q).filter
      (fun ab => hits ab.1 = 0 ∧ ab.2 ≠ b)).card =
    (q - 1) * ((Finset.Icc 1 m).filter (fun a => hits a = 0)).card := by
  have hsplit : ((Finset.Icc 1 m ×ˢ Finset.range q).filter
      (fun ab => hits ab.1 = 0 ∧ ab.2 ≠ b)) =
      ((Finset.Icc 1 m).filter (fun a => hits a = 0)) ×ˢ ((Finset.range q).erase b) := by
    ext ⟨x, y⟩
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_erase]
    constructor
    · rintro ⟨⟨hx, hy⟩, h0, hne⟩
      exact ⟨⟨hx, h0⟩, hne, hy⟩
    · rintro ⟨⟨hx, h0⟩, hne, hy⟩
      exact ⟨⟨hx, hy⟩, h0, hne⟩
  rw [hsplit, Finset.card_product, Finset.card_erase_of_mem (Finset.mem_range.mpr hb),
    Finset.card_range, mul_comm]

private theorem freeCount_succ {k : ℕ} (p : Fin (k + 1) → ℕ) (r : Fin (k + 1) → ℕ)
    (hP : 0 < ∏ i, p (Fin.castSucc i)) (hq : 0 < p (Fin.last k))
    (hcop : (∏ i, p (Fin.castSucc i)).Coprime (p (Fin.last k))) :
    freeCount p r =
      (p (Fin.last k) - 1) * freeCount (p ∘ Fin.castSucc) (r ∘ Fin.castSucc) := by
  let P := ∏ i, p (Fin.castSucc i)
  let q := p (Fin.last k)
  let hits := residueHitCount (p ∘ Fin.castSucc) (r ∘ Fin.castSucc)
  let b := r (Fin.last k) % q
  have hprod : ∏ i, p i = P * q := Fin.prod_univ_castSucc _
  have hsplit (n : ℕ) : residueHitCount p r n =
      hits (intervalRep P n) + (if n % q = b then 1 else 0) := by
    have hrep : hits (intervalRep P n) = hits n :=
      residueHitCount_modEq _ _ (intervalRep_modEq P n)
    rw [hrep]
    dsimp only [hits, residueHitCount]
    rw [Finset.card_filter, Finset.card_filter, Fin.sum_univ_castSucc]
    rfl
  have hiff (n : ℕ) : residueHitCount p r n = 0 ↔ hits (intervalRep P n) = 0 ∧ n % q ≠ b := by
    rw [hsplit n]
    by_cases h : n % q = b <;> simp [h]
  simpa only [freeCount, hprod, hiff, q, P, hits, b, Function.comp_apply] using
    (card_filter_crt hP hq hcop (fun a b' => hits a = 0 ∧ b' ≠ b)).trans
    (card_free_pairs P q b (Nat.mod_lt _ hq) hits)

private theorem freeCount_eq_prod (k : ℕ) (p : Fin k → ℕ) (r : Fin k → ℕ)
    (hprime : ∀ i, (p i).Prime) (hinj : Function.Injective p) :
    freeCount p r = ∏ i, (p i - 1) := by
  induction k with
  | zero =>
    simp [freeCount, residueHitCount]
  | succ k ih =>
    have hprime' : ∀ i, ((p ∘ Fin.castSucc) i).Prime := fun i => hprime _
    have hinj' : Function.Injective (p ∘ Fin.castSucc) :=
      hinj.comp (Fin.castSucc_injective _)
    have hP : 0 < ∏ i, p (Fin.castSucc i) :=
      Finset.prod_pos (fun i _ => (hprime _).pos)
    have hq : 0 < p (Fin.last k) := (hprime _).pos
    have hcop : (∏ i, p (Fin.castSucc i)).Coprime (p (Fin.last k)) := by
      refine Nat.Coprime.prod_left (fun i _ => ?_)
      have hne : p (Fin.castSucc i) ≠ p (Fin.last k) :=
        fun h => Fin.castSucc_ne_last i (hinj h)
      exact (Nat.coprime_primes (hprime _) (hprime _)).2 hne
    rw [freeCount_succ p r hP hq hcop, ih _ _ hprime' hinj']
    have hprod := Fin.prod_univ_castSucc (fun i => p i - 1)
    simpa [Function.comp_apply, mul_comm] using hprod.symm

private theorem neg_one_pow_add_self (k : ℕ) : (-1 : ℤ) ^ (k + k) = 1 := by
  rw [← two_mul, pow_mul]
  simp

private theorem lastCol_eq {k : ℕ} (p : Fin (k + 1) → ℕ) :
    (fun i => (if i = Fin.last k then (p i : ℤ) else 1)) =
      ((p (Fin.last k) : ℤ) - 1) • Pi.single (Fin.last k) (1 : ℤ) + fun _ => 1 := by
  ext i
  by_cases hi : i = Fin.last k <;> simp [hi]

private theorem det_updateCol_single {k : ℕ} (p : Fin (k + 1) → ℕ) :
    (Matrix.updateCol (fun i j => if i = j then (p i : ℤ) else 1)
      (Fin.last k) (Pi.single (Fin.last k) 1)).det =
    onesDiagDet (p ∘ Fin.castSucc) := by
  set M : Matrix (Fin (k + 1)) (Fin (k + 1)) ℤ :=
    fun i j => if i = j then (p i : ℤ) else 1 with hMdef
  have hsub : Matrix.submatrix (M.updateCol (Fin.last k) (Pi.single (Fin.last k) 1))
      (Fin.last k).succAbove (Fin.last k).succAbove =
      (fun i j => if i = j then (((p ∘ Fin.castSucc) i : ℕ) : ℤ) else 1) := by
    funext i j
    simp only [Matrix.submatrix_apply, Fin.succAbove_last]
    have hj : Fin.castSucc j ≠ Fin.last k := Fin.castSucc_ne_last j
    rw [Matrix.updateCol_ne hj]
    simp only [hMdef, Fin.castSucc_inj, Function.comp_apply]
  have hsign :
      (-1 : ℤ) ^ ((Fin.last k : Fin (k + 1)).val + (Fin.last k : Fin (k + 1)).val) = 1 := by
    simp only [Fin.val_last]
    exact neg_one_pow_add_self k
  have hlast : M.updateCol (Fin.last k) (Pi.single (Fin.last k) 1)
      (Fin.last k) (Fin.last k) = 1 := by
    simp
  change (M.updateCol (Fin.last k) (Pi.single (Fin.last k) 1)).det = _
  rw [Matrix.det_succ_column _ (Fin.last k)]
  rw [Finset.sum_eq_single (Fin.last k)]
  · simp only [hsub, hsign, hlast, onesDiagDet, one_mul]
  · intro i _ hi
    have h0 : M.updateCol (Fin.last k) (Pi.single (Fin.last k) 1) i (Fin.last k) = 0 := by
      simp [Pi.single_eq_of_ne hi]
    simp only [h0, mul_zero, zero_mul]
  · simp

private def stepMatrix {k : ℕ} (p : Fin (k + 1) → ℕ) (t : ℕ) :
    Matrix (Fin (k + 1)) (Fin (k + 1)) ℤ :=
  fun i j => if j = Fin.last k then 1
    else if j.val < t then (if i = j then ((p j : ℤ) - 1) else 0)
    else (if i = j then (p i : ℤ) else 1)

private theorem stepMatrix_zero {k : ℕ} (p : Fin (k + 1) → ℕ) :
    stepMatrix p 0 = Matrix.updateCol (fun i j => if i = j then (p i : ℤ) else 1)
      (Fin.last k) (fun _ => 1) := by
  set M : Matrix (Fin (k + 1)) (Fin (k + 1)) ℤ :=
    fun i j => if i = j then (p i : ℤ) else 1 with hMdef
  change stepMatrix p 0 = M.updateCol (Fin.last k) (fun _ => 1)
  ext i j
  simp only [stepMatrix, Matrix.updateCol_apply]
  by_cases hj : j = Fin.last k
  · simp [hj]
  · simp [hj, hMdef]

private theorem stepMatrix_det_succ {k : ℕ} (p : Fin (k + 1) → ℕ) (t : ℕ) (ht : t < k) :
    (stepMatrix p (t + 1)).det = (stepMatrix p t).det := by
  let jt : Fin (k + 1) := ⟨t, by omega⟩
  have hjt_val : jt.val = t := rfl
  have hjt_ne : jt ≠ Fin.last k := by
    intro h
    have hval := congrArg Fin.val h
    simp [hjt_val, Fin.val_last] at hval
    omega
  have hstep : stepMatrix p (t + 1) = Matrix.updateCol (stepMatrix p t) jt
      (fun i => stepMatrix p t i jt + (-1 : ℤ) • stepMatrix p t i (Fin.last k)) := by
    ext i j
    by_cases hj : j = jt
    · subst j
      simp only [Matrix.updateCol_self]
      simp only [stepMatrix, hjt_ne, hjt_val, Nat.lt_irrefl, Nat.lt_succ_self, ite_true, ite_false]
      by_cases hi : i = jt
      · simp [hi]
        ring
      · simp [hi]
    · simp only [Matrix.updateCol_ne hj]
      by_cases hjlast : j = Fin.last k
      · simp [hjlast, stepMatrix]
      · have hcond : (j.val < t + 1) ↔ (j.val < t) := by
          constructor
          · intro hlt
            by_contra hnge
            have heq : j.val = t := by omega
            have hj_eq : j = jt := Fin.ext_iff.mpr (by simpa [hjt_val] using heq)
            exact hj hj_eq
          · intro hlt
            omega
        simp [stepMatrix, hjlast, hcond]
  rw [hstep]
  exact Matrix.det_updateCol_add_smul_self _ hjt_ne _

private theorem val_lt_of_ne_last {k : ℕ} (j : Fin (k + 1)) (hj : j ≠ Fin.last k) :
    j.val < k := by
  have hne_val : j.val ≠ k := by
    intro heq
    apply hj
    rw [Fin.ext_iff]
    simpa [Fin.val_last] using heq
  have hlt : j.val < k + 1 := j.isLt
  omega

private theorem det_stepMatrix_last {k : ℕ} (p : Fin (k + 1) → ℕ) :
    (stepMatrix p k).det = ∏ i, (((p ∘ Fin.castSucc) i : ℤ) - 1) := by
  have hsub : Matrix.submatrix (stepMatrix p k)
      (Fin.last k).succAbove (Fin.last k).succAbove =
      Matrix.diagonal (fun i => (((p ∘ Fin.castSucc) i : ℤ) - 1)) := by
    funext i j
    simp only [Matrix.submatrix_apply, Fin.succAbove_last, Matrix.diagonal_apply]
    have hj : Fin.castSucc j ≠ Fin.last k := Fin.castSucc_ne_last j
    have hlt : (Fin.castSucc j).val < k := j.isLt
    simp only [stepMatrix, hj, hlt, ite_true, ite_false]
    by_cases hij : Fin.castSucc i = Fin.castSucc j
    · have hij' : i = j := Fin.castSucc_inj.mp hij
      simp [hij', Function.comp_apply]
    · have hij' : i ≠ j := fun h => hij (congrArg Fin.castSucc h)
      simp [hij, hij']
  have hsign :
      (-1 : ℤ) ^ ((Fin.last k : Fin (k + 1)).val + (Fin.last k : Fin (k + 1)).val) = 1 := by
    simp only [Fin.val_last]
    exact neg_one_pow_add_self k
  have hlast : stepMatrix p k (Fin.last k) (Fin.last k) = 1 := by
    simp [stepMatrix]
  rw [Matrix.det_succ_row _ (Fin.last k)]
  rw [Finset.sum_eq_single (Fin.last k)]
  · simp only [hsub, hsign, hlast, Matrix.det_diagonal, one_mul]
  · intro j _ hj
    have h0 : stepMatrix p k (Fin.last k) j = 0 := by
      have hlt : j.val < k := val_lt_of_ne_last j hj
      simp [stepMatrix, hj, hlt, Ne.symm hj]
    simp only [h0, mul_zero, zero_mul]
  · simp

private theorem det_updateCol_one {k : ℕ} (p : Fin (k + 1) → ℕ) :
    (Matrix.updateCol (fun i j => if i = j then (p i : ℤ) else 1)
      (Fin.last k) (fun _ => 1)).det =
    ∏ i, (((p ∘ Fin.castSucc) i : ℤ) - 1) := by
  have hall : ∀ t, t ≤ k → (stepMatrix p t).det = (stepMatrix p 0).det := by
    intro t
    induction t with
    | zero => intro _; rfl
    | succ t ih =>
      intro ht
      have htk : t < k := by omega
      have ht' : t ≤ k := by omega
      rw [stepMatrix_det_succ p t htk, ih ht']
  have h0 : stepMatrix p 0 = Matrix.updateCol (fun i j => if i = j then (p i : ℤ) else 1)
      (Fin.last k) (fun _ => 1) := stepMatrix_zero p
  have hfinal : (stepMatrix p k).det = ∏ i, (((p ∘ Fin.castSucc) i : ℤ) - 1) :=
    det_stepMatrix_last p
  rw [← h0, ← hall k le_rfl, hfinal]

private theorem onesDiagDet_succ {k : ℕ} (p : Fin (k + 1) → ℕ) :
    onesDiagDet p = ((p (Fin.last k) : ℤ) - 1) * onesDiagDet (p ∘ Fin.castSucc) +
      ∏ i, (((p ∘ Fin.castSucc) i : ℤ) - 1) := by
  set M : Matrix (Fin (k + 1)) (Fin (k + 1)) ℤ :=
    fun i j => if i = j then (p i : ℤ) else 1 with hMdef
  have hcol : (fun i => M i (Fin.last k)) =
      ((p (Fin.last k) : ℤ) - 1) • Pi.single (Fin.last k) (1 : ℤ) + fun _ => 1 :=
    lastCol_eq p
  have hM : M = M.updateCol (Fin.last k)
      (((p (Fin.last k) : ℤ) - 1) • Pi.single (Fin.last k) (1 : ℤ) + fun _ => 1) := by
    rw [← hcol, Matrix.updateCol_eq_self]
  have hdet : M.det = ((p (Fin.last k) : ℤ) - 1) *
      (M.updateCol (Fin.last k) (Pi.single (Fin.last k) 1)).det +
      (M.updateCol (Fin.last k) (fun _ => 1)).det := by
    conv_lhs => rw [hM]
    rw [Matrix.det_updateCol_add, Matrix.det_updateCol_smul]
  have hL1 : (M.updateCol (Fin.last k) (Pi.single (Fin.last k) 1)).det =
      onesDiagDet (p ∘ Fin.castSucc) := det_updateCol_single p
  have hL2 : (M.updateCol (Fin.last k) (fun _ => 1)).det =
      ∏ i, (((p ∘ Fin.castSucc) i : ℤ) - 1) := det_updateCol_one p
  have hones : M.det = onesDiagDet p := by
    simp [hMdef, onesDiagDet]
  rw [← hones, hdet, hL1, hL2]

private theorem base_two (p : Fin 2 → ℕ) (r : Fin 2 → ℕ)
    (hprime : ∀ i, (p i).Prime) (hinj : Function.Injective p) :
    (availableCount p r : ℤ) = onesDiagDet p := by
  have hp_eq : p = ![p 0, p 1] := by
    funext i
    fin_cases i <;> simp
  have h01 : (0 : Fin 2) ≠ 1 := by decide
  have hpq : p 0 ≠ p 1 := fun h => h01 (hinj h)
  rw [hp_eq]
  exact availableCount_two_primes (p 0) (p 1) (hprime 0) (hprime 1) hpq r

/-- **Available integers for distinct primes.** Let $k \ge 2$, let $p_1, \dots, p_k$ be pairwise
distinct primes, and let $r_1, \dots, r_k$ be any natural numbers. Call an integer $n$ available if
$n \equiv r_i \pmod{p_i}$ holds for at most one index $i$. Then the number of available integers $n$
with $1 \le n \le p_1 p_2 \cdots p_k$ equals $A_k(p_1, \dots, p_k)$, the determinant of the
$k \times k$ matrix with diagonal entries $p_1, \dots, p_k$ and all other entries $1$.

Source: Florian Pausinger, "Counting Appearances of Integers in
Sets of Arithmetic Progressions", Theorem 2. -/
theorem availableCount_distinct_primes (k : ℕ) (hk : 2 ≤ k)
    (p : Fin k → ℕ) (hprime : ∀ i, (p i).Prime)
    (hinj : Function.Injective p) (r : Fin k → ℕ) :
    (availableCount p r : ℤ) = onesDiagDet p := by
  induction k, hk using Nat.le_induction with
  | base =>
    exact base_two p r hprime hinj
  | succ n hn ih =>
    have hprime' : ∀ i, ((p ∘ Fin.castSucc) i).Prime := fun i => hprime _
    have hinj' : Function.Injective (p ∘ Fin.castSucc) :=
      hinj.comp (Fin.castSucc_injective _)
    have hP : 0 < ∏ i, p (Fin.castSucc i) :=
      Finset.prod_pos (fun i _ => (hprime _).pos)
    have hq : 0 < p (Fin.last n) := (hprime _).pos
    have hcop : (∏ i, p (Fin.castSucc i)).Coprime (p (Fin.last n)) := by
      refine Nat.Coprime.prod_left (fun i _ => ?_)
      have hne : p (Fin.castSucc i) ≠ p (Fin.last n) :=
        fun h => Fin.castSucc_ne_last i (hinj h)
      exact (Nat.coprime_primes (hprime _) (hprime _)).2 hne
    have hav := availableCount_succ p r hP hq hcop
    have hfree := freeCount_eq_prod n (p ∘ Fin.castSucc) (r ∘ Fin.castSucc) hprime' hinj'
    have hdet := onesDiagDet_succ p
    have ih' : (availableCount (p ∘ Fin.castSucc) (r ∘ Fin.castSucc) : ℤ) =
        onesDiagDet (p ∘ Fin.castSucc) :=
      ih (p ∘ Fin.castSucc) hprime' hinj' (r ∘ Fin.castSucc)
    have hq1 : 1 ≤ p (Fin.last n) := (hprime _).one_lt.le
    have hfreeZ : (freeCount (p ∘ Fin.castSucc) (r ∘ Fin.castSucc) : ℤ) =
        ∏ i, (((p ∘ Fin.castSucc) i : ℤ) - 1) := by
      rw [hfree, Nat.cast_prod]
      apply Finset.prod_congr rfl
      intro i _
      rw [Nat.cast_sub ((hprime' i).one_lt.le)]
      simp
    have havZ := congrArg (fun n : ℕ => (n : ℤ)) hav
    push_cast at havZ
    rw [Nat.cast_sub hq1, Nat.cast_one] at havZ
    rw [ih', hfreeZ] at havZ
    rw [havZ, hdet]

end MathlibExt.NumberTheory.CountingAppearancesProgressionsWanted
