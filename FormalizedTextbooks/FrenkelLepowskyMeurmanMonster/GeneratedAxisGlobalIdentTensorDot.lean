/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentTensorPairTri

/-! # Packed dot products by one multiplication

The dot product `Σ_i x_i y_i` of two packed vectors with `4096` fields is the middle field of the
product of `x` with the field-reversed `y` (the reversal `i ↦ i XOR 4095` is a packed
translation), provided no field of the product overflows.  This replaces the field-by-field loop
of `sdot` (whose intermediate shifted numbers make kernel memory quadratic) by four big-number
multiplications per column. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
open Polynomial
set_option autoImplicit false

/-! ## Base-`2^w` expansions -/

/-- A number below `2^(w n)` is the sum of its first `n` fields. -/
theorem expand_fld (w : ℕ) : ∀ (n P : ℕ), P < 2 ^ (w * n) →
    P = ∑ i ∈ Finset.range n, fld w P i * 2 ^ (w * i)
  | 0, P, h => by simp at h; simp [h]
  | n + 1, P, h => by
    have hpos : 0 < 2 ^ w := by positivity
    have h' : P / 2 ^ w < 2 ^ (w * n) := by
      rw [Nat.div_lt_iff_lt_mul hpos, ← pow_add]
      calc P < 2 ^ (w * (n + 1)) := h
        _ = 2 ^ (w * n + w) := by ring_nf
    have ih := expand_fld w n (P / 2 ^ w) h'
    rw [Finset.sum_range_succ']
    simp only [fld_succ, mul_zero, pow_zero, mul_one, fld_zero_right]
    have e : ∑ i ∈ Finset.range n, fld w (P / 2 ^ w) i * 2 ^ (w * (i + 1)) =
        2 ^ w * ∑ i ∈ Finset.range n, fld w (P / 2 ^ w) i * 2 ^ (w * i) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [show w * (i + 1) = w * i + w by ring, pow_add]
      ring
    rw [e, ← ih]
    exact (Nat.div_add_mod P (2 ^ w)).symm

/-- Fields of a base-`2^w` number with small digits. -/
theorem fld_sum (w : ℕ) : ∀ (N : ℕ) (c : ℕ → ℕ), (∀ k, c k < 2 ^ w) → ∀ m,
    fld w (∑ k ∈ Finset.range N, c k * 2 ^ (w * k)) m = if m < N then c m else 0
  | 0, c, _, m => by simp [fld]
  | N + 1, c, hc, m => by
    have hpos : 0 < 2 ^ w := by positivity
    rw [Finset.sum_range_succ']
    simp only [mul_zero, pow_zero, mul_one]
    have e : ∑ k ∈ Finset.range N, c (k + 1) * 2 ^ (w * (k + 1)) =
        2 ^ w * ∑ k ∈ Finset.range N, c (k + 1) * 2 ^ (w * k) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      rw [show w * (k + 1) = w * k + w by ring, pow_add]
      ring
    rw [e]
    cases m with
    | zero =>
      rw [fld_zero_right, Nat.add_mod, Nat.mul_mod_right, zero_add, Nat.mod_mod,
        Nat.mod_eq_of_lt (hc 0)]
      simp
    | succ m =>
      rw [fld_succ, show (2 ^ w * ∑ k ∈ Finset.range N, c (k + 1) * 2 ^ (w * k) + c 0) / 2 ^ w =
        ∑ k ∈ Finset.range N, c (k + 1) * 2 ^ (w * k) by
          rw [Nat.add_comm, Nat.add_mul_div_left _ _ hpos, Nat.div_eq_of_lt (hc 0), zero_add],
        fld_sum w N (fun k => c (k + 1)) (fun k => hc (k + 1)) m]
      simp only [Nat.add_lt_add_iff_right]

/-! ## Products as convolutions -/

/-- The polynomial with the given first `n` coefficients. -/
def polyOf (n : ℕ) (a : ℕ → ℕ) : ℕ[X] := ∑ i ∈ Finset.range n, C (a i) * X ^ i

/-- Evaluation at `2^w`. -/
theorem eval_polyOf (w n : ℕ) (a : ℕ → ℕ) :
    (polyOf n a).eval (2 ^ w) = ∑ i ∈ Finset.range n, a i * 2 ^ (w * i) := by
  rw [polyOf, eval_finsetSum]
  apply Finset.sum_congr rfl
  intro i _
  rw [eval_mul, eval_C, eval_pow, eval_X, ← pow_mul]

/-- Coefficients. -/
theorem coeff_polyOf (n : ℕ) (a : ℕ → ℕ) (k : ℕ) :
    (polyOf n a).coeff k = if k < n then a k else 0 := by
  rw [polyOf, finsetSum_coeff]
  simp only [coeff_C_mul_X_pow]
  rw [Finset.sum_ite_eq]
  simp [Finset.mem_range]

/-- The degree is below `n`. -/
theorem natDegree_polyOf (n : ℕ) (a : ℕ → ℕ) : (polyOf n a).natDegree ≤ n - 1 := by
  rw [natDegree_le_iff_coeff_eq_zero]
  intro N hN
  rw [coeff_polyOf]
  split_ifs with h
  · omega
  · rfl

/-- Fields of the evaluation of a polynomial with small coefficients. -/
theorem fld_eval (w N : ℕ) (p : ℕ[X]) (hdeg : p.natDegree < N) (hc : ∀ k, p.coeff k < 2 ^ w)
    (m : ℕ) : fld w (p.eval (2 ^ w)) m = if m < N then p.coeff m else 0 := by
  rw [eval_eq_sum_range' hdeg]
  have e : ∀ i ∈ Finset.range N, p.coeff i * (2 ^ w) ^ i = p.coeff i * 2 ^ (w * i) := by
    intro i _
    rw [← pow_mul]
  rw [Finset.sum_congr rfl e, fld_sum w N _ hc m]

/-- A coefficient of a product of two polynomials with bounded coefficients. -/
theorem coeff_polyOf_mul_le (n : ℕ) (a r : ℕ → ℕ) (Ba Br : ℕ) (ha : ∀ i < n, a i ≤ Ba)
    (hr : ∀ i < n, r i ≤ Br) (k : ℕ) :
    (polyOf n a * polyOf n r).coeff k ≤ (k + 1) * (Ba * Br) := by
  rw [coeff_mul]
  refine le_trans (Finset.sum_le_sum (g := fun _ => Ba * Br) (fun x _ => ?_)) ?_
  · rw [coeff_polyOf, coeff_polyOf]
    split_ifs with h1 h2 h2
    · exact Nat.mul_le_mul (ha _ h1) (hr _ h2)
    all_goals simp
  · rw [Finset.sum_const, Finset.Nat.card_antidiagonal, smul_eq_mul]

/-- The middle coefficient of a product of two polynomials is a dot product with reversal. -/
theorem coeff_polyOf_mul_mid (n : ℕ) (hn : 0 < n) (a r : ℕ → ℕ) :
    (polyOf n a * polyOf n r).coeff (n - 1) = ∑ i ∈ Finset.range n, a i * r (n - 1 - i) := by
  rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j => (polyOf n a).coeff i *
      (polyOf n r).coeff j), Nat.succ_eq_add_one, Nat.sub_add_cancel hn]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mem_range] at hi
  rw [coeff_polyOf, coeff_polyOf, ite_eq_left hi, ite_eq_left (by omega)]

/-- The degree of a product of two polynomials of length `n`. -/
theorem natDegree_polyOf_mul (n : ℕ) (hn : 0 < n) (a r : ℕ → ℕ) :
    (polyOf n a * polyOf n r).natDegree < 2 * n := by
  have h1 := natDegree_mul_le (p := polyOf n a) (q := polyOf n r)
  have h2 := natDegree_polyOf n a
  have h3 := natDegree_polyOf n r
  omega

/-- A packed number is the evaluation of the polynomial of its fields. -/
theorem eval_polyOf_fld (w n P : ℕ) (hP : P < 2 ^ (w * n)) :
    (polyOf n (fld w P)).eval (2 ^ w) = P := by
  rw [eval_polyOf]
  exact (expand_fld w n P hP).symm

/-- The middle field of a sum of two products with reversed second factors. -/
theorem fld_mid_two (w n : ℕ) (hn : 0 < n) (P1 P2 R1 R2 Ba Br : ℕ)
    (hP1 : P1 < 2 ^ (w * n)) (hP2 : P2 < 2 ^ (w * n)) (hR1 : R1 < 2 ^ (w * n))
    (hR2 : R2 < 2 ^ (w * n)) (ha1 : ∀ i < n, fld w P1 i ≤ Ba) (ha2 : ∀ i < n, fld w P2 i ≤ Ba)
    (hr1 : ∀ i < n, fld w R1 i ≤ Br) (hr2 : ∀ i < n, fld w R2 i ≤ Br)
    (hB : 2 * (2 * n * (Ba * Br)) < 2 ^ w) :
    fld w (P1 * R1 + P2 * R2) (n - 1) =
      ∑ i ∈ Finset.range n, (fld w P1 i * fld w R1 (n - 1 - i) + fld w P2 i * fld w R2 (n - 1 - i)) := by
  set p := polyOf n (fld w P1) * polyOf n (fld w R1) + polyOf n (fld w P2) * polyOf n (fld w R2)
    with hp
  have he : P1 * R1 + P2 * R2 = p.eval (2 ^ w) := by
    rw [hp, eval_add, eval_mul, eval_mul, eval_polyOf_fld w n P1 hP1, eval_polyOf_fld w n R1 hR1,
      eval_polyOf_fld w n P2 hP2, eval_polyOf_fld w n R2 hR2]
  have hdeg : p.natDegree < 2 * n := by
    rw [hp]
    have := natDegree_add_le (polyOf n (fld w P1) * polyOf n (fld w R1))
      (polyOf n (fld w P2) * polyOf n (fld w R2))
    have h1 := natDegree_polyOf_mul n hn (fld w P1) (fld w R1)
    have h2 := natDegree_polyOf_mul n hn (fld w P2) (fld w R2)
    omega
  have hc : ∀ k, p.coeff k < 2 ^ w := by
    intro k
    rw [hp, coeff_add]
    by_cases hk : k < 2 * n
    · have h1 := coeff_polyOf_mul_le n (fld w P1) (fld w R1) Ba Br ha1 hr1 k
      have h2 := coeff_polyOf_mul_le n (fld w P2) (fld w R2) Ba Br ha2 hr2 k
      have h3 : (k + 1) * (Ba * Br) ≤ 2 * n * (Ba * Br) := Nat.mul_le_mul_right _ (by omega)
      omega
    · have z1 : (polyOf n (fld w P1) * polyOf n (fld w R1)).coeff k = 0 :=
        coeff_eq_zero_of_natDegree_lt (by have := natDegree_polyOf_mul n hn (fld w P1) (fld w R1); omega)
      have z2 : (polyOf n (fld w P2) * polyOf n (fld w R2)).coeff k = 0 :=
        coeff_eq_zero_of_natDegree_lt (by have := natDegree_polyOf_mul n hn (fld w P2) (fld w R2); omega)
      rw [z1, z2]
      positivity
  rw [he, fld_eval w (2 * n) p hdeg hc, ite_eq_left (by omega), hp, coeff_add,
    coeff_polyOf_mul_mid n hn, coeff_polyOf_mul_mid n hn, ← Finset.sum_add_distrib]

/-! ## The signed packed dot product -/

/-- The field reversal `i ↦ i XOR 4095`, as a translation by all twelve bits. -/
def revBits : List ℕ := [11, 10, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0]

/-- The twelve bits form the mask `4095`. -/
theorem xorBits_revBits : xorBits revBits = 4095 := by decide

/-- The reversal bits are below twelve. -/
theorem revBits_lt : ∀ k ∈ revBits, k < 12 := by decide

/-- The middle field of a product. -/
def midFld (w P : ℕ) : ℕ := (P >>> (w * 4095)) % 2 ^ w

/-- The middle field is a field. -/
theorem midFld_eq (w P : ℕ) : midFld w P = fld w P 4095 := by
  rw [midFld, fld, Nat.shiftRight_eq_div_pow]

/-- The signed packed dot product by multiplication with the reversed vector. -/
def sdotM (w : ℕ) (x y : SVec) : ℤ :=
  (midFld w (x.1 * (strs w 12 revBits y).1 + x.2 * (strs w 12 revBits y).2) : ℤ) -
    (midFld w (x.1 * (strs w 12 revBits y).2 + x.2 * (strs w 12 revBits y).1) : ℤ)

/-- Part-wise fields of a translation by a list of bits. -/
theorem fld_strs {W K : ℕ} : ∀ (ks : List ℕ) (x : SVec), (∀ k ∈ ks, k < K) → ∀ t < 2 ^ K,
    fld W (strs W K ks x).1 t = fld W x.1 (t ^^^ xorBits ks) ∧
      fld W (strs W K ks x).2 t = fld W x.2 (t ^^^ xorBits ks)
  | [], x, _, t, _ => by simp [strs, xorBits]
  | k :: ks, x, hks, t, ht => by
    have hk : k < K := hks k (by simp)
    have hx := xorBits_lt K ks (fun j hj => hks j (by simp [hj]))
    obtain ⟨h1, h2⟩ := fld_strs ks (str W K k x) (fun j hj => hks j (by simp [hj])) t ht
    have ht' : t ^^^ xorBits ks < 2 ^ K := Nat.xor_lt_two_pow ht hx
    simp only [strs]
    rw [h1, h2]
    simp only [str]
    rw [fld_tr W K k _ _ hk ht', fld_tr W K k _ _ hk ht', xorBits, Nat.xor_assoc,
      Nat.xor_comm (xorBits ks) (2 ^ k)]
    exact ⟨rfl, rfl⟩

set_option maxRecDepth 100000 in
/-- Reversal is an involution on the field indices (checked on all indices). -/
theorem rev_rev : ∀ i : Fin 4096, (4095 - i.val) ^^^ 4095 = i.val := by decide +kernel

/-- The multiplicative packed dot product is the dot product. -/
theorem sdotM_eq {w Bx By : ℕ} {x y : SVec} (hx : SBnd w (2 ^ 12) Bx x) (hy : SBnd w (2 ^ 12) By y)
    (hB : 2 * (2 * 4096 * (Bx * By)) < 2 ^ w) :
    sdotM w x y = ∑ i ∈ Finset.range 4096, sval w x i * sval w y i := by
  obtain ⟨hr, -⟩ := strs_spec revBits hy revBits_lt
  have hf := fld_strs (W := w) (K := 12) revBits y revBits_lt
  have hn : (0 : ℕ) < 4096 := by norm_num
  have e12 : (2 : ℕ) ^ 12 = 4096 := by norm_num
  rw [e12] at hx hy hr
  have m1 := fld_mid_two w 4096 hn x.1 x.2 (strs w 12 revBits y).1 (strs w 12 revBits y).2 Bx By
    hx.1 hx.2.1 hr.1 hr.2.1 (fun i hi => (hx.2.2 i hi).1) (fun i hi => (hx.2.2 i hi).2)
    (fun i hi => (hr.2.2 i hi).1) (fun i hi => (hr.2.2 i hi).2) hB
  have m2 := fld_mid_two w 4096 hn x.1 x.2 (strs w 12 revBits y).2 (strs w 12 revBits y).1 Bx By
    hx.1 hx.2.1 hr.2.1 hr.1 (fun i hi => (hx.2.2 i hi).1) (fun i hi => (hx.2.2 i hi).2)
    (fun i hi => (hr.2.2 i hi).2) (fun i hi => (hr.2.2 i hi).1) hB
  rw [sdotM, midFld_eq, midFld_eq, show (4095 : ℕ) = 4096 - 1 from rfl, m1, m2]
  push_cast
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mem_range] at hi
  have ht : 4096 - 1 - i < 2 ^ 12 := by norm_num; omega
  obtain ⟨f1, f2⟩ := hf (4096 - 1 - i) ht
  rw [f1, f2, xorBits_revBits, show 4096 - 1 - i = 4095 - (⟨i, hi⟩ : Fin 4096).val from rfl,
    rev_rev ⟨i, hi⟩]
  simp only [sval]
  ring

/-- The packed tensor pairing by multiplication. -/
def tdotM (w : ℕ) (X Y : List SVec) : ℤ :=
  ((List.range 24).map (fun i => sdotM w (tcol X i) (tcol Y i))).sum

/-- The multiplicative tensor pairing is the tensor pairing. -/
theorem tdotM_eq {w Bx By : ℕ} {X Y : List SVec} (hX : TBnd w Bx X) (hY : TBnd w By Y)
    (hB : 2 * (2 * 4096 * (Bx * By)) < 2 ^ w) : tdotM w X Y = tdot w X Y := by
  unfold tdotM tdot
  congr 1
  apply List.map_congr_left
  intro i hi
  rw [List.mem_range] at hi
  rw [sdotM_eq (hX i hi) (hY i hi) hB, sdot_eq]

/-! ## The criterion with the multiplicative pairing -/

/-- The fast exact pairing with the dense tensor sum as a multiplicative packed dot product. -/
def pairTriM (w : ℕ) (fwd : Bool) (L W : IdentVec) (X Y : List SVec) (D E : ℚ) : ℚ :=
  triMatF fwd L W + triShortF fwd L W +
    ((L.sh.odd.map (fun q => L.sden * (q.2 : ℚ) * triTCF fwd W q.1)).sum +
      (tdotM w (trialityTensorT w (!fwd) X) Y : ℚ) / (2 * D * E)) / 2

/-- With packed tensors and bounds, the multiplicative pairing is the exact pairing. -/
theorem pairTriM_eq {w B C : ℕ} (fwd : Bool) (L W : IdentVec) {X Y : List SVec} {D E : ℚ}
    (hLt : L.ten = tensorRat w X D) (hWt : W.ten = tensorRat w Y E) (hX : TBnd w B X)
    (hY : TBnd w C Y) (hB : 4 * B < 2 ^ w) (hBC : 2 * (2 * 4096 * (4 * B * C)) < 2 ^ w) :
    pairTriM w fwd L W X Y D E = pairTri fwd L W := by
  rw [← pairTriP_eq fwd L W hLt hWt hX hB, pairTriM, pairTriP,
    tdotM_eq (trialityTensorT_spec (!fwd) hX hB).1 hY hBC]

/-- Forward identification from the multiplicative packed pairing. -/
theorem ident_forward_M (i j : Fin 12) (h g : H) (L W : IdentVec) {w B C : ℕ}
    {X Y : List SVec} {D E : ℚ} (hL : L.sh.ok = true) (hW : W.sh.ok = true)
    (hLt : L.ten = tensorRat w X D) (hWt : W.ten = tensorRat w Y E) (hX : TBnd w B X)
    (hY : TBnd w C Y) (hB : 4 * B < 2 ^ w) (hBC : 2 * (2 * 4096 * (4 * B * C)) < 2 ^ w)
    (hx : griessConwayEncode (rhoLocal h (generatedAxisGlobalTwelveRepresentative i)) = L.real)
    (hy : griessConwayEncode (rhoLocal g (generatedAxisGlobalTwelveRepresentative j)) = W.real)
    (hp : pairTriM w true L W X Y D E = 128) :
    sExtra (rhoLocal h (generatedAxisGlobalTwelveRepresentative i)) =
      rhoLocal g (generatedAxisGlobalTwelveRepresentative j) :=
  ident_forward i j h g L W hL hW hx hy (by rw [← pairTriM_eq true L W hLt hWt hX hY hB hBC, hp])

/-- Inverse identification from the multiplicative packed pairing. -/
theorem ident_inverse_M (i j : Fin 12) (h g : H) (L W : IdentVec) {w B C : ℕ}
    {X Y : List SVec} {D E : ℚ} (hL : L.sh.ok = true) (hW : W.sh.ok = true)
    (hLt : L.ten = tensorRat w X D) (hWt : W.ten = tensorRat w Y E) (hX : TBnd w B X)
    (hY : TBnd w C Y) (hB : 4 * B < 2 ^ w) (hBC : 2 * (2 * 4096 * (4 * B * C)) < 2 ^ w)
    (hx : griessConwayEncode (rhoLocal h (generatedAxisGlobalTwelveRepresentative i)) = L.real)
    (hy : griessConwayEncode (rhoLocal g (generatedAxisGlobalTwelveRepresentative j)) = W.real)
    (hp : pairTriM w false L W X Y D E = 128) :
    sExtra.symm (rhoLocal h (generatedAxisGlobalTwelveRepresentative i)) =
      rhoLocal g (generatedAxisGlobalTwelveRepresentative j) :=
  ident_inverse i j h g L W hL hW hx hy (by rw [← pairTriM_eq false L W hLt hWt hX hY hB hBC, hp])

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
