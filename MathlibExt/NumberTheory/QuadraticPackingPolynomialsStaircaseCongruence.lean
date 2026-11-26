/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.QuadraticPackingPolynomials
import Mathlib.Data.Finset.NatAntidiagonal
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Data.ZMod.Basic
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic.Choose
import Mathlib.Tactic.Convert
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GRewrite
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
import Mathlib.Tactic.Zify

/-!
# Staircase congruence for quadratic packing polynomials

Values on staircases whose indices differ by the positive step difference `k` are congruent
modulo `k`. We recover the homogeneous quadratic part from injectivity and a count of the
lattice points in the sector. The resulting translation formula rules out a repeated residue on
staircases less than `k` apart. The pigeonhole principle then gives the congruence.
-/

namespace MetaMathlibExt

namespace quadraticPackingPolynomial_staircase_congruence

private def InCone (m n : ℕ) (x y : ℤ) : Prop :=
  0 ≤ y ∧ m * y ≤ n * x

private theorem cone_mem {m n : ℕ} (hm : 0 < m) {x y : ℤ} (h : InCone m n x y) :
    ((x : ℝ), (y : ℝ)) ∈ sectorLatticePoints ((n : ℝ) / m) := by
  refine ⟨x, y, rfl, by exact_mod_cast h.1, ?_⟩
  rw [div_mul_eq_mul_div, le_div_iff₀ (by exact_mod_cast hm : 0 < (m : ℝ)), mul_comm]
  exact_mod_cast h.2

-- An integral ray strictly inside the sector eventually absorbs any translate.
private theorem ray_in_cone {m n : ℕ} (x y u v : ℤ)
    (hv : 0 < v) (huv : m * v < n * u) :
    ∃ t₀ : ℤ, ∀ t ≥ t₀, InCone m n (x + t * u) (y + t * v) := by
  refine ⟨max 0 (max (-y) (m * y - n * x)), ?_⟩
  intro t ht
  simp only [max_le_iff] at ht
  constructor
  · nlinarith [mul_nonneg ht.1 (show 0 ≤ v - 1 by omega)]
  · nlinarith [mul_nonneg ht.1 (show 0 ≤ n * u - m * v - 1 by omega)]

-- Extrapolate from three integer values on a ray in the sector using the zero third difference.
private theorem integral_values {m n : ℕ} (hm : 0 < m) (hn : 0 < n) {P : ℝ → ℝ → ℝ}
    (hP : IsQuadraticPackingPolynomial (sectorLatticePoints ((n : ℝ) / m)) P)
    (x y : ℤ) : ∃ z : ℤ, (z : ℝ) = P x y := by
  obtain ⟨a, b, c, d, e, f, -, h⟩ := hP.1
  let u : ℤ := m + 1
  let v : ℤ := n
  obtain ⟨t₀, ht⟩ := ray_in_cone (m := m) (n := n) x y u v
    (by dsimp [v]; exact_mod_cast hn) (by
      dsimp [u, v]
      nlinarith [show (0 : ℤ) < n by exact_mod_cast hn])
  let t := max t₀ 0
  have H (j : ℤ) (hj : 1 ≤ j) :
      ∃ w : ℕ, (w : ℝ) = P (x + (j * t : ℤ) * u) (y + (j * t : ℤ) * v) := by
    have ht' : t₀ ≤ j * t := (le_max_left ..).trans (le_mul_of_one_le_left (le_max_right ..) hj)
    obtain ⟨w, hw⟩ := hP.exists_nat_eq (cone_mem hm (ht _ ht'))
    exact ⟨w, by simpa using hw⟩
  obtain ⟨w₁, h₁⟩ := H 1 le_rfl
  obtain ⟨w₂, h₂⟩ := H 2 (by decide)
  obtain ⟨w₃, h₃⟩ := H 3 (by decide)
  refine ⟨3 * (w₁ : ℤ) - 3 * w₂ + w₃, ?_⟩
  push_cast at *
  rw [h₁, h₂, h₃]
  simp only [h]
  ring

private theorem integral_coefficients {m n : ℕ} (hm : 0 < m) (hn : 0 < n) {P : ℝ → ℝ → ℝ}
    (hP : IsQuadraticPackingPolynomial (sectorLatticePoints ((n : ℝ) / m)) P) :
    ∃ A B C D E F : ℤ, ∀ x y, 2 * P x y =
      A * x ^ 2 + 2 * B * x * y + C * y ^ 2 + D * x + E * y + F := by
  obtain ⟨a, b, c, d, e, f, -, h⟩ := hP.1
  choose z hz using integral_values hm hn hP
  let A := z 1 0 + z (-1) 0 - 2 * z 0 0
  let B := z 1 1 - z 1 0 - z 0 1 + z 0 0
  let C := z 0 1 + z 0 (-1) - 2 * z 0 0
  let D := z 1 0 - z (-1) 0
  let E := z 0 1 - z 0 (-1)
  let F := 2 * z 0 0
  have hA : (A : ℝ) = 2 * a := by simp [A, hz, h]; ring
  have hB : (B : ℝ) = b := by simp [B, hz, h]; ring
  have hC : (C : ℝ) = 2 * c := by simp [C, hz, h]; ring
  have hD : (D : ℝ) = 2 * d := by simp [D, hz, h]; ring
  have hE : (E : ℝ) = 2 * e := by simp [E, hz, h]; ring
  have hF : (F : ℝ) = 2 * f := by simp [F, hz, h]
  refine ⟨A, B, C, D, E, F, fun x y => ?_⟩
  rw [hA, hB, hC, hD, hE, hF, h]
  ring

private def poly (A B C D E F x y : ℤ) : ℤ :=
  A * x ^ 2 + 2 * B * x * y + C * y ^ 2 + D * x + E * y + F

private def QuadInjective (Q : ℤ → ℤ → ℤ) : Prop :=
  ∀ {x y u v : ℤ}, 0 ≤ x → 0 ≤ y → 0 ≤ u → 0 ≤ v → Q x y = Q u v → x = u ∧ y = v

-- An invertible Hessian gives two symmetric integral points of equal value.
-- Their common midpoint can be translated into the quadrant along the ray from the centre.
private theorem singular {A B C D E F : ℤ} (hinj : QuadInjective (poly A B C D E F)) :
    A * C - B ^ 2 = 0 := by
  let δ := A * C - B ^ 2
  change δ = 0
  by_contra hδ
  let U := δ * (C * D - B * E)
  let V := δ * (A * E - B * D)
  let T := max 1 (max (1 - U) (1 - V))
  let u := 2 * δ ^ 2 * T + U
  let v := 2 * δ ^ 2 * T + V
  have hT : 1 ≤ T ∧ 1 - U ≤ T ∧ 1 - V ≤ T :=
    ⟨le_max_left .., (le_max_left ..).trans (le_max_right ..),
      (le_max_right ..).trans (le_max_right ..)⟩
  have hd : 1 ≤ 2 * δ ^ 2 := by
    have := sq_pos_of_ne_zero hδ
    omega
  have hg : T ≤ 2 * δ ^ 2 * T := le_mul_of_one_le_left (by omega) hd
  have hu : 1 ≤ u := by dsimp [u]; omega
  have hv : 1 ≤ v := by dsimp [v]; omega
  -- At (T, T) the gradient is (g, h), so a symmetric displacement (h, -g)
  -- preserves the value. Moving the midpoint along (u, v) keeps this perpendicularity.
  let g := 2 * A * T + 2 * B * T + D
  let h := 2 * B * T + 2 * C * T + E
  let t := max (max (max g (-g)) (max h (-h))) 0
  have ht : g ≤ t ∧ -g ≤ t ∧ h ≤ t ∧ -h ≤ t := by
    dsimp only [t]
    omega
  have ht₀ : 0 ≤ t := le_max_right ..
  have htu := le_mul_of_one_le_right ht₀ hu
  have htv := le_mul_of_one_le_right ht₀ hv
  have heq : poly A B C D E F (T + t * u + h) (T + t * v - g) =
      poly A B C D E F (T + t * u - h) (T + t * v + g) := by
    dsimp only [poly, u, v, U, V, δ, g, h]
    ring
  obtain ⟨h₁, h₂⟩ := hinj (by omega) (by omega) (by omega) (by omega) heq
  have hg0 : g = 0 := by omega
  have hh0 : h = 0 := by omega
  have hz : u = δ * (C * g - B * h) := by dsimp only [u, U, δ, g, h]; ring
  rw [hg0, hh0] at hz
  simp at hz
  omega

-- A ray in the kernel would place infinitely many parallel progressions in a
-- finite set of residue classes.
private theorem no_null_ray {A B C D E F a b : ℤ}
    (hinj : QuadInjective (poly A B C D E F)) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hnz : a ≠ 0 ∨ b ≠ 0) (h₁ : A * a + B * b = 0) (h₂ : B * a + C * b = 0) : False := by
  let s := D * a + E * b
  have shift (x y t : ℤ) : poly A B C D E F (x + t * a) (y + t * b) =
      poly A B C D E F x y + t * s := by
    unfold poly s
    linear_combination (2 * t * x + t ^ 2 * a) * h₁ + (2 * t * y + t ^ 2 * b) * h₂
  by_cases hs : s = 0
  · have hv := shift 0 0 1
    simp only [one_mul, zero_add, hs, add_zero] at hv
    obtain ⟨rfl, rfl⟩ := hinj ha hb le_rfl le_rfl hv
    simp at hnz
  obtain ⟨u, v, hu, hv, huv⟩ : ∃ u v : ℤ, 0 ≤ u ∧ 0 ≤ v ∧ b * u - a * v ≠ 0 := by
    by_cases hb' : b = 0
    · exact ⟨0, 1, by decide, by decide, by simp; tauto⟩
    · exact ⟨1, 0, by decide, by decide, by simpa⟩
  let j := s ^ 3 * (A * u ^ 2 + 2 * B * u * v + C * v ^ 2) + s * (D * u + E * v)
  let t := max (-j) 0
  have ht : 0 ≤ t := le_max_right ..
  have htj : 0 ≤ t + j := by dsimp [t]; omega
  have heq : poly A B C D E F (0 + (t + j) * a) (0 + (t + j) * b) =
      poly A B C D E F (s ^ 2 * u + t * a) (s ^ 2 * v + t * b) := by
    rw [shift, shift]
    dsimp [j, poly]
    ring
  obtain ⟨hx, hy⟩ := hinj (by positivity) (by positivity) (by positivity) (by positivity) heq
  have hz : s ^ 2 * (b * u - a * v) = 0 := by linear_combination a * hy - b * hx
  exact (mul_ne_zero (pow_ne_zero _ hs) huv) hz

private theorem positive_coefficients {A B C D E F : ℤ}
    (hinj : QuadInjective (poly A B C D E F))
    (hnonneg : ∀ x ≥ 0, 0 ≤ poly A B C D E F x 0) :
    0 < A ∧ 0 < B ∧ A * C = B ^ 2 := by
  have hsing := singular hinj
  have hA : 0 ≤ A := by
    by_contra! h
    let t := max 1 (max (D + F + 1) (D + 1))
    have ht : 1 ≤ t ∧ D + F + 1 ≤ t ∧ D + 1 ≤ t := by dsimp [t]; omega
    have hval := hnonneg t (by omega)
    simp only [poly, mul_zero, zero_pow (by decide : 2 ≠ 0), add_zero] at hval
    have hA' := mul_nonneg (show 0 ≤ -1 - A by omega) (sq_nonneg t)
    have h' := mul_nonneg (show 0 ≤ t - D - 1 by omega) (show 0 ≤ t - 1 by omega)
    nlinarith
  have hA' : A ≠ 0 := by
    rintro rfl
    have hB : B = 0 := by simpa using hsing
    exact no_null_ray (a := 1) (b := 0) hinj (by decide) (by decide)
      (Or.inl one_ne_zero) (by simp) (by simp [hB])
  refine ⟨by omega, ?_, by linarith⟩
  by_contra! hB
  exact no_null_ray (a := -B) (b := A) hinj (by omega) hA (Or.inr hA')
    (by ring) (by linear_combination hsing)

private def rows (r : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.range r).biUnion Finset.antidiagonal

private theorem mem_rows {r : ℕ} {p : ℕ × ℕ} : p ∈ rows r ↔ p.1 + p.2 < r := by
  simp [rows, Finset.mem_antidiagonal]

private theorem rows_card (r : ℕ) : (rows r).card * 2 = r * (r + 1) := by
  induction r with
  | zero => simp [rows]
  | succ r ih =>
    have hd : Disjoint (rows r) (Finset.antidiagonal r) := by
      rw [Finset.disjoint_left]
      intro p hp h
      exact (mem_rows.mp hp).ne (Finset.mem_antidiagonal.mp h)
    rw [show rows (r + 1) = rows r ∪ Finset.antidiagonal r by
      ext p; simp [mem_rows, Finset.mem_antidiagonal]; omega]
    rw [Finset.card_union_of_disjoint hd, Finset.Nat.card_antidiagonal]
    nlinarith

-- If each diagonal has M(r+1) points and twice the value is a r² + O(r),
-- bijectivity forces M = a by counting the first R diagonals.
private theorem count_diagonals {L : Type} [Fintype L] {a c : ℕ}
    {f : L × (ℕ × ℕ) → ℕ} (hf : Function.Bijective f) (ha : 0 < a)
    (hupper : ∀ p, 2 * f p ≤ a * (p.2.1 + p.2.2) ^ 2 + c * (p.2.1 + p.2.2 + 1))
    (hlower : ∀ p, a * (p.2.1 + p.2.2) ^ 2 ≤ 2 * f p + c * (p.2.1 + p.2.2 + 1)) :
    Fintype.card L = a := by
  classical
  let M := Fintype.card L
  let R := 2 * (M + c + a + 3)
  let s := (Finset.univ : Finset L) ×ˢ rows R
  have mem (p : L × ℕ × ℕ) : p ∈ s ↔ p.2.1 + p.2.2 < R := by simp [s, mem_rows]
  have hcard : (s.image f).card * 2 = M * R * (R + 1) := by
    rw [Finset.card_image_of_injective _ hf.1, Finset.card_product, mul_assoc, rows_card]
    simp [M, mul_assoc]
  have hbig : (M + c) * R + c + 3 < R ^ 2 := by dsimp [R]; nlinarith
  apply le_antisymm
  · by_contra! h
    let U := a * R ^ 2 + c * (R + 1)
    have hsub : s.image f ⊆ Finset.range (U / 2 + 1) := by
      rintro _ hf'
      obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hf'
      have ht := (mem p).mp hp
      have hU : 2 * f p ≤ U := (hupper p).trans (by dsimp [U]; gcongr)
      simp only [Finset.mem_range]
      omega
    have hsize := Finset.card_le_card hsub
    rw [Finset.card_range] at hsize
    have hcard' : M * R * (R + 1) ≤ U + 2 := by omega
    have hgap := Nat.mul_le_mul_right (R ^ 2) (show a + 1 ≤ M from h)
    dsimp only [U] at hcard'
    nlinarith [Nat.zero_le (M * R)]
  · by_contra! h
    let V := (a * R ^ 2 - c * (R + 1)) / 2
    have hsub : Finset.range V ⊆ s.image f := by
      intro z hz
      obtain ⟨p, rfl⟩ := hf.2 z
      refine Finset.mem_image.mpr ⟨p, (mem p).mpr ?_, rfl⟩
      by_contra! ht
      let t := p.2.1 + p.2.2
      have ht' : R ≤ t := ht
      have hR : c ≤ a * (t + R) := by
        have hRc : c ≤ R := by dsimp [R]; omega
        exact hRc.trans ((by omega : R ≤ t + R).trans (Nat.le_mul_of_pos_left _ ha))
      have hmono := Nat.mul_le_mul_right (t - R) hR
      have htR := Nat.sub_add_cancel ht'
      have hdiff : a * R ^ 2 + c * (t + 1) ≤ a * t ^ 2 + c * (R + 1) := by
        zify at hmono ⊢
        push_cast [Nat.cast_sub ht'] at hmono
        nlinarith
      have hlow : a * t ^ 2 ≤ 2 * f p + c * (t + 1) := hlower p
      have hv : f p < (a * R ^ 2 - c * (R + 1)) / 2 := Finset.mem_range.mp hz
      omega
    have hsize := Finset.card_le_card hsub
    rw [Finset.card_range] at hsize
    dsimp [V] at hsize
    have hcard' : a * R ^ 2 ≤ M * R * (R + 1) + c * (R + 1) + 2 := by omega
    have hgap := Nat.mul_le_mul_right (R ^ 2) (show M + 1 ≤ a from h)
    nlinarith

-- At height nv + r the leftmost abscissa is mv + ⌈mr/n⌉. This partitions the sector
-- into n copies of the nonnegative quadrant.
private def baseX (m n : ℕ) (r : Fin n) : ℤ := -(-(m * (r : ℕ) : ℤ) / n)

private theorem baseX_le {m n : ℕ} (hn : 0 < n) (r : Fin n) (x : ℤ) :
    baseX m n r ≤ x ↔ m * (r : ℕ) ≤ (n : ℤ) * x := by
  unfold baseX
  rw [neg_le, Int.le_ediv_iff_mul_le (by exact_mod_cast hn)]
  constructor <;> intro h <;> linarith

private def conePoint (m n : ℕ) (p : Fin n × ℕ × ℕ) : ℝ × ℝ :=
  ((baseX m n p.1 : ℝ) + p.2.1 + p.2.2 * m, (p.2.2 : ℝ) * n + (p.1 : ℕ))

private theorem conePoint_bij {m n : ℕ} (hm : 0 < m) (hn : 0 < n) :
    Set.BijOn (conePoint m n) Set.univ (sectorLatticePoints ((n : ℝ) / m)) := by
  have : NeZero n := ⟨hn.ne'⟩
  constructor
  · rintro ⟨r, u, v⟩ _
    have h := (baseX_le (m := m) hn r (baseX m n r)).mp le_rfl
    have hmem : InCone m n (baseX m n r + u + v * m) ((v : ℤ) * n + (r : ℕ)) :=
      ⟨by positivity, by nlinarith [mul_nonneg (Int.natCast_nonneg n) (Int.natCast_nonneg u)]⟩
    simpa [conePoint] using cone_mem hm hmem
  constructor
  · rintro ⟨r, u, v⟩ - ⟨r', u', v'⟩ - heq
    obtain ⟨hx, hy⟩ := Prod.mk.inj heq
    have heqy : v * n + r = v' * n + r' := by exact_mod_cast hy
    have e := (Nat.divModEquiv n).symm.injective
      (a₁ := (v, r)) (a₂ := (v', r')) heqy
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj e
    congr 2
    exact_mod_cast (show (u : ℝ) = u' by linarith)
  · rintro _ ⟨x, y, rfl, hy, hxy⟩
    have hy0 : 0 ≤ y := by exact_mod_cast hy
    obtain ⟨⟨v, r⟩, he⟩ := (Nat.divModEquiv n).symm.surjective y.toNat
    change v * n + (r : ℕ) = y.toNat at he
    have hv : (v : ℤ) * n + (r : ℕ) = y := by
      rw [← Int.toNat_of_nonneg hy0]
      exact_mod_cast he
    have hxy' : (m : ℤ) * y ≤ (n : ℤ) * x := by
      rw [div_mul_eq_mul_div, le_div_iff₀ (by exact_mod_cast hm : 0 < (m : ℝ))] at hxy
      exact_mod_cast (mul_comm (y : ℝ) m ▸ hxy)
    have hbase : baseX m n r ≤ x - v * m := (baseX_le hn r _).mpr (by
      rw [← hv] at hxy'; nlinarith)
    let u := (x - v * m - baseX m n r).toNat
    have hu : (u : ℤ) = x - v * m - baseX m n r := Int.toNat_of_nonneg (by omega)
    refine ⟨⟨r, u, v⟩, Set.mem_univ _, Prod.ext ?_ ?_⟩
    · change (baseX m n r : ℝ) + u + v * m = x
      exact_mod_cast (show baseX m n r + (u : ℤ) + v * m = x by omega)
    · change (v : ℝ) * n + (r : ℕ) = y
      exact_mod_cast hv

private def refineCoords (n a b : ℕ) :
    ((Fin n × Fin b × Fin a) × ℕ × ℕ) → Fin n × ℕ × ℕ :=
  fun ⟨⟨r, s, t⟩, u, v⟩ => (r, u * b + s, v * a + t)

private theorem refineCoords_bij (n a b : ℕ) [NeZero a] [NeZero b] :
    Function.Bijective (refineCoords n a b) := by
  constructor
  · rintro ⟨⟨r, s, t⟩, u, v⟩ ⟨⟨r', s', t'⟩, u', v'⟩ h
    obtain ⟨hr, hpair⟩ := Prod.mk.inj h
    subst r'
    obtain ⟨hu, hv⟩ := Prod.mk.inj hpair
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj ((Nat.divModEquiv b).symm.injective
      (a₁ := (u, s)) (a₂ := (u', s')) hu)
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj ((Nat.divModEquiv a).symm.injective
      (a₁ := (v, t)) (a₂ := (v', t')) hv)
    rfl
  · rintro ⟨r, x, y⟩
    obtain ⟨⟨u, s⟩, rfl⟩ := (Nat.divModEquiv b).symm.surjective x
    obtain ⟨⟨v, t⟩, rfl⟩ := (Nat.divModEquiv a).symm.surjective y
    exact ⟨((r, s, t), u, v), rfl⟩

private theorem count_coeffs {L : Type} [Fintype L] {a : ℕ} {f : L × ℕ × ℕ → ℕ}
    (hf : Function.Bijective f) (ha : 0 < a) (D E F : L → ℤ)
    (heq : ∀ (l : L) (u v : ℕ), (2 : ℤ) * f (l, u, v) =
      a * (u + v : ℤ) ^ 2 + D l * u + E l * v + F l) :
    Fintype.card L = a := by
  classical
  let c := ∑ l : L, ((D l).natAbs + (E l).natAbs + (F l).natAbs)
  have h (l : L) : (D l).natAbs + (E l).natAbs + (F l).natAbs ≤ c :=
    Finset.single_le_sum (f := fun l : L => (D l).natAbs + (E l).natAbs + (F l).natAbs)
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ l)
  have hlim (l : L) (u v : ℕ) :
      |D l * u + E l * v + F l| ≤ (c : ℤ) * (u + v + 1) := by
    have hc : |D l| + |E l| + |F l| ≤ (c : ℤ) := by
      have hh := Int.ofNat_le.mpr (h l)
      simpa using hh
    have hu : |D l| ≤ (c : ℤ) := by linarith [abs_nonneg (E l), abs_nonneg (F l)]
    have hv : |E l| ≤ (c : ℤ) := by linarith [abs_nonneg (D l), abs_nonneg (F l)]
    have hw : |F l| ≤ (c : ℤ) := by linarith [abs_nonneg (D l), abs_nonneg (E l)]
    calc _ ≤ |D l * u| + |E l * v| + |F l| := by grw [abs_add_le, abs_add_le]
         _ ≤ (c : ℤ) * (u + v + 1) := by
           simp only [abs_mul, abs_of_nonneg (Int.natCast_nonneg _)]
           nlinarith [mul_le_mul_of_nonneg_right hu (Int.natCast_nonneg u),
             mul_le_mul_of_nonneg_right hv (Int.natCast_nonneg v)]
  apply count_diagonals (c := c) hf ha <;> rintro ⟨l, u, v⟩ <;> dsimp <;> zify
  · linarith [(abs_le.mp (hlim l u v)).2, heq l u v]
  · linarith [(abs_le.mp (hlim l u v)).1, heq l u v]

private theorem leading_relation {m n : ℕ} (hm : 0 < m) (hn : 0 < n) {P : ℝ → ℝ → ℝ}
    (hP : IsQuadraticPackingPolynomial (sectorLatticePoints ((n : ℝ) / m)) P)
    {A B C D E F : ℤ} (hform : ∀ x y : ℝ, 2 * P x y =
      A * x ^ 2 + 2 * B * x * y + C * y ^ 2 + D * x + E * y + F) :
    0 < A ∧ A * C = B ^ 2 ∧ A * m + B * n = n := by
  let H := A * m + B * n
  let K := A * m ^ 2 + 2 * B * m * n + C * n ^ 2
  let J := D * m + E * n
  have horig (x y : ℤ) : 2 * P x y = (poly A B C D E F x y : ℤ) := by
    rw [hform]
    simp [poly]
  have hgeom (x y : ℤ) : (poly A H K D J F x y : ℝ) = 2 * P (x + m * y) (n * y) := by
    rw [hform]
    dsimp [poly, H, K, J]
    push_cast
    ring
  have hmem (x y : ℤ) (hx : 0 ≤ x) (hy : 0 ≤ y) :
      ((x + (m : ℝ) * y), ((n : ℝ) * y)) ∈ sectorLatticePoints ((n : ℝ) / m) := by
    have h : InCone m n (x + m * y) (n * y) := ⟨by positivity, by
      nlinarith [mul_nonneg (Int.natCast_nonneg n) hx]⟩
    simpa using cone_mem hm h
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hinj : QuadInjective (poly A H K D J F) := by
    intro x y u v hx hy hu hv heq
    have hval := congrArg (Int.cast (R := ℝ)) heq
    rw [hgeom, hgeom] at hval
    have he := hP.2.injOn (hmem _ _ hx hy) (hmem _ _ hu hv)
      (show P _ _ = P _ _ by linarith)
    obtain ⟨h₁, h₂⟩ := Prod.mk.inj he
    have hy' := mul_left_cancel₀ hnR h₂
    rw [hy', add_left_inj] at h₁
    exact ⟨by exact_mod_cast h₁, by exact_mod_cast hy'⟩
  have hnn (x : ℤ) (hx : 0 ≤ x) : 0 ≤ poly A H K D J F x 0 := by
    obtain ⟨t, ht⟩ := hP.exists_nat_eq (hmem x 0 hx le_rfl)
    have h := hgeom x 0
    dsimp only at ht
    have : 0 ≤ (poly A H K D J F x 0 : ℝ) := by rw [h, ← ht]; positivity
    exact_mod_cast this
  obtain ⟨hA, hH, hdet⟩ := positive_coefficients hinj hnn
  have hdisc : A * C = B ^ 2 := by
    dsimp [K, H] at hdet
    have h0 : (A * C - B ^ 2) * (n : ℤ) ^ 2 = 0 := by linear_combination hdet
    have hnZ : (n : ℤ) ≠ 0 := by exact_mod_cast hn.ne'
    exact sub_eq_zero.mp ((mul_eq_zero.mp h0).resolve_right (pow_ne_zero _ hnZ))
  refine ⟨hA, hdisc, ?_⟩
  let a := A.toNat
  let b := H.toNat
  have ha : (a : ℤ) = A := Int.toNat_of_nonneg hA.le
  have hb : (b : ℤ) = H := Int.toNat_of_nonneg hH.le
  have ha' : 0 < a := by omega
  have hb' : 0 < b := by omega
  have : NeZero a := ⟨ha'.ne'⟩
  have : NeZero b := ⟨hb'.ne'⟩
  -- Split the two quadrant coordinates into residues modulo H and A. On each of
  -- the nHA resulting grids the leading term of 2P is A H² (u + v)².
  let L := Fin n × Fin b × Fin a
  let coord : L × ℕ × ℕ → ℝ × ℝ := conePoint m n ∘ refineCoords n a b
  have hc : Set.BijOn coord Set.univ (sectorLatticePoints ((n : ℝ) / m)) :=
    (conePoint_bij hm hn).comp (refineCoords_bij n a b).bijOn_univ
  have hvals := hP.2.comp hc
  choose f hf using fun p => hvals.mapsTo (Set.mem_univ p)
  have hfb : Function.Bijective f := by
    constructor
    · intro p q h
      apply hvals.injOn (Set.mem_univ p) (Set.mem_univ q)
      rw [← hf p, ← hf q, h]
    · intro z
      obtain ⟨p, -, hp⟩ := hvals.surjOn (Set.mem_range_self z)
      exact ⟨p, Nat.cast_injective (R := ℝ) ((hf p).trans hp)⟩
  let X (l : L) : ℤ := baseX m n l.1 + (l.2.1 : ℕ) + (l.2.2 : ℕ) * m
  let Y (l : L) : ℤ := (l.2.2 : ℕ) * n + (l.1 : ℕ)
  let d (l : L) := 2 * A * X l + 2 * B * Y l + D
  let e (l : L) := 2 * B * X l + 2 * C * Y l + E
  have hcard := count_coeffs hfb (show 0 < a * b ^ 2 by positivity)
    (fun l => H * d l) (fun l => A * (m * d l + n * e l)) (fun l => poly A B C D E F (X l) (Y l))
    (by
      intro l u v
      let x := X l + (u : ℤ) * b + (v : ℤ) * a * m
      let y := Y l + (v : ℤ) * a * n
      have hcxy : coord (l, u, v) = ((x : ℝ), (y : ℝ)) := by
        obtain ⟨r, s, t⟩ := l
        ext <;> dsimp [coord, conePoint, refineCoords, x, y, X, Y] <;> push_cast <;> ring
      have hf' := hf (l, u, v)
      change (f (l, u, v) : ℝ) = P _ _ at hf'
      rw [hcxy] at hf'
      have heq : (2 : ℤ) * f (l, u, v) = poly A B C D E F x y := by
        exact_mod_cast (show 2 * (f (l, u, v) : ℝ) = (poly A B C D E F x y : ℝ) by
          rw [hf']; exact horig _ _)
      rw [heq]
      dsimp only [poly, x, y, d, e]
      push_cast
      rw [ha, hb]
      dsimp only [H, K] at hdet ⊢
      linear_combination A * (v : ℤ) ^ 2 * hdet)
  have hcard' : n * b * a = a * b ^ 2 := by simpa [L, Nat.mul_assoc] using hcard
  have hbn : b = n := by
    apply mul_right_cancel₀ (Nat.mul_pos hb' ha').ne'
    calc b * (b * a) = a * b ^ 2 := by ring
         _ = n * (b * a) := by rw [← hcard', Nat.mul_assoc]
  change H = n
  rw [← hb, hbn]

private theorem packing_form {m n : ℕ} (hm : 0 < m) (hn : 0 < n) (hmn : Nat.Coprime m n)
    {P : ℝ → ℝ → ℝ} (hP : IsQuadraticPackingPolynomial (sectorLatticePoints ((n : ℝ) / m)) P) :
    ∃ D E F : ℝ, ∀ x y, P x y =
      ((n : ℝ) * x - ((m : ℝ) - 1) * y) ^ 2 / (2 * n) + D * x + E * y + F := by
  obtain ⟨A, B, C, D, E, F, h⟩ := integral_coefficients hm hn hP
  obtain ⟨hA, hdisc, hcoeff⟩ := leading_relation hm hn hP h
  have hnZ : 0 < (n : ℤ) := by exact_mod_cast hn
  have hbez := Nat.gcd_eq_gcd_ab m n
  rw [hmn.gcd_eq_one, Nat.cast_one] at hbez
  let t := (1 - B) * Nat.gcdA m n + A * Nat.gcdB m n
  have ht : A = n * t := by
    dsimp [t]
    linear_combination A * hbez + (Nat.gcdA m n : ℤ) * hcoeff
  have hB : B = 1 - m * t := by
    apply mul_left_cancel₀ hnZ.ne'
    linear_combination hcoeff - (m : ℤ) * ht
  have hdiv : t * (n * C + 2 * m - t * m ^ 2) = 1 := by
    linear_combination hdisc - C * ht + (B + 1 - m * t) * hB
  have htpos : 0 < t := by
    by_contra! ht'
    linarith [mul_nonpos_of_nonneg_of_nonpos hnZ.le ht']
  have hpos : 0 < (n * C + 2 * m - t * m ^ 2 : ℤ) :=
    pos_of_mul_pos_right (by rw [hdiv]; decide) htpos.le
  have ht1 : t = 1 := by
    have hle := le_mul_of_one_le_right htpos.le (show 1 ≤ n * C + 2 * m - t * m ^ 2 by omega)
    omega
  simp only [ht1, mul_one] at ht hB
  subst A
  subst B
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hC : (n : ℝ) * C = (1 - (m : ℝ)) ^ 2 := by exact_mod_cast hdisc
  refine ⟨D / 2, E / 2, F / 2, fun x y => ?_⟩
  have hxy := h x y
  push_cast at hxy
  field_simp [hnR]
  linear_combination (n : ℝ) * hxy + y ^ 2 * hC

private def level (m n : ℕ) (x y : ℤ) : ℤ := n * x - ((m : ℤ) - 1) * y

private theorem no_short_period {m n k : ℕ} (hm : 0 < m) (hn : 0 < n) {P : ℝ → ℝ → ℝ}
    (hP : IsQuadraticPackingPolynomial (sectorLatticePoints ((n : ℝ) / m)) P)
    (hkP : consecutiveStepDifference m n P = k)
    {D E F : ℝ} (hform : ∀ x y, P x y =
      ((n : ℝ) * x - ((m : ℝ) - 1) * y) ^ 2 / (2 * n) + D * x + E * y + F)
    {px py qx qy h z : ℤ} (hh : 0 < h) (hhk : h < k)
    (hgap : level m n qx qy - level m n px py = (Nat.gcd (m - 1) n : ℤ) * h)
    (heq : P qx qy - P px py = z * k) : False := by
  let l := Nat.gcd (m - 1) n
  let a : ℤ := ((m - 1) / l : ℕ)
  let b : ℤ := (n / l : ℕ)
  have hl : 0 < (l : ℤ) := by exact_mod_cast Nat.gcd_pos_of_pos_right (m - 1) hn
  have ha : a * l = (m : ℤ) - 1 := by
    have h := Nat.div_mul_cancel (Nat.gcd_dvd_left (m - 1) n)
    simpa only [a, l, Nat.cast_mul, Nat.cast_sub hm, Nat.cast_one] using
      congrArg (Nat.cast (R := ℤ)) h
  have hb : b * l = n := by
    simpa only [b, l, Nat.cast_mul] using congrArg (Nat.cast (R := ℤ))
      (Nat.div_mul_cancel (Nat.gcd_dvd_right (m - 1) n))
  have htan : level m n a b = 0 := by
    unfold level
    linear_combination b * ha - a * hb
  have hlR : (l : ℝ) ≠ 0 := by exact_mod_cast hl.ne'
  have haR : (a : ℝ) = ((m : ℝ) - 1) / l := (eq_div_iff hlR).mpr (by exact_mod_cast ha)
  have hbR : (b : ℝ) = n / l := (eq_div_iff hlR).mpr (by exact_mod_cast hb)
  have hk : P a b - P 0 0 = k := by rw [haR, hbR]; exact hkP
  have htanR : (n : ℝ) * a - ((m : ℝ) - 1) * b = 0 := by exact_mod_cast htan
  have hstep (x y t : ℤ) :
      P (x + t * a : ℤ) (y + t * b : ℤ) = P x y + t * k := by
    simp only [hform] at hk ⊢
    rw [htanR] at hk
    push_cast
    rw [show (n : ℝ) * (x + t * a) - ((m : ℝ) - 1) * (y + t * b) = n * x - ((m : ℝ) - 1) * y by
      linear_combination (t : ℝ) * htanR]
    simp at hk
    linear_combination (t : ℝ) * hk
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hgapR : (n : ℝ) * qx - ((m : ℝ) - 1) * qy - ((n : ℝ) * px - ((m : ℝ) - 1) * py) = l * h := by
    exact_mod_cast hgap
  have hshift (s : ℤ) : P (qx + s : ℤ) qy - P (px + s : ℤ) py = z * k + s * (l : ℝ) * h := by
    simp only [hform] at heq ⊢
    push_cast
    field_simp [hnR] at heq ⊢
    linear_combination heq + 2 * (s : ℝ) * n * hgapR
  -- Moving both points horizontally by 2kt adds 2ktlh to their value difference.
  -- Move p an extra 2tlh steps to absorb this change, and move both up lt steps
  -- so that both translation vectors point strictly inside the sector.
  let u (j : ℤ) := 2 * (k : ℤ) + j * (a * l)
  let v (j : ℤ) := j * (b * l)
  have hin (x y j : ℤ) (hj : 0 < j) (hjk : j < 2 * k) :=
    ray_in_cone (m := m) (n := n) x y (u j) (v j) (by
      dsimp [v]; rw [hb]; exact mul_pos hj (by exact_mod_cast hn)) (by
      dsimp [u, v]
      rw [ha, hb]
      nlinarith [mul_pos (show (0 : ℤ) < n by exact_mod_cast hn) (sub_pos.mpr hjk)])
  obtain ⟨t₁, hp⟩ := hin (px + z * a) (py + z * b) (2 * h + 1) (by omega) (by omega)
  obtain ⟨t₂, hq⟩ := hin qx qy 1 (by decide) (by omega)
  let t := max t₁ t₂
  let s := 2 * (k : ℤ) * t
  let jp := z + (2 * h + 1) * l * t
  let jq := (l : ℤ) * t
  have hp' : InCone m n (px + s + jp * a) (py + jp * b) := by
    convert hp t (le_max_left ..) using 1 <;> dsimp [s, jp, u, v] <;> ring
  have hq' : InCone m n (qx + s + jq * a) (qy + jq * b) := by
    convert hq t (le_max_right ..) using 1 <;> dsimp [s, jq, u, v] <;> ring
  have hpq : P (px + s + jp * a : ℤ) (py + jp * b : ℤ) =
      P (qx + s + jq * a : ℤ) (qy + jq * b : ℤ) := by
    rw [hstep, hstep]
    have h := hshift s
    dsimp only [s, jp, jq] at h ⊢
    push_cast at h ⊢
    linear_combination -h
  have hxy := hP.2.injOn (cone_mem hm hp') (cone_mem hm hq') hpq
  obtain ⟨hx, hy⟩ := Prod.mk.inj hxy
  have hx' : px + s + jp * a = qx + s + jq * a := by exact_mod_cast hx
  have hy' : py + jp * b = qy + jq * b := by exact_mod_cast hy
  have hz : level m n qx qy - level m n px py = 0 := by
    dsimp only [level] at htan ⊢
    linear_combination -(n : ℤ) * hx' + ((m : ℤ) - 1) * hy' + (jp - jq) * htan
  rw [hgap] at hz
  exact (mul_ne_zero hl.ne' hh.ne') hz

-- The k+1 representatives must repeat a residue. A gap less than k is impossible,
-- so only the two endpoints can repeat.
private theorem endpoints {k : ℕ} (hk : 0 < k) (g : Fin (k + 1) → ℤ)
    (hshort : ∀ r s : Fin (k + 1), r < s → (s : ℕ) - (r : ℕ) < k →
      ¬ (k : ℤ) ∣ g s - g r) : (k : ℤ) ∣ g (Fin.last k) - g 0 := by
  have : NeZero k := ⟨hk.ne'⟩
  obtain ⟨r, s, hne, he⟩ := Fintype.exists_ne_map_eq_of_card_lt
    (fun r => (g r : ZMod k)) (by simp)
  have ordered (x y : Fin (k + 1)) (hxy : x < y) (heq : (g x : ZMod k) = g y) :
      (k : ℤ) ∣ g (Fin.last k) - g 0 := by
    have hd := (ZMod.intCast_eq_intCast_iff_dvd_sub ..).mp heq
    by_cases h : (y : ℕ) - x < k
    · exact (hshort x y hxy h hd).elim
    · have hx : x = 0 := Fin.ext (by change x.val = 0; omega)
      have hy : y = Fin.last k := Fin.ext (by simp; omega)
      simpa [hx, hy] using hd
  rcases lt_or_gt_of_ne hne with hrs | hsr
  · exact ordered r s hrs he
  · exact ordered s r hsr he.symm

end quadraticPackingPolynomial_staircase_congruence

open quadraticPackingPolynomial_staircase_congruence

/-- **Staircase congruence for quadratic packing polynomials.** Let $m, n$ be positive coprime
integers, let $P$ be a quadratic packing polynomial on the lattice sector $I(n/m)$, and suppose
that the step difference of $P$ equals a positive integer $k$. Then for every natural number
$i$, every point $p$ of the staircase $J_i$ and every point $q$ of the staircase $J_{i+k}$, the
difference $P(q) - P(p)$ is an integer multiple of $k$.

Source: Brandt and Gjaldbæk, *Classification of Quadratic Packing Polynomials on Sectors of
R^2*, INTEGERS 25 (2025), Article A81, Lemma 2 (`integers-2025-A81-lem-2`). -/
public theorem quadraticPackingPolynomial_staircase_congruence {m n k : ℕ} (hm : 0 < m)
    (hn : 0 < n) (hmn : Nat.Coprime m n) {P : ℝ → ℝ → ℝ}
    (hP : IsQuadraticPackingPolynomial (sectorLatticePoints ((n : ℝ) / m)) P)
    (hk : 0 < k) (hkP : consecutiveStepDifference m n P = k) (i : ℕ) {p q : ℝ × ℝ}
    (hp : p ∈ sectorStaircase m n i) (hq : q ∈ sectorStaircase m n (i + k)) :
    ∃ z : ℤ, P q.1 q.2 - P p.1 p.2 = z * k := by
  obtain ⟨D, E, F, hform⟩ := packing_form hm hn hmn hP
  obtain ⟨⟨px, py, rfl, -⟩, hp⟩ := hp
  obtain ⟨⟨qx, qy, rfl, -⟩, hq⟩ := hq
  let l := Nat.gcd (m - 1) n
  have hp' : level m n px py = l * i := by
    dsimp only [level, l]
    dsimp only at hp
    exact_mod_cast hp
  have hq' : level m n qx qy = l * (i + k : ℤ) := by
    dsimp only [level, l]
    dsimp only [Nat.cast_add] at hq
    exact_mod_cast hq
  let a := Nat.gcdA (m - 1) n
  let b := Nat.gcdB (m - 1) n
  have hdir : level m n b (-a) = l := by
    have h := Nat.gcd_eq_gcd_ab (m - 1) n
    rw [Nat.cast_sub hm, Nat.cast_one] at h
    dsimp [a, b, level, l]
    linear_combination -h
  let pt (j : Fin (k + 1)) : ℤ × ℤ :=
    if j = Fin.last k then (qx, qy) else (px + (j : ℕ) * b, py - (j : ℕ) * a)
  have hlast : pt (Fin.last k) = (qx, qy) := by simp [pt]
  have hzero : pt 0 = (px, py) := by
    have hne : (0 : Fin (k + 1)) ≠ Fin.last k := by
      intro h
      have := congrArg Fin.val h
      exact hk.ne' this.symm
    simp [pt, hne]
  have hlevel (j) : level m n (pt j).1 (pt j).2 = l * (i + (j : ℕ) : ℤ) := by
    by_cases h : j = Fin.last k
    · subst j
      simpa only [hlast, Fin.val_last] using hq'
    · simp only [pt, h, ite_false]
      dsimp only [level] at hp' hdir ⊢
      linear_combination hp' + (j : ℕ) * hdir
  choose g hg using fun j => integral_values hm hn hP (pt j).1 (pt j).2
  have hd := endpoints hk g (by
    intro r s hrs hlt hdvd
    obtain ⟨z, hz⟩ := hdvd
    apply no_short_period hm hn hP hkP hform (h := (s : ℕ) - (r : ℤ)) (z := z)
      (px := (pt r).1) (py := (pt r).2) (qx := (pt s).1) (qy := (pt s).2) (by omega) (by omega)
    · linear_combination hlevel s - hlevel r
    · rw [← hg, ← hg, mul_comm]
      exact_mod_cast hz)
  obtain ⟨z, hz⟩ := hd
  refine ⟨z, ?_⟩
  have h₀ := hg 0
  have hₖ := hg (Fin.last k)
  rw [hzero] at h₀
  rw [hlast] at hₖ
  rw [← h₀, ← hₖ, mul_comm]
  exact_mod_cast hz

end MetaMathlibExt
