/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.Padics.HilbertSymbol.OddFormula

/-!
# The formula for the $2$-adic Hilbert symbol

Write nonzero $a, b \in \mathbb{Q}_2$ as $a = 2^\alpha u$ and $b = 2^\beta v$ with
$\alpha, \beta \in \mathbb{Z}$ and $u, v$ units of $\mathbb{Z}_2$. Then

$$(a, b)_2 = (-1)^{\varepsilon(u)\varepsilon(v) + \alpha\omega(v) + \beta\omega(u)},$$

where $\varepsilon(u)$ and $\omega(u)$ are the classes modulo $2$ of $(u - 1)/2$ and
$(u^2 - 1)/8$ (J.-P. Serre, *A Course in Arithmetic*, Chapter III, §1.2, Theorem 1, p. 20, the
case $p = 2$).

In the statement, $\varepsilon(u)$ and $\omega(u)$ are computed from the representative
$\bar u \in \{1, 3, 5, 7\}$ of $u$ modulo $8$, as the natural numbers $(\bar u - 1)/2$ and
$(\bar u^2 - 1)/8$, and $\alpha, \beta$ enter through their absolute values. As $u \equiv \bar u$
modulo $8$, these numbers have the parities of Serre's $(u - 1)/2$ and $(u^2 - 1)/8$, and the
exponent has the parity of Serre's.

The proof reduces $\alpha$ and $\beta$ modulo $2$ and works with Serre's definition through
nontrivial zeros of $z^2 - a x^2 - b y^2$, which agrees with the one used here by
`hilbertSymbol.eq_one_iff_exists_ternary_eq_zero`. A nontrivial zero can be scaled to integers
with one coordinate equal to $1$, and reducing it modulo $8$ gives the conditions on $u$ and $v$;
conversely, the zeros are built from square roots of units congruent to $1$ modulo $8$, which
exist by Hensel's lemma. The case $(2u, 2v)$ reduces to the case $(2u, -uv)$ through
$(a, b) = (a, -ab)$.

On the way it records that a unit of $\mathbb{Z}_2$ is a square exactly when it is congruent to
$1$ modulo $8$.
-/

set_option autoImplicit false

@[expose] public section

namespace PadicInt

-- An element of `ℤ_[2]` congruent to `1` modulo `8` is a square (Hensel's lemma).
theorem isSquare_of_toZModPow_three_eq_one {w : ℤ_[2]} (hw : PadicInt.toZModPow 3 w = 1) :
    IsSquare w := by
  have hmem : (1 - w) ∈ Ideal.span {((2 : ℕ) : ℤ_[2]) ^ 3} := by
    rw [← PadicInt.ker_toZModPow, RingHom.mem_ker, map_sub, map_one, hw, sub_self]
  have h1 : ‖(1 : ℤ_[2]) - w‖ ≤ ((2 : ℕ) : ℝ) ^ (-((3 : ℕ) : ℤ)) :=
    (PadicInt.norm_le_pow_iff_mem_span_pow _ _).2 hmem
  have h2 : ‖(2 : ℤ_[2])‖ = 2⁻¹ := by
    have := PadicInt.norm_p (p := 2)
    simpa using this
  open Polynomial in
  have h_eval : Polynomial.aeval (1 : ℤ_[2]) (X ^ 2 - C w) = 1 - w := by simp [aeval_def]
  open Polynomial in
  have h_der : Polynomial.aeval (1 : ℤ_[2]) (Polynomial.derivative (X ^ 2 - C w)) = 2 := by
    simp only [derivative_sub, derivative_X_pow, derivative_C, sub_zero, map_mul, map_pow,
      aeval_X, Nat.cast_ofNat, map_ofNat, one_pow, mul_one]
  open Polynomial in
  have hhyp : ‖Polynomial.aeval (1 : ℤ_[2]) (X ^ 2 - C w)‖ <
      ‖Polynomial.aeval (1 : ℤ_[2]) (Polynomial.derivative (X ^ 2 - C w))‖ ^ 2 := by
    rw [h_eval, h_der, h2]
    refine lt_of_le_of_lt h1 ?_
    norm_num
  open Polynomial in
  obtain ⟨z, hz, -⟩ := hensels_lemma hhyp
  refine ⟨z, ?_⟩
  simp [aeval_def] at hz
  linear_combination -hz

/-- **Squares among the units of $\mathbb{Z}_2$.** A unit $w$ of $\mathbb{Z}_2$ is a square in
$\mathbb{Z}_2$ if and only if $w \equiv 1 \pmod 8$. -/
theorem isSquare_unit_iff_toZModPow_three_eq_one (w : ℤ_[2]ˣ) :
    IsSquare (w : ℤ_[2]) ↔ PadicInt.toZModPow 3 (w : ℤ_[2]) = 1 := by
  refine ⟨?_, isSquare_of_toZModPow_three_eq_one⟩
  rintro ⟨s, hs⟩
  have hsu : IsUnit (PadicInt.toZModPow 3 s) := by
    have hs' : IsUnit (s * s) := hs ▸ w.isUnit
    exact (isUnit_of_mul_isUnit_left hs').map _
  obtain ⟨t, ht⟩ := hsu.exists_right_inv
  have key : ∀ r t : ZMod 8, r * t = 1 → r * r = 1 := by decide
  rw [hs, map_mul]
  exact key _ _ ht

end PadicInt

namespace HilbertSymbol

section Field

variable {F : Type*} [Field F]

/-- The ternary form $z^2 - A x^2 - B y^2$ has a nontrivial zero. -/
private def Iso (A B : F) : Prop :=
  ∃ z x y : F, ¬(z = 0 ∧ x = 0 ∧ y = 0) ∧ z ^ 2 - A * x ^ 2 - B * y ^ 2 = 0

private theorem iso_comm {A B : F} : Iso A B ↔ Iso B A := by
  constructor <;>
  · rintro ⟨z, x, y, hne, h⟩
    exact ⟨z, y, x, fun h' => hne ⟨h'.1, h'.2.2, h'.2.1⟩, by linear_combination h⟩

private theorem iso_mul_sq {A B c : F} (hc : c ≠ 0) : Iso (A * c ^ 2) B ↔ Iso A B := by
  constructor
  · rintro ⟨z, x, y, hne, h⟩
    refine ⟨z, c * x, y, fun h' => hne ⟨h'.1, ?_, h'.2.2⟩, by linear_combination h⟩
    simpa [hc] using h'.2.1
  · rintro ⟨z, x, y, hne, h⟩
    refine ⟨z, x / c, y, fun h' => hne ⟨h'.1, ?_, h'.2.2⟩, ?_⟩
    · simpa [hc] using h'.2.1
    · have : A * c ^ 2 * (x / c) ^ 2 = A * x ^ 2 := by field_simp
      linear_combination h - this

/-- One half of $(a, b) = (a, -ab)$. -/
private theorem iso_neg_mul {A B : F} (hA : A ≠ 0) (h : Iso A B) : Iso A (-(A * B)) := by
  obtain ⟨z, x, y, hne, h⟩ := h
  refine ⟨A * x, z, y, fun h' => hne ⟨h'.2.1, ?_, h'.2.2⟩, by linear_combination (-A) * h⟩
  simpa [hA] using h'.1

/-- $(a, b) = (a, -ab)$, for the ternary form. -/
private theorem iso_neg_mul_iff {A B : F} (hA : A ≠ 0) : Iso A B ↔ Iso A (-(A * B)) := by
  refine ⟨iso_neg_mul hA, fun h => ?_⟩
  have h' := iso_neg_mul hA h
  have hAB : -(A * -(A * B)) = B * A ^ 2 := by ring
  rw [hAB, iso_comm, iso_mul_sq hA, iso_comm] at h'
  exact h'

end Field

private theorem coe_two : ((2 : ℤ_[2]) : ℚ_[2]) = 2 := by
  simpa using PadicInt.coe_natCast (p := 2) 2

private theorem coe_four : ((4 : ℤ_[2]) : ℚ_[2]) = 4 := by
  simpa using PadicInt.coe_natCast (p := 2) 4

/-- Residues modulo $8$ of units of $\mathbb{Z}_2$. -/
private def OddRes (r : ZMod 8) : Prop :=
  r = 1 ∨ r = 3 ∨ r = 5 ∨ r = 7

private theorem oddRes_of_isUnit {w : ℤ_[2]} (hw : IsUnit w) :
    OddRes (PadicInt.toZModPow 3 w) := by
  obtain ⟨t, ht⟩ := (hw.map (PadicInt.toZModPow 3)).exists_right_inv
  have key : ∀ r t : ZMod 8, r * t = 1 → OddRes r := by
    unfold OddRes
    decide
  exact key _ _ ht

/-- A nontrivial zero of $z^2 - A x^2 - B y^2$ over $\mathbb{Q}_p$ with $A, B \in \mathbb{Z}_p$
scales to a zero over $\mathbb{Z}_p$ with one coordinate equal to $1$. -/
private theorem exists_int_zero {p : ℕ} [Fact p.Prime] {A B : ℤ_[p]}
    (h : Iso (A : ℚ_[p]) (B : ℚ_[p])) :
    ∃ Z X Y : ℤ_[p], Z ^ 2 = A * X ^ 2 + B * Y ^ 2 ∧ (Z = 1 ∨ X = 1 ∨ Y = 1) := by
  obtain ⟨z, x, y, hne, h⟩ := h
  -- Scaling by a coordinate `w` of largest norm.
  have scale : ∀ w : ℚ_[p], ‖z‖ ≤ ‖w‖ → ‖x‖ ≤ ‖w‖ → ‖y‖ ≤ ‖w‖ →
      ∃ Z X Y : ℤ_[p], Z ^ 2 = A * X ^ 2 + B * Y ^ 2 ∧ (Z : ℚ_[p]) = z / w ∧
        (X : ℚ_[p]) = x / w ∧ (Y : ℚ_[p]) = y / w := by
    intro w hz hx hy
    have hw : w ≠ 0 := by
      intro hw0
      rw [hw0, norm_zero, norm_le_zero_iff] at hz hx hy
      exact hne ⟨hz, hx, hy⟩
    have hwn : 0 < ‖w‖ := norm_pos_iff.2 hw
    have hle : ∀ t : ℚ_[p], ‖t‖ ≤ ‖w‖ → ‖t / w‖ ≤ 1 := fun t ht => by
      rw [norm_div]
      exact (div_le_one hwn).2 ht
    refine ⟨⟨z / w, hle z hz⟩, ⟨x / w, hle x hx⟩, ⟨y / w, hle y hy⟩, ?_, rfl, rfl, rfl⟩
    apply PadicInt.ext
    simp only [PadicInt.coe_add, PadicInt.coe_mul]
    change (z / w) ^ 2 = (A : ℚ_[p]) * (x / w) ^ 2 + (B : ℚ_[p]) * (y / w) ^ 2
    field_simp
    linear_combination h
  have hz := le_max_left (max ‖z‖ ‖x‖) ‖y‖
  have hy := le_max_right (max ‖z‖ ‖x‖) ‖y‖
  have hz' := le_trans (le_max_left ‖z‖ ‖x‖) hz
  have hx' := le_trans (le_max_right ‖z‖ ‖x‖) hz
  have hne' : ∀ w : ℚ_[p], w = 0 → ‖z‖ ≤ ‖w‖ → ‖x‖ ≤ ‖w‖ → ‖y‖ ≤ ‖w‖ → False := by
    intro w hw0 h1 h2 h3
    rw [hw0, norm_zero, norm_le_zero_iff] at h1 h2 h3
    exact hne ⟨h1, h2, h3⟩
  rcases max_choice (max ‖z‖ ‖x‖) ‖y‖ with hm | hm <;>
    [rcases max_choice ‖z‖ ‖x‖ with hm' | hm'; skip] <;>
    rw [hm] at hz' hx' hy <;> (try rw [hm'] at hz' hx' hy)
  · obtain ⟨Z, X, Y, hZ, hZz, -, -⟩ := scale z hz' hx' hy
    refine ⟨Z, X, Y, hZ, Or.inl (PadicInt.ext ?_)⟩
    rw [hZz, PadicInt.coe_one, div_self fun h0 => hne' z h0 hz' hx' hy]
  · obtain ⟨Z, X, Y, hZ, -, hXx, -⟩ := scale x hz' hx' hy
    refine ⟨Z, X, Y, hZ, Or.inr (Or.inl (PadicInt.ext ?_))⟩
    rw [hXx, PadicInt.coe_one, div_self fun h0 => hne' x h0 hz' hx' hy]
  · obtain ⟨Z, X, Y, hZ, -, -, hYy⟩ := scale y hz' hx' hy
    refine ⟨Z, X, Y, hZ, Or.inr (Or.inr (PadicInt.ext ?_))⟩
    rw [hYy, PadicInt.coe_one, div_self fun h0 => hne' y h0 hz' hx' hy]

/-- A nontrivial zero over $\mathbb{Q}_2$, reduced modulo $8$. -/
private theorem exists_res_zero {A B : ℤ_[2]} (h : Iso (A : ℚ_[2]) (B : ℚ_[2])) :
    ∃ z x y : ZMod 8, z ^ 2 = PadicInt.toZModPow 3 A * x ^ 2 + PadicInt.toZModPow 3 B * y ^ 2 ∧
      (z = 1 ∨ x = 1 ∨ y = 1) := by
  obtain ⟨Z, X, Y, hZ, h1⟩ := exists_int_zero h
  refine ⟨PadicInt.toZModPow 3 Z, PadicInt.toZModPow 3 X, PadicInt.toZModPow 3 Y, ?_, ?_⟩
  · have := congrArg (PadicInt.toZModPow 3) hZ
    simpa only [map_add, map_mul, map_pow] using this
  · rcases h1 with h1 | h1 | h1 <;> simp [h1]

/-- The residue modulo `8` of `u` is `1`: then `u` is a square. -/
private theorem exists_sq_of_res_eq_one {w : ℤ_[2]} (hw : PadicInt.toZModPow 3 w = 1) :
    ∃ s : ℤ_[2], (w : ℚ_[2]) = (s : ℚ_[2]) ^ 2 := by
  obtain ⟨s, hs⟩ := PadicInt.isSquare_of_toZModPow_three_eq_one hw
  exact ⟨s, by rw [hs]; push_cast; ring⟩

/-- The case $(u, v)_2$. -/
private theorem iso_units_iff {u v : ℤ_[2]} (hu : OddRes (PadicInt.toZModPow 3 u))
    (hv : OddRes (PadicInt.toZModPow 3 v)) :
    Iso (u : ℚ_[2]) (v : ℚ_[2]) ↔
      (PadicInt.toZModPow 3 u = 1 ∨ PadicInt.toZModPow 3 u = 5 ∨
        PadicInt.toZModPow 3 v = 1 ∨ PadicInt.toZModPow 3 v = 5) := by
  have fin : ∀ r s : ZMod 8, OddRes r → OddRes s → ∀ z x y : ZMod 8,
      z ^ 2 = r * x ^ 2 + s * y ^ 2 → (z = 1 ∨ x = 1 ∨ y = 1) →
        (r = 1 ∨ r = 5 ∨ s = 1 ∨ s = 5) := by
    intro r s hr hs
    unfold OddRes at hr hs
    rcases hr with rfl | rfl | rfl | rfl <;> rcases hs with rfl | rfl | rfl | rfl <;> decide
  have five : ∀ r s : ZMod 8, r = 5 → OddRes s → r + 4 * s = 1 := by
    intro r s hr hs
    unfold OddRes at hs
    subst hr
    rcases hs with rfl | rfl | rfl | rfl <;> decide
  -- One unit with residue `1` or `5` makes the form isotropic.
  have pos : ∀ u v : ℤ_[2], OddRes (PadicInt.toZModPow 3 v) →
      (PadicInt.toZModPow 3 u = 1 ∨ PadicInt.toZModPow 3 u = 5) → Iso (u : ℚ_[2]) (v : ℚ_[2]) := by
    intro u v hv h
    rcases h with h | h
    · obtain ⟨s, hs⟩ := exists_sq_of_res_eq_one h
      exact ⟨s, 1, 0, fun h' => one_ne_zero h'.2.1, by rw [hs]; ring⟩
    · have hw : PadicInt.toZModPow 3 (u + 4 * v) = 1 := by
        rw [map_add, map_mul, map_ofNat]
        exact five _ _ h hv
      obtain ⟨s, hs⟩ := exists_sq_of_res_eq_one hw
      refine ⟨s, 1, 2, fun h' => one_ne_zero h'.2.1, ?_⟩
      rw [← hs, PadicInt.coe_add, PadicInt.coe_mul, coe_four]
      ring
  constructor
  · intro h
    obtain ⟨z, x, y, hz, h1⟩ := exists_res_zero h
    exact fin _ _ hu hv z x y hz h1
  · rintro (h | h | h | h)
    · exact pos u v hv (Or.inl h)
    · exact pos u v hv (Or.inr h)
    · exact iso_comm.1 (pos v u hu (Or.inl h))
    · exact iso_comm.1 (pos v u hu (Or.inr h))

/-- The case $(2u, v)_2$. -/
private theorem iso_two_mul_iff {u v : ℤ_[2]} (hu : OddRes (PadicInt.toZModPow 3 u))
    (hv : OddRes (PadicInt.toZModPow 3 v)) :
    Iso (2 * (u : ℚ_[2])) (v : ℚ_[2]) ↔
      (PadicInt.toZModPow 3 v = 1 ∨ PadicInt.toZModPow 3 v = 1 - 2 * PadicInt.toZModPow 3 u) := by
  have fin : ∀ r s : ZMod 8, OddRes r → OddRes s → ∀ z x y : ZMod 8,
      z ^ 2 = 2 * r * x ^ 2 + s * y ^ 2 → (z = 1 ∨ x = 1 ∨ y = 1) →
        (s = 1 ∨ s = 1 - 2 * r) := by
    intro r s hr hs
    unfold OddRes at hr hs
    rcases hr with rfl | rfl | rfl | rfl <;> rcases hs with rfl | rfl | rfl | rfl <;> decide
  constructor
  · intro h
    have h' : Iso (((2 * u : ℤ_[2])) : ℚ_[2]) (v : ℚ_[2]) := by
      rw [PadicInt.coe_mul, coe_two]
      exact h
    obtain ⟨z, x, y, hz, h1⟩ := exists_res_zero h'
    rw [map_mul, map_ofNat] at hz
    exact fin _ _ hu hv z x y hz h1
  · rintro (h | h)
    · obtain ⟨s, hs⟩ := exists_sq_of_res_eq_one h
      exact ⟨s, 0, 1, fun h' => one_ne_zero h'.2.2, by rw [hs]; ring⟩
    · have hw : PadicInt.toZModPow 3 (2 * u + v) = 1 := by
        rw [map_add, map_mul, map_ofNat, h]
        ring
      obtain ⟨s, hs⟩ := exists_sq_of_res_eq_one hw
      refine ⟨s, 1, 1, fun h' => one_ne_zero h'.2.1, ?_⟩
      rw [← hs, PadicInt.coe_add, PadicInt.coe_mul, coe_two]
      ring

/-- The case $(2u, 2v)_2$, through $(2u, 2v)_2 = (2u, -uv)_2$. -/
private theorem iso_two_mul_two_mul_iff {u v : ℤ_[2]} (hu : OddRes (PadicInt.toZModPow 3 u))
    (hv : OddRes (PadicInt.toZModPow 3 v)) :
    Iso (2 * (u : ℚ_[2])) (2 * (v : ℚ_[2])) ↔
      (-(PadicInt.toZModPow 3 u * PadicInt.toZModPow 3 v) = 1 ∨
        -(PadicInt.toZModPow 3 u * PadicInt.toZModPow 3 v) = 1 - 2 * PadicInt.toZModPow 3 u) := by
  have huv : OddRes (PadicInt.toZModPow 3 (-(u * v))) := by
    have key : ∀ r s : ZMod 8, OddRes r → OddRes s → OddRes (-(r * s)) := by
      intro r s hr hs
      unfold OddRes at hr hs ⊢
      rcases hr with rfl | rfl | rfl | rfl <;> rcases hs with rfl | rfl | rfl | rfl <;> decide
    rw [map_neg, map_mul]
    exact key _ _ hu hv
  have hu0 : (u : ℚ_[2]) ≠ 0 := by
    intro h0
    have : u = 0 := PadicInt.ext (h0.trans PadicInt.coe_zero.symm)
    rw [this, map_zero] at hu
    unfold OddRes at hu
    revert hu
    decide
  have h2u : 2 * (u : ℚ_[2]) ≠ 0 := mul_ne_zero two_ne_zero hu0
  rw [iso_neg_mul_iff h2u]
  have : -(2 * (u : ℚ_[2]) * (2 * (v : ℚ_[2]))) = ((-(u * v) : ℤ_[2]) : ℚ_[2]) * 2 ^ 2 := by
    rw [PadicInt.coe_neg, PadicInt.coe_mul]
    ring
  rw [this, iso_comm, iso_mul_sq two_ne_zero, iso_comm, iso_two_mul_iff hu huv, map_neg, map_mul]

/-- Reduction of the exponent modulo `2`. -/
private theorem zpow_two_eq_mul_sq (α : ℤ) :
    (2 : ℚ_[2]) ^ α = (2 : ℚ_[2]) ^ (α % 2) * ((2 : ℚ_[2]) ^ (α / 2)) ^ 2 := by
  rw [← zpow_natCast, ← zpow_mul, ← zpow_add₀ two_ne_zero]
  congr 1
  push_cast
  omega

private theorem iso_reduce (α β : ℤ) (u v : ℚ_[2]) :
    Iso ((2 : ℚ_[2]) ^ α * u) ((2 : ℚ_[2]) ^ β * v) ↔
      Iso ((2 : ℚ_[2]) ^ (α % 2) * u) ((2 : ℚ_[2]) ^ (β % 2) * v) := by
  have hα : (2 : ℚ_[2]) ^ α * u = (2 : ℚ_[2]) ^ (α % 2) * u * ((2 : ℚ_[2]) ^ (α / 2)) ^ 2 := by
    rw [zpow_two_eq_mul_sq α]; ring
  have hβ : (2 : ℚ_[2]) ^ β * v = (2 : ℚ_[2]) ^ (β % 2) * v * ((2 : ℚ_[2]) ^ (β / 2)) ^ 2 := by
    rw [zpow_two_eq_mul_sq β]; ring
  rw [hα, hβ, iso_mul_sq (zpow_ne_zero _ two_ne_zero), iso_comm,
    iso_mul_sq (zpow_ne_zero _ two_ne_zero), iso_comm]

/-- Only the parities of `i` and `j` matter. -/
private theorem even_add_mul_iff (x y z i j : ℕ) :
    Even (x + i * y + j * z) ↔ Even (x + (i % 2) * y + (j % 2) * z) := by
  have hi := Nat.div_add_mod i 2
  have hj := Nat.div_add_mod j 2
  have : x + i * y + j * z = (x + (i % 2) * y + (j % 2) * z) + 2 * ((i / 2) * y + (j / 2) * z) := by
    calc x + i * y + j * z = x + (2 * (i / 2) + i % 2) * y + (2 * (j / 2) + j % 2) * z := by
          rw [hi, hj]
      _ = _ := by ring
  rw [this, Nat.even_add, iff_true_right (even_two_mul _)]

private theorem natAbs_mod_two (α : ℤ) : α.natAbs % 2 = (α % 2).natAbs := by
  rcases Int.emod_two_eq α with h | h
  · rw [h, Nat.even_iff.1 (Int.natAbs_even.2 (Int.even_iff.2 h))]
    rfl
  · rw [h, Nat.odd_iff.1 (Int.natAbs_odd.2 (Int.odd_iff.2 h))]
    rfl

end HilbertSymbol

open HilbertSymbol

namespace padicHilbertSymbol

/-- **Formula for the $2$-adic Hilbert symbol.** Let $a, b \in \mathbb{Q}_2$ be nonzero, written
as $a = 2^\alpha u$ and $b = 2^\beta v$ with $\alpha, \beta \in \mathbb{Z}$ and $u, v$ units of
$\mathbb{Z}_2$. Then the $2$-adic Hilbert symbol satisfies

$$(a, b)_2 = (-1)^{\varepsilon(u)\varepsilon(v) + \alpha\omega(v) + \beta\omega(u)},$$

where $\varepsilon(u)$ and $\omega(u)$ are the classes modulo $2$ of $(u - 1)/2$ and
$(u^2 - 1)/8$.

Here $\varepsilon(u) = (\bar u - 1)/2$ and $\omega(u) = (\bar u^2 - 1)/8$ are computed as natural
numbers from the representative $\bar u \in \{0, \dots, 7\}$ of $u$ modulo $8$, which has the
same classes, and $\alpha, \beta$ are taken in absolute value, which leaves the sign unchanged.

Source: J.-P. Serre, *A Course in Arithmetic*, Graduate Texts in Mathematics 7, Springer, 1973,
Chapter III, §1.2, Theorem 1, p. 20 (the case $p = 2$). Serre defines $(a, b) = 1$ by a nonzero
zero of $z^2 - a x^2 - b y^2$; this agrees with the definition used here by
`hilbertSymbol.eq_one_iff_exists_ternary_eq_zero`. -/
theorem eq_formula_two (a b : ℚ_[2]ˣ) (α β : ℤ) (u v : ℤ_[2]ˣ)
    (ha : (a : ℚ_[2]) = (2 : ℚ_[2]) ^ α * ((u : ℤ_[2]) : ℚ_[2]))
    (hb : (b : ℚ_[2]) = (2 : ℚ_[2]) ^ β * ((v : ℤ_[2]) : ℚ_[2])) :
    padicHilbertSymbol 2 a b =
      (-1) ^ (((PadicInt.toZModPow 3 (u : ℤ_[2])).val - 1) / 2 *
            (((PadicInt.toZModPow 3 (v : ℤ_[2])).val - 1) / 2) +
          α.natAbs * (((PadicInt.toZModPow 3 (v : ℤ_[2])).val ^ 2 - 1) / 8) +
          β.natAbs * (((PadicInt.toZModPow 3 (u : ℤ_[2])).val ^ 2 - 1) / 8)) := by
  have hu := oddRes_of_isUnit u.isUnit
  have hv := oddRes_of_isUnit v.isUnit
  set ru : ZMod 8 := PadicInt.toZModPow 3 (u : ℤ_[2]) with hru
  set rv : ZMod 8 := PadicInt.toZModPow 3 (v : ℤ_[2]) with hrv
  -- The symbol through the ternary form.
  have hval : padicHilbertSymbol 2 a b = 1 ↔ Iso (a : ℚ_[2]) (b : ℚ_[2]) :=
    hilbertSymbol.eq_one_iff_exists_ternary_eq_zero two_ne_zero a b
  -- The value of the ternary condition.
  have hE : Iso (a : ℚ_[2]) (b : ℚ_[2]) ↔
      Even ((ru.val - 1) / 2 * ((rv.val - 1) / 2) + α.natAbs * ((rv.val ^ 2 - 1) / 8) +
        β.natAbs * ((ru.val ^ 2 - 1) / 8)) := by
    rw [ha, hb, iso_reduce, even_add_mul_iff, natAbs_mod_two, natAbs_mod_two]
    rcases Int.emod_two_eq α with hα | hα <;> rcases Int.emod_two_eq β with hβ | hβ <;>
      simp only [hα, hβ, zpow_zero, zpow_one, one_mul, Int.natAbs_zero, Int.natAbs_one]
    · rw [iso_units_iff hu hv]
      rw [← hru, ← hrv]
      clear_value ru rv
      unfold OddRes at hu hv
      rcases hu with rfl | rfl | rfl | rfl <;> rcases hv with rfl | rfl | rfl | rfl <;> decide
    · rw [iso_comm, iso_two_mul_iff hv hu]
      rw [← hru, ← hrv]
      clear_value ru rv
      unfold OddRes at hu hv
      rcases hu with rfl | rfl | rfl | rfl <;> rcases hv with rfl | rfl | rfl | rfl <;> decide
    · rw [iso_two_mul_iff hu hv]
      rw [← hru, ← hrv]
      clear_value ru rv
      unfold OddRes at hu hv
      rcases hu with rfl | rfl | rfl | rfl <;> rcases hv with rfl | rfl | rfl | rfl <;> decide
    · rw [iso_two_mul_two_mul_iff hu hv]
      rw [← hru, ← hrv]
      clear_value ru rv
      unfold OddRes at hu hv
      rcases hu with rfl | rfl | rfl | rfl <;> rcases hv with rfl | rfl | rfl | rfl <;> decide
  rcases Nat.even_or_odd ((ru.val - 1) / 2 * ((rv.val - 1) / 2) +
      α.natAbs * ((rv.val ^ 2 - 1) / 8) + β.natAbs * ((ru.val ^ 2 - 1) / 8)) with he | ho
  · rw [he.neg_one_pow]
    exact hval.2 (hE.2 he)
  · rw [ho.neg_one_pow]
    rcases padicHilbertSymbol.eq_one_or_neg_one a b with h | h
    · exact absurd (hE.1 (hval.1 h)) (Nat.not_even_iff_odd.2 ho)
    · exact h

end padicHilbertSymbol
