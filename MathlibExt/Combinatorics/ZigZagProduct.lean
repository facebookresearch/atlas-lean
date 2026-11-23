/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.RotationMap

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The zig-zag theorem

O. Reingold, S. Vadhan and A. Wigderson, *Entropy waves, the zig-zag graph product, and new
constant-degree expanders*, Ann. of Math. 155 (2002), Theorem 3.2: if `G` is an
`(N₁, D₁, λ₁)`-graph and `H` a `(D₁, D₂, λ₂)`-graph, then the zig-zag product `G ⓩ H` is an
`(N₁ D₁, D₂², λ₁ + λ₂ + λ₂²)`-graph. The proof is the basic analysis of their Section 4.1: the
normalised adjacency matrix of `G ⓩ H` factors as `B̃ Ã B̃`, where `B̃` applies `H` inside each
cloud `{v} × [D₁]` and `Ã` is the permutation given by the rotation map of `G`. A vector `x`
orthogonal to the constants splits as `x = x^∥ + x^⊥`, with `x^∥` constant on clouds and `x^⊥`
summing to zero on each cloud; `B̃` fixes `x^∥` and shrinks `x^⊥` by `λ₂`, and `Ã` acts on `x^∥`
as `G` acts on the cloud averages, shrinking it by `λ₁`. This bounds the quadratic form
`|⟨M x, x⟩| ≤ (λ₁ + λ₂ + λ₂²) ‖x‖²`, and a polarization argument
(`isSpectralBound_of_abs_dotProduct_le`) converts it into the norm form used by
`IsNDLambdaGraph` (Reingold, Vadhan and Wigderson, Definition 2.2, states the two forms as
equivalent).
-/

@[expose] public section

open Finset Matrix

namespace MathlibExt.Combinatorics.RotationMap

open MathlibExt.Combinatorics.SpectralExpander

private lemma dot_self_nonneg' {ι : Type*} [Fintype ι] (x : ι → ℝ) : 0 ≤ x ⬝ᵥ x := by
  unfold dotProduct
  exact Finset.sum_nonneg fun i _ => mul_self_nonneg (x i)

private lemma abs_dot_le {ι : Type*} [Fintype ι] (x y : ι → ℝ) :
    |x ⬝ᵥ y| ≤ √(x ⬝ᵥ x) * √(y ⬝ᵥ y) := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ x y
  have h' : (x ⬝ᵥ y) ^ 2 ≤ (x ⬝ᵥ x) * (y ⬝ᵥ y) := by simpa [dotProduct, sq] using h
  rw [← Real.sqrt_mul (dot_self_nonneg' x)]
  exact Real.abs_le_sqrt h'

/-- **Norm bound from a quadratic-form bound.** Let `A` be a symmetric real matrix that maps
vectors with zero sum to vectors with zero sum, and suppose `|xᵀ A x| ≤ c xᵀ x` for every `x`
with zero sum, where `c ≥ 0`. Then `‖A x‖ ≤ c ‖x‖` for every such `x`: the variational
characterisations `max |⟨α, M α⟩| / ⟨α, α⟩` and `max ‖M α‖ / ‖α‖` over `α ⊥ 1` agree
(O. Reingold, S. Vadhan and A. Wigderson, Ann. of Math. 155 (2002), Definition 2.2). The proof
polarizes: `4 t ‖A x‖² ≤ c (‖A x + t x‖² + ‖A x - t x‖²)`, with `t = c` (or `t = 1` if
`c = 0`). -/
theorem isSpectralBound_of_abs_dotProduct_le {ι : Type*} [Fintype ι] {A : Matrix ι ι ℝ}
    (hA : Aᵀ = A) (hpres : ∀ x : ι → ℝ, ∑ i, x i = 0 → ∑ i, (A *ᵥ x) i = 0) {c : ℝ}
    (hc : 0 ≤ c) (hq : ∀ x : ι → ℝ, ∑ i, x i = 0 → |x ⬝ᵥ (A *ᵥ x)| ≤ c * (x ⬝ᵥ x)) :
    IsSpectralBound A c := by
  intro x hx
  set y := A *ᵥ x with hy
  have hys : ∑ i, y i = 0 := hpres x hx
  have hsym : ∀ a b : ι → ℝ, a ⬝ᵥ (A *ᵥ b) = b ⬝ᵥ (A *ᵥ a) := fun a b => by
    rw [dotProduct_mulVec, ← mulVec_transpose, hA, dotProduct_comm]
  have hsum : ∀ (t : ℝ) (s : ℝ), ∑ i, (y + (s * t) • x) i = 0 := fun t s => by
    simp [Finset.sum_add_distrib, ← Finset.mul_sum, hys, hx]
  -- For every `t`, `4 t ‖y‖² ≤ 2 c (‖y‖² + t² ‖x‖²)`.
  have key : ∀ t : ℝ, 4 * t * (y ⬝ᵥ y) ≤ 2 * c * ((y ⬝ᵥ y) + t ^ 2 * (x ⬝ᵥ x)) := by
    intro t
    have hu := hq (y + (1 * t) • x) (hsum t 1)
    have hw := hq (y + ((-1) * t) • x) (hsum t (-1))
    have hyx : y ⬝ᵥ (A *ᵥ x) = y ⬝ᵥ y := by rw [hy]
    have hxy : x ⬝ᵥ (A *ᵥ y) = y ⬝ᵥ y := by rw [hsym, hyx]
    simp only [mulVec_add, mulVec_smul, dotProduct_add, add_dotProduct, dotProduct_smul,
      smul_dotProduct, smul_eq_mul, hyx, hxy, dotProduct_comm x y] at hu hw
    have hu' := (abs_le.mp hu).2
    have hw' := (abs_le.mp hw).1
    nlinarith
  rcases hc.lt_or_eq with hc0 | hc0
  · have := key c
    have : c * (y ⬝ᵥ y) ≤ c * (c ^ 2 * (x ⬝ᵥ x)) := by nlinarith
    exact le_of_mul_le_mul_left this hc0
  · have := key 1
    rw [← hc0] at this ⊢
    nlinarith [dot_self_nonneg' y]

variable {V K L : Type*} [Fintype V] [Fintype K] [Fintype L] [DecidableEq V] [DecidableEq K]

/-- The rows-sum-to-degree identity in summed form: `∑ (A x) = |L| ∑ x`. -/
private lemma sum_adjMatrix_mulVec {W : Type*} [Fintype W] [DecidableEq W] (G : RotationMap W L)
    (x : W → ℝ) : ∑ i, (G.adjMatrix *ᵥ x) i = Fintype.card L * ∑ i, x i := by
  have : ∑ i, (G.adjMatrix *ᵥ x) i = (1 : W → ℝ) ⬝ᵥ (G.adjMatrix *ᵥ x) := by
    simp [dotProduct]
  rw [this, dotProduct_mulVec, ← mulVec_transpose, adjMatrix_transpose, adjMatrix_mulVec_one,
    smul_dotProduct, one_dotProduct, smul_eq_mul]


/-- `B̃`: apply the adjacency operator of `H` inside every cloud `{v} × K`. -/
private noncomputable def cloudOp (H : RotationMap K L) (z : V × K → ℝ) : V × K → ℝ :=
  fun p => ∑ i, z (p.1, (H.rot (p.2, i)).1)

/-- `Ã`: the permutation of `V × K` given by the rotation map of `G`. -/
private def rotOp (G : RotationMap V K) (z : V × K → ℝ) : V × K → ℝ :=
  fun p => z (G.rot p)

private lemma zigzag_mulVec (G : RotationMap V K) (H : RotationMap K L) (z : V × K → ℝ) :
    (G.zigzag H).adjMatrix *ᵥ z = cloudOp H (rotOp G (cloudOp H z)) := by
  funext p
  rw [adjMatrix_mulVec_apply, Fintype.sum_prod_type]
  rfl

omit [Fintype V] [DecidableEq V] in
private lemma cloudOp_eq (H : RotationMap K L) (z : V × K → ℝ) (v : V) (k : K) :
    cloudOp H z (v, k) = (H.adjMatrix *ᵥ fun k' => z (v, k')) k := by
  rw [adjMatrix_mulVec_apply]; rfl

omit [DecidableEq V] [DecidableEq K] in
private lemma dot_cloudOp_comm (H : RotationMap K L) (u w : V × K → ℝ) :
    u ⬝ᵥ cloudOp H w = cloudOp H u ⬝ᵥ w := by
  classical
  have key : ∀ a b : K → ℝ, a ⬝ᵥ (H.adjMatrix *ᵥ b) = (H.adjMatrix *ᵥ a) ⬝ᵥ b := fun a b => by
    rw [dotProduct_mulVec, ← mulVec_transpose, adjMatrix_transpose]
  simp only [dotProduct, Fintype.sum_prod_type, cloudOp_eq]
  refine Finset.sum_congr rfl fun v _ => ?_
  simpa [dotProduct] using key (fun k => u (v, k)) (fun k => w (v, k))

/-- The rotation map of `G` as a permutation of `V × K`. -/
private def rotPerm (G : RotationMap V K) : Equiv.Perm (V × K) :=
  ⟨G.rot, G.rot, G.rot_rot, G.rot_rot⟩

omit [DecidableEq V] [DecidableEq K] in
private lemma dot_rotOp_comm (G : RotationMap V K) (u w : V × K → ℝ) :
    u ⬝ᵥ rotOp G w = rotOp G u ⬝ᵥ w := by
  simp only [dotProduct, rotOp]
  rw [← Equiv.sum_comp (rotPerm G)]
  change ∑ i, u (G.rot i) * w (G.rot (G.rot i)) = _
  simp only [G.rot_rot]

omit [DecidableEq V] [DecidableEq K] in
private lemma dot_rotOp_self (G : RotationMap V K) (w : V × K → ℝ) :
    rotOp G w ⬝ᵥ rotOp G w = w ⬝ᵥ w := by
  simp only [dotProduct, rotOp]
  exact Equiv.sum_comp (rotPerm G) (fun p => w p * w p)

omit [Fintype V] [Fintype K] [DecidableEq V] [DecidableEq K] in
private lemma cloudOp_add (H : RotationMap K L) (u w : V × K → ℝ) :
    cloudOp H (u + w) = cloudOp H u + cloudOp H w := by
  funext p; simp [cloudOp, Finset.sum_add_distrib]

omit [DecidableEq V] in
private lemma cloudOp_bound (H : RotationMap K L) {lam₂ : ℝ} (hH : H.IsNDLambdaGraph lam₂)
    (z : V × K → ℝ) (hz : ∀ v, ∑ k, z (v, k) = 0) :
    cloudOp H z ⬝ᵥ cloudOp H z ≤ ((Fintype.card L : ℝ) * lam₂) ^ 2 * (z ⬝ᵥ z) := by
  simp only [dotProduct, Fintype.sum_prod_type, cloudOp_eq, Finset.mul_sum]
  refine Finset.sum_le_sum fun v _ => ?_
  have := hH.2 (fun k => z (v, k)) (hz v)
  simpa [dotProduct, Finset.mul_sum] using this


/-- The scalar inequality closing the zig-zag estimate:
`D₂² λ₁ P² + 2 D₂ P R + R² ≤ D₂² (λ₁ + λ₂ + λ₂²)(P² + Q²)` when `R ≤ D₂ λ₂ Q`. -/
private lemma zigzag_arith {D2 lam₁ lam₂ P Q R T1 T2 T3 T4 : ℝ} (hD20 : 0 ≤ D2) (h1 : 0 ≤ lam₁)
    (h2 : 0 ≤ lam₂) (hP0 : 0 ≤ P) (hQ0 : 0 ≤ Q) (hR0 : 0 ≤ R) (hRQ : R ≤ D2 * lam₂ * Q)
    (hT1 : |T1| ≤ lam₁ * P ^ 2) (hT2 : |T2| ≤ P * R) (hT3 : |T3| ≤ R * P)
    (hT4 : |T4| ≤ R * R) :
    |D2 ^ 2 * T1 + D2 * T2 + D2 * T3 + T4| ≤
      D2 ^ 2 * (lam₁ + lam₂ + lam₂ ^ 2) * (P ^ 2 + Q ^ 2) := by
  obtain ⟨a1, b1⟩ := abs_le.mp hT1
  obtain ⟨a2, b2⟩ := abs_le.mp hT2
  obtain ⟨a3, b3⟩ := abs_le.mp hT3
  obtain ⟨a4, b4⟩ := abs_le.mp hT4
  have hD2sq : 0 ≤ D2 ^ 2 := sq_nonneg _
  have hB : |D2 ^ 2 * T1 + D2 * T2 + D2 * T3 + T4| ≤
      D2 ^ 2 * (lam₁ * P ^ 2) + 2 * D2 * (P * R) + R * R := by
    rw [abs_le]
    constructor
    · nlinarith [mul_le_mul_of_nonneg_left a1 hD2sq, mul_le_mul_of_nonneg_left a2 hD20,
        mul_le_mul_of_nonneg_left a3 hD20]
    · nlinarith [mul_le_mul_of_nonneg_left b1 hD2sq, mul_le_mul_of_nonneg_left b2 hD20,
        mul_le_mul_of_nonneg_left b3 hD20]
  refine hB.trans ?_
  have hDR : D2 * R ≤ D2 * (D2 * lam₂ * Q) := mul_le_mul_of_nonneg_left hRQ hD20
  have hRR' : R * R ≤ (D2 * lam₂ * Q) * (D2 * lam₂ * Q) :=
    mul_le_mul hRQ hRQ hR0 (by positivity)
  have hPQ : 2 * P * Q ≤ P ^ 2 + Q ^ 2 := two_mul_le_add_sq P Q
  have hDRP := mul_le_mul_of_nonneg_left hDR (by positivity : 0 ≤ 2 * P)
  have step1 : D2 ^ 2 * (lam₁ * P ^ 2) + 2 * D2 * (P * R) + R * R ≤
      D2 ^ 2 * (lam₁ * P ^ 2 + lam₂ * (2 * P * Q) + lam₂ ^ 2 * Q ^ 2) := by
    have e1 : 2 * D2 * (P * R) = 2 * P * (D2 * R) := by ring
    have e2 : 2 * P * (D2 * (D2 * lam₂ * Q)) = D2 ^ 2 * (lam₂ * (2 * P * Q)) := by ring
    have e3 : (D2 * lam₂ * Q) * (D2 * lam₂ * Q) = D2 ^ 2 * (lam₂ ^ 2 * Q ^ 2) := by ring
    rw [e1]
    linarith
  refine step1.trans ?_
  have step2 : lam₁ * P ^ 2 + lam₂ * (2 * P * Q) + lam₂ ^ 2 * Q ^ 2 ≤
      (lam₁ + lam₂ + lam₂ ^ 2) * (P ^ 2 + Q ^ 2) := by
    have := mul_le_mul_of_nonneg_left hPQ h2
    nlinarith [mul_nonneg h1 (sq_nonneg Q), mul_nonneg (sq_nonneg lam₂) (sq_nonneg P)]
  calc _ ≤ D2 ^ 2 * ((lam₁ + lam₂ + lam₂ ^ 2) * (P ^ 2 + Q ^ 2)) :=
        mul_le_mul_of_nonneg_left step2 hD2sq
    _ = _ := by ring

/-- The decomposition behind both zig-zag bounds: `B̃ x = D₂ x^∥ + y` with `x^∥ ⊥ y`,
`‖x‖² = ‖x^∥‖² + ‖x^⊥‖²`, `|⟨Ã x^∥, x^∥⟩| ≤ λ₁ ‖x^∥‖²` and `‖y‖ ≤ D₂ λ₂ ‖x^⊥‖`. -/
private lemma zigzag_core {G : RotationMap V K} {H : RotationMap K L} {lam₁ lam₂ : ℝ}
    (hG : G.IsNDLambdaGraph lam₁) (hH : H.IsNDLambdaGraph lam₂) [Nonempty K] (x : V × K → ℝ)
    (hx : ∑ i, x i = 0) :
    ∃ xpar xperp y : V × K → ℝ,
      cloudOp H x = (Fintype.card L : ℝ) • xpar + y ∧
      x ⬝ᵥ x = xpar ⬝ᵥ xpar + xperp ⬝ᵥ xperp ∧ xpar ⬝ᵥ y = 0 ∧
      |xpar ⬝ᵥ rotOp G xpar| ≤ lam₁ * (xpar ⬝ᵥ xpar) ∧
      y ⬝ᵥ y ≤ ((Fintype.card L : ℝ) * lam₂) ^ 2 * (xperp ⬝ᵥ xperp) := by
  obtain ⟨h1, hbG⟩ := hG
  obtain ⟨h2, hbH⟩ := hH
  set D1 : ℝ := (Fintype.card K : ℝ) with hD1
  set D2 : ℝ := (Fintype.card L : ℝ) with hD2
  have hD1pos : 0 < D1 := by simp only [hD1]; exact_mod_cast Fintype.card_pos
  -- Cloud averages and the decomposition `x = x^∥ + x^⊥`.
  set a : V → ℝ := fun v => (∑ k, x (v, k)) / D1 with ha
  set xpar : V × K → ℝ := fun p => a p.1 with hxpar
  set xperp : V × K → ℝ := x - xpar with hxperp
  have hdecomp : x = xpar + xperp := by simp [hxperp]
  have hcloud : ∀ v, ∑ k, xperp (v, k) = 0 := by
    intro v
    simp only [hxperp, hxpar, ha, Pi.sub_apply, Finset.sum_sub_distrib, Finset.sum_const,
      Finset.card_univ, nsmul_eq_mul, ← hD1]
    field_simp
    ring
  have hasum : ∑ v, a v = 0 := by
    simp only [ha, ← Finset.sum_div]
    rw [← Fintype.sum_prod_type' (fun v k => x (v, k))]
    simp [hx]
  have hparpar : xpar ⬝ᵥ xpar = D1 * (a ⬝ᵥ a) := by
    simp only [dotProduct, hxpar, Fintype.sum_prod_type, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul, ← hD1, Finset.mul_sum]
  have horth : xpar ⬝ᵥ xperp = 0 := by
    simp only [dotProduct, Fintype.sum_prod_type, hxpar]
    refine Finset.sum_eq_zero fun v _ => ?_
    rw [← Finset.mul_sum, hcloud v, mul_zero]
  have hxx : x ⬝ᵥ x = xpar ⬝ᵥ xpar + xperp ⬝ᵥ xperp := by
    rw [hdecomp, add_dotProduct, dotProduct_add, dotProduct_add, horth, dotProduct_comm xperp xpar,
      horth]
    ring
  -- `B̃ x = D₂ x^∥ + B̃ x^⊥`.
  have hBpar : cloudOp H xpar = D2 • xpar := by
    funext p; simp [cloudOp, hxpar, hD2]
  set y := cloudOp H xperp with hy
  have hBx : cloudOp H x = D2 • xpar + y := by
    conv_lhs => rw [hdecomp]
    rw [cloudOp_add, hBpar]
  have hyy : y ⬝ᵥ y ≤ (D2 * lam₂) ^ 2 * (xperp ⬝ᵥ xperp) := cloudOp_bound H ⟨h2, hbH⟩ xperp hcloud
  -- `Ã` acts on `x^∥` through `G`.
  have hPpar : |xpar ⬝ᵥ rotOp G xpar| ≤ lam₁ * (xpar ⬝ᵥ xpar) := by
    have he : xpar ⬝ᵥ rotOp G xpar = a ⬝ᵥ (G.adjMatrix *ᵥ a) := by
      simp only [dotProduct, Fintype.sum_prod_type, hxpar, rotOp, adjMatrix_mulVec_apply,
        Finset.mul_sum]
    rw [he, hparpar]
    have hb := hbG a hasum
    calc |a ⬝ᵥ (G.adjMatrix *ᵥ a)| ≤ √(a ⬝ᵥ a) * √((G.adjMatrix *ᵥ a) ⬝ᵥ (G.adjMatrix *ᵥ a)) :=
          abs_dot_le _ _
      _ ≤ √(a ⬝ᵥ a) * √((D1 * lam₁) ^ 2 * (a ⬝ᵥ a)) :=
          mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hb) (Real.sqrt_nonneg _)
      _ = lam₁ * (D1 * (a ⬝ᵥ a)) := by
          rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (by positivity),
            show √(a ⬝ᵥ a) * (D1 * lam₁ * √(a ⬝ᵥ a)) = D1 * lam₁ * (√(a ⬝ᵥ a) * √(a ⬝ᵥ a)) by ring,
            Real.mul_self_sqrt (dot_self_nonneg' a)]
          ring
  have hypar : xpar ⬝ᵥ y = 0 := by
    simp only [dotProduct, Fintype.sum_prod_type, hxpar, hy, cloudOp_eq]
    refine Finset.sum_eq_zero fun v _ => ?_
    rw [← Finset.mul_sum, sum_adjMatrix_mulVec, hcloud v, mul_zero, mul_zero]
  exact ⟨xpar, xperp, y, hBx, hxx, hypar, hPpar, hyy⟩


/-- The scalar inequality closing the spectral-gap form of the zig-zag estimate. -/
private lemma zigzag_gap_arith {D2 lam₁ lam₂ c P S F T1 T2 T3 T4 : ℝ} (hD20 : 0 ≤ D2)
    (h1 : 0 ≤ lam₁) (h2 : 0 ≤ lam₂) (h₂ : lam₂ ≤ 1) (hc : c = D2 * (1 - lam₂))
    (hP0 : 0 ≤ P) (hF0 : 0 ≤ F) (hPS : P ≤ S) (hFS : F ≤ D2 * lam₂ * S)
    (hT1 : |T1| ≤ lam₁ * P ^ 2) (hT2 : |T2| ≤ P * F) (hT3 : |T3| ≤ F * P)
    (hT4 : |T4| ≤ F * F) :
    |c ^ 2 * T1 + c * T2 + c * T3 + T4| ≤
      D2 ^ 2 * (1 - (1 - lam₁) * (1 - lam₂) ^ 2) * S ^ 2 := by
  have hc0 : 0 ≤ c := by rw [hc]; exact mul_nonneg hD20 (by linarith)
  obtain ⟨a1, b1⟩ := abs_le.mp hT1
  obtain ⟨a2, b2⟩ := abs_le.mp hT2
  obtain ⟨a3, b3⟩ := abs_le.mp hT3
  obtain ⟨a4, b4⟩ := abs_le.mp hT4
  have hc2 : 0 ≤ c ^ 2 := sq_nonneg _
  have hB : |c ^ 2 * T1 + c * T2 + c * T3 + T4| ≤
      c ^ 2 * (lam₁ * P ^ 2) + 2 * c * (P * F) + F * F := by
    rw [abs_le]
    constructor
    · nlinarith [mul_le_mul_of_nonneg_left a1 hc2, mul_le_mul_of_nonneg_left a2 hc0,
        mul_le_mul_of_nonneg_left a3 hc0]
    · nlinarith [mul_le_mul_of_nonneg_left b1 hc2, mul_le_mul_of_nonneg_left b2 hc0,
        mul_le_mul_of_nonneg_left b3 hc0]
  refine hB.trans ?_
  have hS0 : 0 ≤ S := hP0.trans hPS
  have e1 : c ^ 2 * (lam₁ * P ^ 2) ≤ c ^ 2 * (lam₁ * S ^ 2) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hP0 hPS 2) h1) hc2
  have e2 : 2 * c * (P * F) ≤ 2 * c * (S * (D2 * lam₂ * S)) :=
    mul_le_mul_of_nonneg_left (mul_le_mul hPS hFS hF0 hS0) (by positivity)
  have e3 : F * F ≤ (D2 * lam₂ * S) * (D2 * lam₂ * S) := mul_le_mul hFS hFS hF0 (by positivity)
  have e4 : c ^ 2 * (lam₁ * S ^ 2) + 2 * c * (S * (D2 * lam₂ * S)) +
      (D2 * lam₂ * S) * (D2 * lam₂ * S) = D2 ^ 2 * (1 - (1 - lam₁) * (1 - lam₂) ^ 2) * S ^ 2 := by
    rw [hc]; ring
  linarith
/-- **Zig-zag theorem.** If the rotation map `G` describes an `(N₁, D₁, λ₁)`-graph and the
rotation map `H` on `D₁` vertices describes a `(D₁, D₂, λ₂)`-graph, then their zig-zag product is
an `(N₁ D₁, D₂², λ₁ + λ₂ + λ₂²)`-graph (O. Reingold, S. Vadhan and A. Wigderson, Ann. of Math. 155
(2002), Theorem 3.2, the bound `f(λ₁, λ₂) ≤ λ₁ + λ₂ + λ₂²`, proved in their Section 4.1; see also
Theorem 1.3). This is the basic analysis; the tighter bound of their Theorem 4.3 is not formalized.
-/
theorem IsNDLambdaGraph.zigzag {G : RotationMap V K} {H : RotationMap K L} {lam₁ lam₂ : ℝ}
    (hG : G.IsNDLambdaGraph lam₁) (hH : H.IsNDLambdaGraph lam₂) :
    (G.zigzag H).IsNDLambdaGraph (lam₁ + lam₂ + lam₂ ^ 2) := by
  have h1 := hG.1
  have h2 := hH.1
  set D2 : ℝ := (Fintype.card L : ℝ) with hD2
  have hcard : (Fintype.card (L × L) : ℝ) = D2 ^ 2 := by simp [Fintype.card_prod, sq, hD2]
  refine ⟨by positivity, ?_⟩
  rw [hcard]
  refine isSpectralBound_of_abs_dotProduct_le (adjMatrix_transpose _)
    (fun x hx => by rw [sum_adjMatrix_mulVec, hx, mul_zero]) (by positivity) ?_
  intro x hx
  rcases isEmpty_or_nonempty K with hK | hK
  · have : x ⬝ᵥ ((G.zigzag H).adjMatrix *ᵥ x) = 0 := by simp [dotProduct]
    rw [this, abs_zero]
    exact mul_nonneg (by positivity) (dot_self_nonneg' x)
  obtain ⟨xpar, xperp, y, hBx, hxx, -, hPpar, hyy⟩ := zigzag_core hG hH x hx
  have hrot_add : ∀ u w : V × K → ℝ, rotOp G (u + w) = rotOp G u + rotOp G w := fun u w => rfl
  have hrot_smul : ∀ (c : ℝ) (u : V × K → ℝ), rotOp G (c • u) = c • rotOp G u := fun c u => rfl
  have hexp : x ⬝ᵥ ((G.zigzag H).adjMatrix *ᵥ x) =
      D2 ^ 2 * (xpar ⬝ᵥ rotOp G xpar) + D2 * (xpar ⬝ᵥ rotOp G y) + D2 * (y ⬝ᵥ rotOp G xpar) +
        y ⬝ᵥ rotOp G y := by
    rw [zigzag_mulVec, dot_cloudOp_comm, hBx, hrot_add, hrot_smul]
    simp only [add_dotProduct, dotProduct_add, smul_dotProduct, dotProduct_smul, smul_eq_mul]
    ring
  set P := √(xpar ⬝ᵥ xpar)
  set Q := √(xperp ⬝ᵥ xperp)
  set R := √(y ⬝ᵥ y)
  have hP0 : 0 ≤ P := Real.sqrt_nonneg _
  have hQ0 : 0 ≤ Q := Real.sqrt_nonneg _
  have hR0 : 0 ≤ R := Real.sqrt_nonneg _
  have hPP : P ^ 2 = xpar ⬝ᵥ xpar := Real.sq_sqrt (dot_self_nonneg' _)
  have hQQ : Q ^ 2 = xperp ⬝ᵥ xperp := Real.sq_sqrt (dot_self_nonneg' _)
  have hRR : R ^ 2 = y ⬝ᵥ y := Real.sq_sqrt (dot_self_nonneg' _)
  have hRQ : R ≤ D2 * lam₂ * Q :=
    calc R ≤ √((D2 * lam₂) ^ 2 * (xperp ⬝ᵥ xperp)) := Real.sqrt_le_sqrt hyy
      _ = D2 * lam₂ * Q := by rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (by positivity)]
  have hT1 : |xpar ⬝ᵥ rotOp G xpar| ≤ lam₁ * P ^ 2 := by rw [hPP]; exact hPpar
  have hT2 : |xpar ⬝ᵥ rotOp G y| ≤ P * R := by
    have := abs_dot_le xpar (rotOp G y); rwa [dot_rotOp_self] at this
  have hT3 : |y ⬝ᵥ rotOp G xpar| ≤ R * P := by
    have := abs_dot_le y (rotOp G xpar); rwa [dot_rotOp_self] at this
  have hT4 : |y ⬝ᵥ rotOp G y| ≤ R * R := by
    have := abs_dot_le y (rotOp G y); rwa [dot_rotOp_self] at this
  rw [hexp, hxx, ← hPP, ← hQQ]
  exact zigzag_arith (by positivity) h1 h2 hP0 hQ0 hR0 hRQ hT1 hT2 hT3 hT4

/-- **Zig-zag theorem, spectral-gap form.** If the rotation map `G` describes an
`(N₁, D₁, λ₁)`-graph and `H` a `(D₁, D₂, λ₂)`-graph with `λ₂ ≤ 1`, then the zig-zag product
has spectral gap at least the product of the gap of `G` and the square of the gap of `H`:
it is an `(N₁ D₁, D₂², 1 - (1 - λ₁)(1 - λ₂)²)`-graph; in particular `λ ≤ λ₁ + 2 λ₂`, and `λ < 1`
when `λ₁, λ₂ < 1` (S. Vadhan, *Pseudorandomness*, Foundations and Trends in Theoretical Computer
Science 7 (2012), Theorem 4.35, with `γᵢ = 1 - λᵢ`, where spectral gaps lie in `[0, 1]`; the
source's restriction `λ₁ ≤ 1` is not needed for the bound; compare O. Reingold, S. Vadhan and
A. Wigderson, Ann. of Math. 155 (2002), Theorem 3.2, `f(λ₁, λ₂) < 1` when `λ₁, λ₂ < 1`). The proof
is Vadhan's matrix decomposition `B̃ = (1 - λ₂) J̃ + λ₂ Ẽ` applied to `x`: `B̃ x = (1 - λ₂) x^∥ + f`
with `‖f‖ ≤ λ₂ ‖x‖` (unnormalised here, with the factor `D₂`). -/
theorem IsNDLambdaGraph.zigzag_gap {G : RotationMap V K} {H : RotationMap K L} {lam₁ lam₂ : ℝ}
    (hG : G.IsNDLambdaGraph lam₁) (hH : H.IsNDLambdaGraph lam₂) (h₂ : lam₂ ≤ 1) :
    (G.zigzag H).IsNDLambdaGraph (1 - (1 - lam₁) * (1 - lam₂) ^ 2) := by
  have h1 := hG.1
  have h2 := hH.1
  set D2 : ℝ := (Fintype.card L : ℝ) with hD2
  have hcard : (Fintype.card (L × L) : ℝ) = D2 ^ 2 := by simp [Fintype.card_prod, sq, hD2]
  have hlam0 : 0 ≤ 1 - (1 - lam₁) * (1 - lam₂) ^ 2 := by
    have : (1 - lam₁) * (1 - lam₂) ^ 2 ≤ 1 := by
      have a : (1 - lam₂) ^ 2 ≤ 1 := by nlinarith
      calc (1 - lam₁) * (1 - lam₂) ^ 2 ≤ 1 * 1 :=
            mul_le_mul (by linarith) a (sq_nonneg _) zero_le_one
        _ = 1 := by ring
    linarith
  refine ⟨hlam0, ?_⟩
  rw [hcard]
  refine isSpectralBound_of_abs_dotProduct_le (adjMatrix_transpose _)
    (fun x hx => by rw [sum_adjMatrix_mulVec, hx, mul_zero]) (by positivity) ?_
  intro x hx
  rcases isEmpty_or_nonempty K with hK | hK
  · have : x ⬝ᵥ ((G.zigzag H).adjMatrix *ᵥ x) = 0 := by simp [dotProduct]
    rw [this, abs_zero]
    exact mul_nonneg (by positivity) (dot_self_nonneg' x)
  obtain ⟨xpar, xperp, y, hBx, hxx, hypar, hPpar, hyy⟩ := zigzag_core hG hH x hx
  set c : ℝ := D2 * (1 - lam₂) with hc
  set f : V × K → ℝ := (D2 * lam₂) • xpar + y with hf
  have hBx' : cloudOp H x = c • xpar + f := by
    rw [hBx, hf, hc]; funext p; simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
  have hff : f ⬝ᵥ f ≤ (D2 * lam₂) ^ 2 * (x ⬝ᵥ x) := by
    have e : f ⬝ᵥ f = (D2 * lam₂) ^ 2 * (xpar ⬝ᵥ xpar) + 2 * (D2 * lam₂) * (xpar ⬝ᵥ y) +
        y ⬝ᵥ y := by
      simp only [hf, add_dotProduct, dotProduct_add, smul_dotProduct, dotProduct_smul,
        smul_eq_mul, dotProduct_comm y xpar]
      ring
    rw [e, hypar, hxx]
    nlinarith [hyy]
  have hrot_add : ∀ u w : V × K → ℝ, rotOp G (u + w) = rotOp G u + rotOp G w := fun u w => rfl
  have hrot_smul : ∀ (c : ℝ) (u : V × K → ℝ), rotOp G (c • u) = c • rotOp G u := fun c u => rfl
  have hexp : x ⬝ᵥ ((G.zigzag H).adjMatrix *ᵥ x) =
      c ^ 2 * (xpar ⬝ᵥ rotOp G xpar) + c * (xpar ⬝ᵥ rotOp G f) + c * (f ⬝ᵥ rotOp G xpar) +
        f ⬝ᵥ rotOp G f := by
    rw [zigzag_mulVec, dot_cloudOp_comm, hBx', hrot_add, hrot_smul]
    simp only [add_dotProduct, dotProduct_add, smul_dotProduct, dotProduct_smul, smul_eq_mul]
    ring
  set P := √(xpar ⬝ᵥ xpar)
  set S := √(x ⬝ᵥ x)
  set F := √(f ⬝ᵥ f)
  have hP0 : 0 ≤ P := Real.sqrt_nonneg _
  have hS0 : 0 ≤ S := Real.sqrt_nonneg _
  have hF0 : 0 ≤ F := Real.sqrt_nonneg _
  have hPP : P ^ 2 = xpar ⬝ᵥ xpar := Real.sq_sqrt (dot_self_nonneg' _)
  have hSS : S ^ 2 = x ⬝ᵥ x := Real.sq_sqrt (dot_self_nonneg' _)
  have hPS : P ≤ S := Real.sqrt_le_sqrt (by rw [hxx]; linarith [dot_self_nonneg' xperp])
  have hFS : F ≤ D2 * lam₂ * S :=
    calc F ≤ √((D2 * lam₂) ^ 2 * (x ⬝ᵥ x)) := Real.sqrt_le_sqrt hff
      _ = D2 * lam₂ * S := by rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (by positivity)]
  have hT1 : |xpar ⬝ᵥ rotOp G xpar| ≤ lam₁ * P ^ 2 := by rw [hPP]; exact hPpar
  have hT2 : |xpar ⬝ᵥ rotOp G f| ≤ P * F := by
    have := abs_dot_le xpar (rotOp G f); rwa [dot_rotOp_self] at this
  have hT3 : |f ⬝ᵥ rotOp G xpar| ≤ F * P := by
    have := abs_dot_le f (rotOp G xpar); rwa [dot_rotOp_self] at this
  have hT4 : |f ⬝ᵥ rotOp G f| ≤ F * F := by
    have := abs_dot_le f (rotOp G f); rwa [dot_rotOp_self] at this
  rw [hexp, ← hSS]
  exact zigzag_gap_arith (by positivity) h1 h2 h₂ hc hP0 hF0 hPS hFS hT1 hT2 hT3 hT4

end MathlibExt.Combinatorics.RotationMap
