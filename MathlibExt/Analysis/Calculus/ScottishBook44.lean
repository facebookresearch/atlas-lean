/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# Doubly ruled graphs

A real function of two variables whose graph is doubly ruled is affine or defines a
hyperbolic paraboloid. In coordinates along two rulings, subtracting the plane they
span reduces the classification to showing that the remaining function is a multiple of
the product of the coordinates.
-/

@[expose] public section

namespace MathlibExt.Analysis.Calculus.ScottishBook44Wanted

/-- **Line lying in a graph.** Let $f$ be a real-valued function of two real variables, and let
$x_0, y_0, u, v, w$ be real numbers. The line through $(x_0, y_0, f(x_0, y_0))$ with direction
$(u, v, w)$ lies in the graph of $f$ when $(u, v) \ne (0, 0)$ and
$f(x_0 + tu, y_0 + tv) = f(x_0, y_0) + tw$ for every real $t$. -/
def LineInGraph (f : ℝ → ℝ → ℝ) (x₀ y₀ u v w : ℝ) : Prop :=
  ¬ (u = 0 ∧ v = 0) ∧
    ∀ t : ℝ, f (x₀ + t * u) (y₀ + t * v) = f x₀ y₀ + t * w

/-- **Doubly ruled graph.** The graph of a real-valued function $f$ of two real variables is
doubly ruled when for every point $(x_0, y_0) \in \mathbb{R}^2$ there are $(u_1, v_1, w_1)$ and
$(u_2, v_2, w_2)$ in $\mathbb{R}^3$ such that the lines through $(x_0, y_0, f(x_0, y_0))$ with
directions $(u_1, v_1, w_1)$ and $(u_2, v_2, w_2)$ both lie in the graph of $f$, and $(u_2, v_2)$
is not a real multiple of $(u_1, v_1)$.

A line lying in the graph has a nonzero horizontal direction, so the last condition holds exactly
when the two lines are distinct. -/
def DoublyRuledGraph (f : ℝ → ℝ → ℝ) : Prop :=
  ∀ x₀ y₀ : ℝ, ∃ u₁ v₁ w₁ u₂ v₂ w₂ : ℝ,
    LineInGraph f x₀ y₀ u₁ v₁ w₁ ∧ LineInGraph f x₀ y₀ u₂ v₂ w₂ ∧
    ¬ ∃ c : ℝ, u₂ = c * u₁ ∧ v₂ = c * v₁

private lemma det_ne_zero {u v U V : ℝ} (h : ¬ (u = 0 ∧ v = 0))
    (hind : ¬ ∃ c : ℝ, U = c * u ∧ V = c * v) : u * V - v * U ≠ 0 := by
  intro hd
  apply hind
  by_cases hu : u = 0
  · subst u
    have hv : v ≠ 0 := fun hv ↦ h ⟨rfl, hv⟩
    refine ⟨V / v, ?_, by field_simp⟩
    simpa [hv] using hd
  · refine ⟨U / u, by field_simp, ?_⟩
    field_simp
    linarith

private lemma swap_line {f : ℝ → ℝ → ℝ} {x y u v w : ℝ} (hl : LineInGraph f x y u v w) :
    LineInGraph (fun a b ↦ f b a) y x v u w :=
  ⟨fun h ↦ hl.1 h.symm, hl.2⟩

private lemma swap_ruled {f : ℝ → ℝ → ℝ} (hf : DoublyRuledGraph f) :
    DoublyRuledGraph (fun a b ↦ f b a) := by
  intro x y
  obtain ⟨u, v, w, U, V, W, hl, hL, hind⟩ := hf y x
  exact ⟨v, u, w, V, U, W, swap_line hl, swap_line hL, fun ⟨c, hc⟩ ↦ hind ⟨c, hc.symm⟩⟩

-- Use height in the projected plane as the parameter on a nonhorizontal ruling.
private lemma transversal {f : ℝ → ℝ → ℝ} (hf : DoublyRuledGraph f) (r y : ℝ) :
    ∃ m n : ℝ, ∀ s : ℝ, f (r + (s - y) * m) s = f r y + (s - y) * n := by
  obtain ⟨u, v, w, U, V, W, hl, hL, hind⟩ := hf r y
  have hdet := det_ne_zero hl.1 hind
  have ht {a b c : ℝ} (h : LineInGraph f r y a b c) (hb : b ≠ 0) :
      ∃ m n : ℝ, ∀ s : ℝ, f (r + (s - y) * m) s = f r y + (s - y) * n := by
    refine ⟨a / b, c / b, fun s ↦ ?_⟩
    convert h.2 ((s - y) / b) using 1 <;> congr 1 <;> field_simp; ring
  by_cases hv : v = 0
  · exact ht hL fun hV ↦ hdet (by simp [hv, hV])
  · exact ht hl hv

-- A transversal with endpoints (p, 0) and (q, b) has prescribed values at both ends.
private lemma transversal_endpoints {f : ℝ → ℝ → ℝ} (hf : DoublyRuledGraph f)
    (hbottom : ∀ x, f x 0 = 0) {b k : ℝ} (htop : ∀ x, f x b = k * x) (r t₀ : ℝ) :
    ∃ p q : ℝ, p + t₀ * (q - p) = r ∧
      ∀ t : ℝ, f (p + t * (q - p)) (t * b) = t * (k * q) := by
  obtain ⟨m, n, h⟩ := transversal hf r (t₀ * b)
  let p := r - t₀ * b * m
  let q := p + b * m
  have hx (t : ℝ) : r + (t * b - t₀ * b) * m = p + t * (q - p) := by dsimp [q, p]; ring
  have ht (t : ℝ) := h (t * b)
  simp_rw [hx] at ht
  have h₀ := ht 0
  have h₁ := ht 1
  simp [hbottom] at h₀
  simp [htop] at h₁
  refine ⟨p, q, by dsimp [q, p]; ring, fun t ↦ ?_⟩
  linear_combination ht t - (1 - t) * h₀ - t * h₁

-- A nonvertical transversal crosses the vertical axis, where the function is zero.
-- Its affine height then forces one of its endpoints to lie on that axis.
private lemma endpoint_on_axis {f : ℝ → ℝ → ℝ} (haxis : ∀ y, f 0 y = 0)
    {p q b k : ℝ} (hk : k ≠ 0)
    (h : ∀ t : ℝ, f (p + t * (q - p)) (t * b) = t * (k * q)) (hpq : p ≠ q) :
    p = 0 ∨ q = 0 := by
  have hd : q - p ≠ 0 := sub_ne_zero.mpr hpq.symm
  let t := -p / (q - p)
  have hx : p + t * (q - p) = 0 := by dsimp [t]; field_simp; ring
  have hz := h t
  rw [hx, haxis] at hz
  by_contra! hn
  exact (mul_ne_zero (div_ne_zero (neg_ne_zero.mpr hn.1) hd) (mul_ne_zero hk hn.2)) hz.symm

private lemma product_of_row {f : ℝ → ℝ → ℝ} (hf : DoublyRuledGraph f)
    (hbottom : ∀ x, f x 0 = 0) (haxis : ∀ y, f 0 y = 0)
    {b k : ℝ} (hb : b ≠ 0) (hk : k ≠ 0) (htop : ∀ x, f x b = k * x) :
    ∀ x y : ℝ, f x y = (k / b) * x * y := by
  intro x y
  obtain ⟨p, q, hp, h⟩ := transversal_endpoints hf hbottom htop x 0
  obtain ⟨p', q', hq', h'⟩ := transversal_endpoints hf hbottom htop x 1
  simp only [zero_mul, add_zero] at hp
  simp only [one_mul, add_sub_cancel] at hq'
  subst p
  subst q'
  have vertical {r : ℝ} (hl : ∀ t : ℝ, f (r + t * (r - r)) (t * b) = t * (k * r)) :
      f r y = k / b * r * y := by
    have ht := hl (y / b)
    rw [div_mul_cancel₀ _ hb] at ht
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using ht
  by_cases hx : x = 0
  · simp [hx, haxis]
  by_cases hq : x = q
  · subst q
    exact vertical h
  by_cases hp' : p' = x
  · subst p'
    exact vertical h'
  -- Otherwise the two transversals give different heights at their common midpoint.
  obtain rfl := (endpoint_on_axis haxis hk h hq).resolve_left hx
  obtain rfl := (endpoint_on_axis haxis hk h' hp').resolve_right hx
  have hm := h (1 / 2)
  have hm' := h' (1 / 2)
  ring_nf at hm hm'
  exact False.elim ((mul_ne_zero hk hx) (by linarith))

-- At a point of nonzero height, an oblique ruling must project onto a line through
-- the origin: its intersections with the two axes must be the same zero of its height.
private lemma radial_of_oblique {f : ℝ → ℝ → ℝ} (hbottom : ∀ x, f x 0 = 0)
    (haxis : ∀ y, f 0 y = 0) {x y u v w : ℝ} (hxy : f x y ≠ 0)
    (hl : LineInGraph f x y u v w) (hu : u ≠ 0) (hv : v ≠ 0) : x * v = y * u := by
  have hx := hl.2 (-x / u)
  have hy := hl.2 (-y / v)
  rw [div_mul_cancel₀ _ hu, add_neg_cancel, haxis] at hx
  rw [div_mul_cancel₀ _ hv, add_neg_cancel, hbottom] at hy
  have hw : w ≠ 0 := by
    rintro rfl
    exact hxy (by simpa using hx.symm)
  have ht : -x / u = -y / v := mul_right_cancel₀ hw (by linarith)
  field_simp at ht
  linarith

private lemma product_of_horizontal {f : ℝ → ℝ → ℝ} (hf : DoublyRuledGraph f)
    (hbottom : ∀ x, f x 0 = 0) (haxis : ∀ y, f 0 y = 0)
    {x y u w : ℝ} (hxy : f x y ≠ 0) (hl : LineInGraph f x y u 0 w) :
    ∃ c : ℝ, ∀ r s : ℝ, f r s = c * r * s := by
  have hu : u ≠ 0 := fun h ↦ hl.1 ⟨h, rfl⟩
  have hrow (r : ℝ) : f r y = f x y + (r - x) / u * w := by
    simpa [div_mul_cancel₀ _ hu] using hl.2 ((r - x) / u)
  have h₀ := hrow 0
  rw [haxis] at h₀
  have hk : w / u ≠ 0 := by
    apply div_ne_zero _ hu
    rintro rfl
    exact hxy (by simpa using h₀.symm)
  have hy : y ≠ 0 := by rintro rfl; exact hxy (hbottom x)
  refine ⟨(w / u) / y, product_of_row hf hbottom haxis hy hk fun r ↦ ?_⟩
  rw [hrow]
  linear_combination -h₀

private lemma product_of_zero_axes {f : ℝ → ℝ → ℝ} (hf : DoublyRuledGraph f)
    (hbottom : ∀ x, f x 0 = 0) (haxis : ∀ y, f 0 y = 0) :
    ∃ k : ℝ, ∀ x y : ℝ, f x y = k * x * y := by
  by_cases hz : ∀ x y, f x y = 0
  · exact ⟨0, by simp [hz]⟩
  push Not at hz
  obtain ⟨x, y, hxy⟩ := hz
  obtain ⟨u, v, w, U, V, W, hl, hL, hind⟩ := hf x y
  have parallel_axis {a b c : ℝ} (h : LineInGraph f x y a b c) (hab : a = 0 ∨ b = 0) :
      ∃ k : ℝ, ∀ r s : ℝ, f r s = k * r * s := by
    rcases hab with rfl | rfl
    · obtain ⟨k, hk⟩ := product_of_horizontal (swap_ruled hf) haxis hbottom hxy (swap_line h)
      exact ⟨k, fun r s ↦ (hk s r).trans (by ring)⟩
    · exact product_of_horizontal hf hbottom haxis hxy h
  by_cases h : u = 0 ∨ v = 0
  · exact parallel_axis hl h
  by_cases H : U = 0 ∨ V = 0
  · exact parallel_axis hL H
  obtain ⟨hu, hv⟩ := not_or.mp h
  obtain ⟨hU, hV⟩ := not_or.mp H
  have h₁ := radial_of_oblique hbottom haxis hxy hl hu hv
  have h₂ := radial_of_oblique hbottom haxis hxy hL hU hV
  have hx : x ≠ 0 := by rintro rfl; exact hxy (haxis y)
  exfalso
  apply det_ne_zero hl.1 hind
  apply mul_left_cancel₀ hx
  linear_combination u * h₂ - U * h₁

-- Pull the graph back by a change of horizontal basis and subtract an affine function.
private lemma ruled_in_coordinates {f : ℝ → ℝ → ℝ} (hf : DoublyRuledGraph f)
    {a b c d : ℝ} (hsurj : ∀ x y : ℝ, ∃ s t : ℝ, a * s + b * t = x ∧ c * s + d * t = y)
    (p q z : ℝ) :
    DoublyRuledGraph (fun s t ↦ f (a * s + b * t) (c * s + d * t) - (z + p * s + q * t)) := by
  intro s t
  obtain ⟨u, v, w, U, V, W, hl, hL, hind⟩ := hf (a * s + b * t) (c * s + d * t)
  obtain ⟨i, j, hx, hy⟩ := hsurj u v
  obtain ⟨I, J, hX, hY⟩ := hsurj U V
  have lift_line {i j u v w : ℝ} (hx : a * i + b * j = u) (hy : c * i + d * j = v)
      (h : LineInGraph f (a * s + b * t) (c * s + d * t) u v w) :
      LineInGraph (fun s t ↦ f (a * s + b * t) (c * s + d * t) - (z + p * s + q * t))
        s t i j (w - p * i - q * j) := by
    refine ⟨?_, fun l ↦ ?_⟩
    · rintro ⟨rfl, rfl⟩
      exact h.1 ⟨by simpa using hx.symm, by simpa using hy.symm⟩
    · dsimp
      rw [show a * (s + l * i) + b * (t + l * j) = a * s + b * t + l * u by
            linear_combination l * hx,
          show c * (s + l * i) + d * (t + l * j) = c * s + d * t + l * v by
            linear_combination l * hy, h.2]
      ring
  refine ⟨i, j, _, I, J, _, lift_line hx hy hl, lift_line hX hY hL, ?_⟩
  rintro ⟨l, rfl, rfl⟩
  exact hind ⟨l, by linear_combination l * hx - hX, by linear_combination l * hy - hY⟩

/--
**Doubly ruled graphs are planes or hyperbolic paraboloids.** Let $f$ be a real-valued
function of two real variables whose graph is doubly ruled; no continuity of $f$ is assumed. Then
there are real numbers $a, b, c, d, e, g$ such that
$f(x, y) = ax^2 + bxy + cy^2 + dx + ey + g$ for all real $x$ and $y$, and either $a = b = c = 0$
(the graph is a plane) or $b^2 - 4ac > 0$ (the graph is a hyperbolic paraboloid).

This answers Steinhaus's Problem 44 of the Scottish Book, which asks whether such a surface, the
graph of a continuous function, must be a hyperbolic paraboloid, and whether this can be proved
without continuity. Banach answered both questions affirmatively, with a proof based on the remark
that any two lines on the surface either intersect or have parallel projections on the
$xy$-plane; planes are the degenerate doubly ruled case.

Source: H. Steinhaus, Problem 44 of the Scottish Book; addendum in the
Scottish Book, 30 July 1935: solved affirmatively by Banach, also without
assuming continuity; see the commentary in R. D. Mauldin (ed.),
The Scottish Book, 2nd ed. (Birkhäuser, 2015).
-/
theorem doubly_ruled_graph_is_quadric :
    ∀ f : ℝ → ℝ → ℝ, DoublyRuledGraph f →
      ∃ a b c d e g : ℝ,
        (∀ x y : ℝ, f x y = a * x ^ 2 + b * x * y + c * y ^ 2 + d * x + e * y + g) ∧
        ((a = 0 ∧ b = 0 ∧ c = 0) ∨ b ^ 2 - 4 * a * c > 0) := by
  intro f hf
  obtain ⟨u, v, p, U, V, q, hl, hL, hind⟩ := hf 0 0
  let δ := u * V - v * U
  have hδ : δ ≠ 0 := det_ne_zero hl.1 hind
  -- The two coordinate functions in the basis of the rulings through the origin.
  let A := V / δ
  let B := -U / δ
  let C := -v / δ
  let D := u / δ
  have hcoords (x y : ℝ) :
      u * (A * x + B * y) + U * (C * x + D * y) = x ∧
      v * (A * x + B * y) + V * (C * x + D * y) = y := by
    constructor <;> dsimp [A, B, C, D] <;> field_simp [hδ] <;> dsimp [δ] <;> ring
  let g (s t : ℝ) := f (u * s + U * t) (v * s + V * t) - (f 0 0 + p * s + q * t)
  have hg : DoublyRuledGraph g :=
    ruled_in_coordinates hf (fun x y ↦ ⟨_, _, hcoords x y⟩) p q (f 0 0)
  have hbottom (s : ℝ) : g s 0 = 0 := by
    simpa [g, mul_comm, sub_eq_zero] using hl.2 s
  have haxis (t : ℝ) : g 0 t = 0 := by
    simpa [g, mul_comm, sub_eq_zero] using hL.2 t
  obtain ⟨k, hk⟩ := product_of_zero_axes hg hbottom haxis
  refine ⟨k * A * C, k * (A * D + B * C), k * B * D, p * A + q * C, p * B + q * D, f 0 0,
    fun x y ↦ ?_, ?_⟩
  · have h := hk (A * x + B * y) (C * x + D * y)
    simp only [g, (hcoords x y).1, (hcoords x y).2] at h
    linear_combination h
  · by_cases h : k = 0
    · exact Or.inl (by simp [h])
    · right
      have hd : A * D - B * C = 1 / δ := by
        dsimp [A, B, C, D]
        field_simp [hδ]
        dsimp [δ]
        ring
      rw [show (k * (A * D + B * C)) ^ 2 - 4 * (k * A * C) * (k * B * D) =
          (k * (A * D - B * C)) ^ 2 by ring, hd]
      exact sq_pos_of_ne_zero (mul_ne_zero h (div_ne_zero one_ne_zero hδ))

end MathlibExt.Analysis.Calculus.ScottishBook44Wanted
