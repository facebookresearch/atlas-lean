/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.Convex.NewtonPolygon
public import Mathlib.Analysis.Convex.Combination
public import Mathlib.Analysis.Convex.KreinMilman
public import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# The Newton polygon of a product is the Minkowski sum (Ostrowski)

For bivariate polynomials `f, g` over a ring without zero divisors,
`New(f g) = New(f) + New(g)`: multiplying polynomials adds their Newton polygons. The inclusion
`⊆` holds because every exponent of `f g` is a sum of exponents of `f` and `g`. For `⊇`, every
vertex of `New(f) + New(g)` decomposes in exactly one way as a sum of exponents of `f` and `g`,
so the corresponding coefficient of `f g` is a single nonzero product; a polygon is the convex
hull of its vertices (Krein–Milman).

Source: B. Sturmfels, *Solving Systems of Polynomial Equations*, CBMS Regional Conference Series
in Mathematics 97, AMS, 2002, Section 3.1 (`New(g · h) = New(g) + New(h)`); A. Ostrowski,
*Über die Bedeutung der Theorie der konvexen Polyeder für die formale Algebra*, Jahresber.
Deutsch. Math.-Verein. 30 (1921).
-/

@[expose] public section

noncomputable section

namespace MathlibExt.Analysis.Convex.NewtonPolygonMul

open NewtonPolygon
open scoped Pointwise

variable {k : Type*} [CommRing k] [NoZeroDivisors k]

private theorem exponentToReal_add (a b : Fin 2 →₀ ℕ) :
    exponentToReal (a + b) = exponentToReal a + exponentToReal b := by
  funext i; simp [exponentToReal]

private theorem exponentToReal_injective : Function.Injective exponentToReal := by
  intro a b h
  ext i
  have := congrFun h i
  simpa [exponentToReal] using this

omit [NoZeroDivisors k] in
/-- **Newton support of a product.** Every exponent of `f g` is the sum of an exponent of `f` and
an exponent of `g`, over any commutative ring. -/
theorem newtonSupport_mul_subset (f g : MvPolynomial (Fin 2) k) :
    newtonSupport (f * g) ⊆ newtonSupport f + newtonSupport g := by
  classical
  rintro _ ⟨e, he, rfl⟩
  obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_add.1 (MvPolynomial.support_mul f g he)
  exact ⟨_, ⟨a, ha, rfl⟩, _, ⟨b, hb, rfl⟩, (exponentToReal_add a b).symm⟩

/-- **Vertices of a Minkowski sum of Newton polygons are exponents of the product.** If
`a + b`, with `a` an exponent of `f` and `b` one of `g`, is an extreme point of
`New(f) + New(g)`, then the coefficient of `x^{a+b}` in `f g` is the single nonzero product
`f_a g_b`. -/
theorem add_mem_support_of_extreme (f g : MvPolynomial (Fin 2) k) {a b : Fin 2 →₀ ℕ}
    (ha : a ∈ f.support) (hb : b ∈ g.support)
    (hext : exponentToReal (a + b) ∈
      (convexHull ℝ (newtonSupport f + newtonSupport g)).extremePoints ℝ) :
    a + b ∈ (f * g).support := by
  classical
  rw [MvPolynomial.mem_support_iff, MvPolynomial.coeff_mul,
    Finset.sum_eq_single (a, b)]
  · exact mul_ne_zero (MvPolynomial.mem_support_iff.1 ha) (MvPolynomial.mem_support_iff.1 hb)
  · rintro ⟨x, y⟩ hxy hne
    rw [Finset.mem_antidiagonal] at hxy
    have hxy' : x + y = a + b := hxy
    by_contra h0
    have hx : x ∈ f.support := MvPolynomial.mem_support_iff.2 (left_ne_zero_of_mul h0)
    have hy : y ∈ g.support := MvPolynomial.mem_support_iff.2 (right_ne_zero_of_mul h0)
    set A := convexHull ℝ (newtonSupport f + newtonSupport g)
    have hmem : ∀ {u v}, u ∈ f.support → v ∈ g.support → exponentToReal (u + v) ∈ A :=
      fun hu hv ↦ subset_convexHull ℝ _ ⟨_, ⟨_, hu, rfl⟩, _, ⟨_, hv, rfl⟩,
        (exponentToReal_add _ _).symm⟩
    -- `a + b` is the midpoint of `x + b` and `a + y`
    have hmid : exponentToReal (a + b) =
        midpoint ℝ (exponentToReal (x + b)) (exponentToReal (a + y)) := by
      have hsum : exponentToReal (x + b) + exponentToReal (a + y) =
          exponentToReal (a + b) + exponentToReal (a + b) := by
        rw [← exponentToReal_add, ← exponentToReal_add]
        congr 1
        rw [show x + b + (a + y) = (x + y) + (a + b) by abel, hxy']
      rw [midpoint_eq_smul_add, hsum, ← two_smul ℝ, smul_smul]
      norm_num
    have hos : exponentToReal (a + b) ∈
        openSegment ℝ (exponentToReal (x + b)) (exponentToReal (a + y)) := by
      let : Invertible (2 : ℝ) := invertibleOfNonzero two_ne_zero
      rw [hmid]
      exact midpoint_mem_openSegment _ _
    have hseg := (mem_extremePoints.1 hext).2 _ (hmem hx hb) _ (hmem ha hy) hos
    have h1 : x + b = a + b := exponentToReal_injective hseg.1
    have hxa : x = a := add_right_cancel h1
    subst hxa
    have : y = b := add_left_cancel hxy'
    exact hne (by rw [this])
  · intro h
    exact absurd (by simp : (a, b) ∈ Finset.antidiagonal (a + b)) h

/-- **Ostrowski's theorem in the plane.** For bivariate polynomials over a ring without zero
divisors, the Newton polygon of a product is the Minkowski sum of the Newton polygons,
`New(f g) = New(f) + New(g)` (Sturmfels, *Solving Systems of Polynomial Equations*, CBMS 97,
Section 3.1). -/
theorem newtonPolygon_mul (f g : MvPolynomial (Fin 2) k) :
    newtonPolygon (f * g) = newtonPolygon f + newtonPolygon g := by
  classical
  unfold newtonPolygon
  rw [← convexHull_add]
  apply le_antisymm (convexHull_mono (newtonSupport_mul_subset f g))
  set A := newtonSupport f + newtonSupport g
  have hAfin : A.Finite :=
    ((f.support.finite_toSet.image _).add (g.support.finite_toSet.image _))
  set E := (convexHull ℝ A).extremePoints ℝ
  have hEA : E ⊆ A := extremePoints_convexHull_subset
  have hEfin : E.Finite := hAfin.subset hEA
  have hKM : convexHull ℝ E = convexHull ℝ A := by
    have := closure_convexHull_extremePoints (hAfin.isCompact_convexHull ℝ)
      (convex_convexHull ℝ A)
    rwa [(hEfin.isClosed_convexHull ℝ).closure_eq] at this
  rw [← hKM]
  apply convexHull_min _ (convex_convexHull ℝ _)
  intro e he
  obtain ⟨_, ⟨a, ha, rfl⟩, _, ⟨b, hb, rfl⟩, rfl⟩ := hEA he
  change exponentToReal a + exponentToReal b ∈ E at he
  change exponentToReal a + exponentToReal b ∈ _
  rw [← exponentToReal_add] at he ⊢
  exact subset_convexHull ℝ _ ⟨a + b, add_mem_support_of_extreme f g ha hb he, rfl⟩

end MathlibExt.Analysis.Convex.NewtonPolygonMul
