/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
  Author: @toskua, Avocado
-/
module

public import MathlibExt.RepresentationTheory.Homological.GroupCohomology.CupCocycleOneOne
public import Mathlib.RepresentationTheory.Homological.GroupCohomology.FiniteCyclic

/-!
# Norm comparison for degree-two group cohomology

Let `G` be a finite commutative group, `k` a commutative ring, `A` a representation, and `g` a
chosen element of `G`. Put `N_A = ∑ h : G, A.ρ h` and `D_g = A.ρ g - 1`. Evaluation at `g`,
the sum `z ↦ ∑ h, z(h,g)`, and the sum `w ↦ ∑ h, w(g,h,g)` define a morphism from the
inhomogeneous short complex `C¹(G,A) → C²(G,A) → C³(G,A)` to `A —N_A→ A —D_g→ A`.

A two-cocycle gives the `g`-invariant vector `I_g(z) = ∑ h, z(h,g)`. For a one-cochain `b`,
`I_g(d¹b) = N_A(b(g))`, so the comparison induces a map from `H²(G,A)` to the homology of the
norm complex. For one-cocycles `x,y`, the invariant of their cup is `∑ h, x(h) ⊗ h·y(g)`.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false

open CategoryTheory MonoidalCategory
open scoped BigOperators

namespace groupCohomology

universe u

variable {k G : Type u} [CommRing k] [CommGroup G] [Fintype G]

/-- Let `G` be a finite commutative group, `k` a commutative ring, `A : Rep k G`, and `g : G`. The
`k`-linear morphism `cyclicEvalOne A g : (G → A) → A` sends a one-cochain `b` to `b(g)`. -/
noncomputable def cyclicEvalOne (A : Rep k G) (g : G) :
    ModuleCat.of k (G → A) ⟶ ModuleCat.of k A :=
  ModuleCat.ofHom
    { toFun := fun b => b g
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }

/-- Let `G` be a finite commutative group, `k` a commutative ring, `A : Rep k G`, and `g : G`. The
`k`-linear morphism `cyclicSumTwo A g : (G × G → A) → A` sends `z` to `∑ h : G, z(h,g)`. -/
noncomputable def cyclicSumTwo (A : Rep k G) (g : G) :
    ModuleCat.of k (G × G → A) ⟶ ModuleCat.of k A :=
  ModuleCat.ofHom
    { toFun := fun z => ∑ h : G, z (h, g)
      map_add' := fun x y => by
        simp only [Pi.add_apply, Finset.sum_add_distrib]
      map_smul' := fun r x => by
        change (∑ h : G, r • x (h, g)) = r • ∑ h : G, x (h, g)
        rw [Finset.smul_sum] }

/-- Let `G` be a finite commutative group, `k` a commutative ring, `A : Rep k G`, and `g : G`. The
`k`-linear morphism `cyclicSumThree A g : (G × G × G → A) → A` sends `w` to `∑ h : G,
w(g,h,g)`. -/
noncomputable def cyclicSumThree (A : Rep k G) (g : G) :
    ModuleCat.of k (G × G × G → A) ⟶ ModuleCat.of k A :=
  ModuleCat.ofHom
    { toFun := fun z => ∑ h : G, z (g, h, g)
      map_add' := fun x y => by
        simp only [Pi.add_apply, Finset.sum_add_distrib]
      map_smul' := fun r x => by
        change (∑ h : G, r • x (g, h, g)) = r • ∑ h : G, x (g, h, g)
        rw [Finset.smul_sum] }

/-- Let `G` be a finite commutative group, `k` a commutative ring, `A : Rep k G`, and `g : G`.
With `N_A = ∑ h : G, A.ρ h`, `cyclicEvalOne A g ≫ N_A = d₁₂ A ≫ cyclicSumTwo A g`.
Equivalently, for every one-cochain `b`, `N_A(b(g)) = ∑ h, (h·b(g) - b(hg) + b(h))`. -/
theorem cyclicEvalOne_comp_norm (A : Rep k G) (g : G) :
    cyclicEvalOne A g ≫ A.norm.asHom.toModuleCatHom =
      d₁₂ A ≫ cyclicSumTwo A g := by
  ext b
  change A.ρ.norm (b g) =
    ∑ h : G, (A.ρ h (b g) - b (h * g) + b h)
  unfold Representation.norm
  simp only [LinearMap.sum_apply, Finset.sum_add_distrib,
    Finset.sum_sub_distrib]
  have hright : (∑ h : G, b (h * g)) = ∑ h : G, b h := by
    simpa using Fintype.sum_bijective (· * g)
      (Group.mulRight_bijective g) (fun h => b (h * g)) (fun h => b h)
        (fun _ => rfl)
  rw [hright, sub_add_cancel]

/-- Let `G` be a finite commutative group, `k` a commutative ring, `A : Rep k G`, and `g : G`.
Then `cyclicSumTwo A g ≫ (ρ(g) - 1) = d₂₃ A ≫ cyclicSumThree A g`. Thus for every two-cochain
`z`, `(ρ(g) - 1)(∑ h, z(h,g)) = ∑ h, d²z(g,h,g)`, where `d²z(a,b,c) = a·z(b,c) - z(ab,c) +
z(a,bc) - z(a,b)`. -/
theorem cyclicSumTwo_comp_sub (A : Rep k G) (g : G) :
    cyclicSumTwo A g ≫ (Rep.applyAsHom A g - 𝟙 A).toModuleCatHom =
      d₂₃ A ≫ cyclicSumThree A g := by
  ext z
  change A.ρ g (∑ h : G, z (h, g)) - (∑ h : G, z (h, g)) =
    ∑ h : G, (A.ρ g (z (h, g)) - z (g * h, g) +
      z (g, h * g) - z (g, h))
  rw [map_sum]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  have hleft : (∑ h : G, z (g * h, g)) = ∑ h : G, z (h, g) := by
    simpa using Fintype.sum_bijective (g * ·)
      (Group.mulLeft_bijective g) (fun h => z (g * h, g)) (fun h => z (h, g))
        (fun _ => rfl)
  have hright : (∑ h : G, z (g, h * g)) = ∑ h : G, z (g, h) := by
    simpa using Fintype.sum_bijective (· * g)
      (Group.mulRight_bijective g) (fun h => z (g, h * g)) (fun h => z (g, h))
        (fun _ => rfl)
  rw [hleft, hright]
  abel

/-- Let `G` be a finite commutative group, `k` a commutative ring, `A : Rep k G`, and `g : G`. The
morphism from `C¹(G,A) —d¹→ C²(G,A) —d²→ C³(G,A)` to `A —N_A→ A —(ρ(g)-1)→ A`, with `N_A = ∑ h
: G, A.ρ h`, has components `b ↦ b(g)`, `z ↦ ∑ h, z(h,g)`, and `w ↦ ∑ h, w(g,h,g)`. -/
noncomputable def cyclicEvenComparisonHom (A : Rep k G) (g : G) :
    shortComplexH2 A ⟶ Rep.FiniteCyclicGroup.normHomCompSub A g where
  τ₁ := cyclicEvalOne A g
  τ₂ := cyclicSumTwo A g
  τ₃ := cyclicSumThree A g
  comm₁₂ := cyclicEvalOne_comp_norm A g
  comm₂₃ := cyclicSumTwo_comp_sub A g

/-- Let `G` be a finite commutative group, `k` a commutative ring, `A : Rep k G`, `g : G`, and `z
∈ Z²(G,A)`. The sum `I_g(z) = ∑ h : G, z(h,g)` belongs to `ker (A.ρ g - 1)`, so it is fixed by
the action of `g`. -/
noncomputable def cyclicTwoCocycleInvariant
    (A : Rep k G) (g : G) (z : cocycles₂ A) :
    LinearMap.ker (Rep.applyAsHom A g - 𝟙 A).hom.toLinearMap := by
  refine ⟨∑ h : G, z (h, g), ?_⟩
  have hcomm := ConcreteCategory.congr_hom
    (cyclicSumTwo_comp_sub A g) z
  change (Rep.applyAsHom A g - 𝟙 A).hom
      ((cyclicSumTwo A g).hom z) = 0
  calc
    _ = (cyclicSumThree A g).hom (d₂₃ A z) := hcomm
    _ = (cyclicSumThree A g).hom 0 := congrArg _ z.property
    _ = 0 := map_zero _

/-- Let `G` be a finite commutative group, `k` a commutative ring, `A : Rep k G`, `g : G`, and `b
: G → A` a one-cochain. For the two-cocycle `d¹b`, `I_g(d¹b) = N_A(b(g))` as elements of `A`,
where `I_g(z) = ∑ h, z(h,g)` and `N_A(a) = ∑ h : G, h·a`. -/
theorem cyclicTwoCocycleInvariant_coboundary
    (A : Rep k G) (g : G) (b : G → A) :
    (cyclicTwoCocycleInvariant A g
      ⟨d₁₂ A b, d₁₂_apply_mem_cocycles₂ b⟩ : A) =
      A.norm.asHom.hom (b g) := by
  have hcomm := ConcreteCategory.congr_hom
    (cyclicEvalOne_comp_norm A g) b
  exact hcomm.symm

/-- Let `G` be a finite commutative group, `k` a commutative ring, `A : Rep k G`, `g : G`, and
`z,w ∈ Z²(G,A)`. If `H2π A z = H2π A w`, then `I_g(z) - I_g(w) ∈ range N_A`, where `I_g(z) = ∑
h, z(h,g)` and `N_A(a) = ∑ h : G, h·a`. -/
theorem cyclicTwoCocycleInvariant_sub_mem_norm_range_of_H2π_eq
    (A : Rep k G) (g : G) (z w : cocycles₂ A)
    (hzw : H2π A z = H2π A w) :
    (cyclicTwoCocycleInvariant A g z : A) -
        (cyclicTwoCocycleInvariant A g w : A) ∈
      LinearMap.range A.norm.asHom.hom.toLinearMap := by
  have hboundary := (H2π_eq_iff z w).mp hzw
  rw [coboundaries₂] at hboundary
  rcases hboundary with ⟨b, hb⟩
  refine ⟨b g, ?_⟩
  change A.norm.asHom.hom (b g) = _
  rw [← cyclicTwoCocycleInvariant_coboundary A g b]
  change (∑ h : G, d₁₂ A b (h, g)) =
    (∑ h : G, z (h, g)) - (∑ h : G, w (h, g))
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro h _
  exact congrFun hb (h, g)

/-- Let `G` be a finite commutative group, `k` a commutative ring, `A,B : Rep k G`, `g : G`, and
one-cocycles `x ∈ Z¹(G,A)`, `y ∈ Z¹(G,B)`. The invariant in `A ⊗ B` of their two-cocycle cup
satisfies `I_g(x ∪ y) = ∑ h : G, x(h) ⊗ₜ[k] B.ρ h (y(g))`, where `I_g(z) = ∑ h, z(h,g)`. -/
theorem cyclicTwoCocycleInvariant_cup
    (A B : Rep k G) (g : G) (x : cocycles₁ A) (y : cocycles₁ B) :
    (cyclicTwoCocycleInvariant (A ⊗ B : Rep k G) g
      (cupCocycleOneOne A B x y) : (A ⊗ B : Rep k G)) =
      ∑ h : G, x h ⊗ₜ[k] B.ρ h (y g) := by
  rfl

/-- Let `G` be a finite commutative group, `k` a commutative ring, `A : Rep k G`, and `g : G`. The
comparison with the short complex `A —N_A→ A —(ρ(g)-1)→ A` induces a `k`-linear map from
`H²(G,A)` to its middle homology, `ker (ρ(g)-1) / range N_A`. The degree-two component of the
short-complex comparison sends a cochain `z` to `∑ h : G, z(h,g)`, with `N_A = ∑ h : G, A.ρ
h`. -/
noncomputable def cyclicEvenComparisonMap (A : Rep k G) (g : G) :
    H2 A ⟶ (Rep.FiniteCyclicGroup.normHomCompSub A g).homology :=
  (H2Iso A).hom ≫
    (shortComplexH2 A).moduleCatHomologyIso.inv ≫
      ShortComplex.homologyMap (cyclicEvenComparisonHom A g)

end groupCohomology
