/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicGeometry.ComplexAnalytification
public import Mathlib.Algebra.Polynomial.Eval.Defs

@[expose] public section

/-!
# Concrete complex-point evaluation tests

The point of the affine line attached to polynomial evaluation at `a` must
evaluate its coordinate to `a`. In particular, the points attached to `0` and
`1` must be distinct. These checks exercise the identification of global
sections with the coordinate ring and the direction of the spectrum functor.

The remaining checks cover the unique complex point of `Spec ℂ`, the ring,
restriction and constant laws of evaluation, the basic analytic opens
(including a basic open separating the points `0` and `1` of the affine line),
continuity of evaluation, and the functor on schemes over `ℂ`.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory
open scoped Polynomial
open MathlibExt.AlgebraicGeometry.ComplexAnalytification

namespace MathlibExtTest.AlgebraicGeometry.ComplexAnalytification

private def affineLine : Over (Spec (.of ℂ)) :=
  Over.mk (Spec.map (CommRingCat.ofHom (Polynomial.C : ℂ →+* ℂ[X])))

private def point (a : ℂ) : ComplexPoints affineLine.hom :=
  ⟨Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom a)), by
    change Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom a)) ≫
      Spec.map (CommRingCat.ofHom Polynomial.C) = 𝟙 _
    rw [← Spec.map_comp]
    have h : CommRingCat.ofHom Polynomial.C ≫
        CommRingCat.ofHom (Polynomial.evalRingHom a) =
          𝟙 (CommRingCat.of ℂ) := by
      ext r
      simp
    rw [h, Spec.map_id]⟩

private def coordinate : Γ(affineLine.left, ⊤) :=
  (Scheme.ΓSpecIso (.of ℂ[X])).inv Polynomial.X

private def coordinateValue (p : ComplexPoints affineLine.hom) : ℂ :=
  ComplexPoints.eval coordinate p p.hom.preimage_top

private theorem coordinateValue_point (a : ℂ) :
    coordinateValue (point a) = a := by
  change ((Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom a))).appTop ≫
    (Scheme.ΓSpecIso (.of ℂ)).hom)
      ((Scheme.ΓSpecIso (.of ℂ[X])).inv Polynomial.X) = a
  rw [Scheme.ΓSpecIso_naturality]
  simp

example (a : ℂ) : coordinateValue (point a) = a :=
  coordinateValue_point a

example : point 0 ≠ point 1 := by
  intro h
  have hvalues := congrArg coordinateValue h
  simp only [coordinateValue_point, zero_ne_one] at hvalues


/-! ### The complex points of `Spec ℂ` -/

/-- `Spec ℂ` as a scheme over itself. -/
private def specC : Over (Spec (.of ℂ)) := Over.mk (𝟙 _)

/-- The identity section, the only complex point of `Spec ℂ`. -/
private def specPoint : ComplexPoints specC.hom :=
  ⟨𝟙 _, Category.id_comp _⟩

/-- `Spec ℂ` has exactly one complex point. -/
example (p : ComplexPoints specC.hom) : p = specPoint :=
  ComplexPoints.ext ((by simpa [specC] using p.hom_comp : p.hom = 𝟙 _).trans rfl)

/-- Evaluation at the point of `Spec ℂ` is the identification `Γ(Spec ℂ) ≅ ℂ`. -/
example (c : ℂ) :
    ComplexPoints.eval ((Scheme.ΓSpecIso (.of ℂ)).inv c) specPoint
      (ComplexPoints.mem_top _) = c := by
  have key : ∀ e, Scheme.Hom.appLE (𝟙 (Spec (.of ℂ))) ⊤ ⊤ e = 𝟙 _ := by
    intro e
    simp only [Scheme.Hom.appLE, Scheme.Hom.id_app]
    exact (Spec _).presheaf.map_id (Opposite.op ⊤)
  simp only [ComplexPoints.eval, specPoint, ComplexPoints.hom]
  rw [key]
  simp

/-! ### Evaluation laws -/

example (a : ℂ) :
    ComplexPoints.eval (coordinate * coordinate + 1) (point a)
      (ComplexPoints.mem_top _) = a * a + 1 := by
  simp only [ComplexPoints.eval_add, ComplexPoints.eval_mul,
    ComplexPoints.eval_one]
  rw [← coordinateValue, coordinateValue_point]

example (a c : ℂ) :
    ComplexPoints.eval (ComplexPoints.constHom (y := affineLine.hom) ⊤ c)
      (point a) (ComplexPoints.mem_top _) = c :=
  ComplexPoints.eval_constHom c (point a) _

/-- Restricting the coordinate to any open does not change its values. -/
example (V : affineLine.left.Opens) (a : ℂ) (hp : (point a).Mem V) :
    ComplexPoints.eval
      (affineLine.left.presheaf.map (homOfLE le_top).op coordinate)
      (point a) hp = a := by
  rw [ComplexPoints.eval_map]
  exact coordinateValue_point a

example (a : ℂ) (k : ℕ) :
    ComplexPoints.evalHom (point a) (ComplexPoints.mem_top _)
      (coordinate ^ k) = a ^ k := by
  rw [ComplexPoints.evalHom_apply, ComplexPoints.eval_pow, ← coordinateValue,
    coordinateValue_point]

/-! ### Basic analytic opens -/

example {Y : Scheme.{0}} {y : Y ⟶ Spec (.of ℂ)} (U : Y.Opens) (g : Γ(Y, U)) :
    ComplexPoints.basicSet (y := y) U g ∅ = ∅ := by
  ext p
  simp [ComplexPoints.mem_basicSet]

example {Y : Scheme.{0}} {y : Y ⟶ Spec (.of ℂ)} (U : Y.Opens) :
    IsOpen {p : ComplexPoints y | p.Mem U} :=
  ComplexPoints.isOpen_setOf_mem U

/-- The unit disc in the coordinate is an analytic open of the affine line that
contains the point `0` but not the point `1`. -/
private def disc : Set (ComplexPoints affineLine.hom) :=
  ComplexPoints.basicSet ⊤ coordinate (Metric.ball 0 1)

example : IsOpen disc :=
  ComplexPoints.isOpen_basicSet ⊤ coordinate Metric.isOpen_ball

example : point 0 ∈ disc ∧ point 1 ∉ disc := by
  constructor
  · refine ComplexPoints.mem_basicSet.2 ⟨ComplexPoints.mem_top _, ?_⟩
    rw [← coordinateValue, coordinateValue_point]
    simp
  · rintro ⟨hp, h⟩
    rw [← coordinateValue, coordinateValue_point] at h
    simp at h

example : Continuous fun p : {p : ComplexPoints affineLine.hom // p.Mem ⊤} =>
    ComplexPoints.eval coordinate p.1 p.2 :=
  ComplexPoints.continuous_eval ⊤ coordinate

/-- The coordinate is continuous on the complex points of the affine line:
its preimages of open sets are basic analytic opens. -/
example : Continuous coordinateValue := by
  rw [continuous_def]
  intro V hV
  have h : coordinateValue ⁻¹' V = ComplexPoints.basicSet ⊤ coordinate V := by
    ext p
    exact ⟨fun h => ⟨ComplexPoints.mem_top p, h⟩, fun ⟨_, h⟩ => h⟩
  rw [h]
  exact ComplexPoints.isOpen_basicSet ⊤ coordinate hV

/-! ### Functoriality -/

/-- The structure morphism of the affine line, as a morphism over `ℂ`. -/
private def toSpecC : affineLine ⟶ specC :=
  Over.homMk affineLine.hom (Category.comp_id _)

/-- The structure morphism sends every complex point to the point of
`Spec ℂ`. -/
example (a : ℂ) : spaceMap toSpecC (point a) = specPoint :=
  ComplexPoints.ext ((by simpa [specC] using
    (spaceMap toSpecC (point a)).hom_comp :
      (spaceMap toSpecC (point a)).hom = 𝟙 _).trans rfl)

example (a : ℂ) :
    ComplexPoints.map (𝟙 affineLine.left) (Category.id_comp _) (point a) =
      point a :=
  ComplexPoints.map_id _

example (a : ℂ) :
    ComplexPoints.map (𝟙 affineLine.left ≫ toSpecC.left)
        (by rw [Category.assoc, toSpecC.w, Category.id_comp]) (point a) =
      ComplexPoints.map toSpecC.left toSpecC.w
        (ComplexPoints.map (𝟙 affineLine.left) (Category.id_comp _) (point a)) :=
  ComplexPoints.map_comp _ _ _ _ _

example : functor.obj affineLine = space affineLine := rfl

example (a : ℂ) : (functor.map toSpecC) (point a) =
    ComplexPoints.map toSpecC.left toSpecC.w (point a) := rfl

example : functor.map (𝟙 affineLine) = 𝟙 (space affineLine) :=
  functor.map_id affineLine

/-- Pulling the coordinate back along the identity and evaluating agrees with
evaluating at the image point. -/
example (a : ℂ) :
    ComplexPoints.eval coordinate
      (ComplexPoints.map (𝟙 affineLine.left) (Category.id_comp _) (point a))
      (ComplexPoints.mem_top _) = a := by
  rw [ComplexPoints.eval_map_point, Scheme.Hom.id_app]
  exact coordinateValue_point a

example : Continuous (ComplexPoints.map toSpecC.left toSpecC.w) :=
  ComplexPoints.continuous_map _ _

end MathlibExtTest.AlgebraicGeometry.ComplexAnalytification
