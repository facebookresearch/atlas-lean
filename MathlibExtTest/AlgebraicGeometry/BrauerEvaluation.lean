/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.AlgebraicGeometry.BrauerEvaluation

/-!
# Geometric pullback of multiplicative cohomology

The units presheaf is the literal global-units functor. Pullback is
functorial, so cohomological Brauer groups are preserved by pullback. The
trivial extension `K/K` gives an actual finite Galois étale Čech chart, and
geometric unit values at the identity `Ksep`-point recover the unit.
-/

noncomputable section

namespace MathlibExtTest.BrauerEvaluation

open CategoryTheory Opposite AlgebraicGeometry
open AlgebraicGeometry.BrauerCoefficients AlgebraicGeometry.BrauerEvaluation

/-! ## Units and pullback -/

example (X : Scheme.{0}) (u : Γ(X, ⊤)ˣ) : unitsPresheaf.obj (op X) := Additive.ofMul u

example {X Y : Scheme.{0}} (f : X ⟶ Y) (u : Γ(Y, ⊤)ˣ) :
    unitsPresheaf.map f.op (Additive.ofMul u) =
      Additive.ofMul (Units.map f.appTop.hom.toMonoidHom u) := rfl

example : IsGrothendieckAbelian.{1} EtaleAb := inferInstance

example (X : Scheme.{0}) (a : GmH2 X) : pullback (𝟙 X) a = a := by simp

example {X Y Z : Scheme.{0}} (f : X ⟶ Y) (g : Y ⟶ Z) (a : GmH2 Z) :
    pullback (f ≫ g) a = pullback f (pullback g a) := by
  rw [pullback_comp]
  rfl

example (K L : Type) [Field K] [Field L] (f : K →+* L) {X : Scheme.{0}}
    (p : Spec (.of K) ⟶ X) (a : GmH2 X) :
    pointPullback L (Spec.map (CommRingCat.ofHom f) ≫ p) a =
      pullback (Spec.map (CommRingCat.ofHom f)) (pointPullback K p a) := by
  rw [pointPullback_baseChange]
  rfl

/-- Pullback preserves the cohomological Brauer group. -/
example {X Y : Scheme.{0}} (f : X ⟶ Y) (a : Brauer Y) : pullback f a.val ∈ Brauer X := by
  obtain ⟨n, hn, ha⟩ := isOfFinAddOrder_iff_nsmul_eq_zero.mp ((AddCommGroup.mem_torsion _).mp a.2)
  exact (AddCommGroup.mem_torsion _).mpr
    (isOfFinAddOrder_iff_nsmul_eq_zero.mpr ⟨n, hn, by rw [← map_nsmul, ha, map_zero]⟩)

/-! ## Čech charts -/

variable (K : Type) [Field K]

private abbrev botField := (⊥ : IntermediateField K (SeparableClosure K))

private instance : IsIso (CommRingCat.ofHom (algebraMap K (botField K))) := by
  have h : CommRingCat.ofHom (algebraMap K (botField K)) =
      (IntermediateField.botEquiv K (SeparableClosure K)).symm.toCommRingCatIso.hom :=
    CommRingCat.hom_ext (RingHom.ext fun x =>
      (IntermediateField.botEquiv_symm (F := K) (E := SeparableClosure K) x).symm)
  rw [h]
  infer_instance

/-- The trivial extension is a finite Galois étale Čech chart. -/
def trivialChart : GaloisCechChart K where
  E := ⊥

example : galoisCover (trivialChart K) =
    Arrow.mk (Spec.map (CommRingCat.ofHom (algebraMap K (trivialChart K).E))) := rfl

example (n : ℕ) : cechTerm (trivialChart K) n =
    (galoisCover (trivialChart K)).cechNerve.obj (op (SimplexCategory.mk n)) := rfl

example (g : Field.absoluteGaloisGroup K) : sepAutomorphism g = g.separableClosure := rfl

/-- The value of a units section at the identity `Ksep`-point is the unit itself. -/
example (u : (SeparableClosure K)ˣ) :
    unitPointValue (K := K) (𝟙 (Spec (.of (SeparableClosure K))))
      (Additive.ofMul
        (Units.map (Scheme.ΓSpecIso (.of (SeparableClosure K))).inv.hom.toMonoidHom u)) =
      Additive.ofMul u := by
  apply Additive.toMul.injective
  ext
  simp only [unitPointValue, Scheme.Γ_map, Quiver.Hom.unop_op, Scheme.Hom.id_appTop]
  simp
  exact (Scheme.ΓSpecIso (.of (SeparableClosure K))).inv_hom_id_apply (u : SeparableClosure K)

end MathlibExtTest.BrauerEvaluation
