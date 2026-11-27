/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.CameralTorusBands
public import MathlibExt.AlgebraicGeometry.NativeLineDuals
public import MathlibExt.AlgebraicGeometry.FiniteCoverLocalComparison
public import Mathlib.LinearAlgebra.TensorProduct.Tower

/-!
# Actual ramification symbols on nonreduced cameral schemes

For a reflection s on an affine algebra B, the ideal-symbol module is
B tensor_(B^s) B^-, with the actual evaluation b tensor g ↦ bg. Its
sheafification is the line I_alpha of Donagi--Gaitsgory. Evaluation need
not be injective after nonflat base change: I_alpha is not replaced by
its image ideal. R_alpha is its computed sheaf dual, with the section
dual to evaluation.
Source: Donagi--Gaitsgory arXiv:math/0005132v3, Section5.2.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
@[expose] public noncomputable section
  AlgebraicGeometry.SheafedSpace.sheaf
namespace MathlibExt.AlgebraicGeometry.CameralRamificationSymbols

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open _root_.AlgebraicGeometry
open CoherentCurveLinearSeries NativeLineDuals
open scoped TensorProduct

variable {k : Type} [Field k] (B : Type) [CommRing B] [Algebra k B] (s : B ≃ₐ[k] B)

def invariantAlgebra : Subalgebra k B where
  carrier := {b | s b = b}
  algebraMap_mem' c := s.commutes c
  zero_mem' := map_zero s
  one_mem' := map_one s
  add_mem' {x y} hx hy := by change s (x + y) = x + y; rw [map_add, hx, hy]
  mul_mem' {x y} hx hy := by change s (x * y) = x * y; rw [map_mul, hx, hy]

def antiInvariant : Submodule (invariantAlgebra B s) B where
  carrier := {b | s b = -b}
  zero_mem' := by simp
  add_mem' {x y} hx hy := by change s (x + y) = -(x + y); rw [map_add, hx, hy, neg_add]
  smul_mem' c b hb := by
    change s (c.val * b) = -(c.val * b)
    rw [map_mul, c.property, hb, mul_neg]

abbrev symbols := B ⊗[invariantAlgebra B s] antiInvariant B s

def evaluation : symbols B s →ₗ[B] B :=
  TensorProduct.AlgebraTensorModule.lift
    (LinearMap.toSpanSingleton B _ ((antiInvariant B s).subtype))

@[simp] theorem evaluation_symbol (b : B) (g : antiInvariant B s) :
    evaluation B s (b ⊗ₜ[invariantAlgebra B s] g) = b * g.val := rfl

structure AffineReflection (Y : Over (Spec (.of k))) (a : Y.left ≅ Y.left) where
  algebra : CommAlgCat.{0} k
  neighborhood : Y.left.affineOpens
  stable : ∀ x : Y.left, x ∈ neighborhood.val ↔ a.hom x ∈ neighborhood.val
  chart : Spec (.of algebra) ≅ neighborhood.val.toScheme
  over : chart.hom ≫ neighborhood.val.ι ≫ Y.hom = Spec.algebraMap k algebra
  reflection : algebra ≃ₐ[k] algebra
  reflection_square : ∀ b : algebra, reflection (reflection b) = b
  geometric : Spec.map (CommRingCat.ofHom reflection.toAlgHom.toRingHom) ≫
    chart.hom ≫ neighborhood.val.ι = chart.hom ≫ neighborhood.val.ι ≫ a.hom

def chartSections {Y : Over (Spec (.of k))} {a : Y.left ≅ Y.left}
    (U : AffineReflection Y a) (I : Y.left.Modules) : ModuleCat U.algebra :=
  (ModuleCat.restrictScalars (Scheme.ΓSpecIso (.of U.algebra)).inv.hom).obj
    ((SheafOfModules.evaluation (Spec (.of U.algebra)).ringCatSheaf (.op ⊤)).obj
      ((Scheme.Modules.pullback (U.chart.hom ≫ U.neighborhood.val.ι)).obj I))

def affineEvaluation {Y : Over (Spec (.of k))} {a : Y.left ≅ Y.left}
    (U : AffineReflection Y a) {I : Y.left.Modules} (e : I ⟶ structureModule Y.left)
    (x : chartSections U I) : U.algebra :=
  (Scheme.ΓSpecIso (.of U.algebra)).hom.hom
    (((FiniteCoverLocalComparison.pullbackStructureIso
      (U.chart.hom ≫ U.neighborhood.val.ι)).hom.val.app (.op ⊤)).hom
      ((((Scheme.Modules.pullback (U.chart.hom ≫ U.neighborhood.val.ι)).map e).val.app
        (.op ⊤)).hom x))

structure IdealSymbols (Y : Over (Spec (.of k))) (a : Y.left ≅ Y.left) where
  module : Y.left.Modules
  line : IsLineBundle module
  evaluation : module ⟶ structureModule Y.left
  charts : ∀ x : Y.left, ∃ U : AffineReflection Y a, x ∈ U.neighborhood.val
  symbolSections : ∀ U : AffineReflection Y a,
    chartSections U module ≅ ModuleCat.of U.algebra (symbols U.algebra U.reflection)
  normalization : ∀ (U : AffineReflection Y a)
      (b : U.algebra) (g : antiInvariant U.algebra U.reflection),
    affineEvaluation U evaluation
      ((symbolSections U).inv.hom (b ⊗ₜ[invariantAlgebra U.algebra U.reflection] g)) = b * g.val
  fixedCokernel : cokernel evaluation ≅
    (Scheme.Modules.pushforward (equalizer.ι a.hom (𝟙 Y.left))).obj
      (structureModule (equalizer a.hom (𝟙 Y.left)))

def ramificationLine {Y : Over (Spec (.of k))} {a : Y.left ≅ Y.left}
    (I : IdealSymbols Y a) : Y.left.Modules := dualModule Y.left I.module

structure RamificationSection {Y : Over (Spec (.of k))} {a : Y.left ≅ Y.left}
    (I : IdealSymbols Y a) where
  duality : LineDuality Y.left I.module
  sectionMap : structureModule Y.left ⟶ ramificationLine I
  normalized : ∀ (U : Y.left.Opens) (v : Γ(I.module, U)),
    localEvaluation Y.left I.module U
      (((ramificationLine I).unitHomEquiv sectionMap).val (.op U)) v =
      (I.evaluation.val.app (.op U)).hom v

end MathlibExt.AlgebraicGeometry.CameralRamificationSymbols
