/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.ModuleInternalHom
public import MathlibExt.AlgebraicGeometry.CurveVectorBundles
public import MathlibExt.CategoryTheory.Abelian.RightDerivedLinear
public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# Geometric bundle trace and its actual cohomology kernel

The endomorphism sheaf is the actual slice-wise internal Hom, with its
proved sheaf condition. A geometric trace is normalized on finite bases
over affine opens by the actual matrix trace. The scalar map is multiplication
on the restricted sheaf, and the trace-free object is its actual kernel.

Reference: Huybrechts--Lehn, *The Geometry of Moduli Spaces of Sheaves*,
Section 4.5 (trace and determinant in deformation theory). The generic
flat module lifting obstruction/torsor theory is already proved in
AxiomMath/Stacks, Deformation/RingedSpaceThickening/FlatModuleDeformation.lean
at c496df0d9beea9deaeabcea8492605f9a0a2313b, and is not requested here.
-/

@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.BundleTrace

open CategoryTheory CategoryTheory.Limits Opposite Module
open _root_.AlgebraicGeometry
open ModuleInternalHom CoherentCurveLinearSeries CurveVectorBundles

attribute [local implicit_reducible] AlgebraicGeometry.Scheme.Modules
  AlgebraicGeometry.Scheme.Modules.Hom ModuleInternalHom.ORestr ModuleInternalHom.restrFun

universe u

/-- The actual module-Hom sheaf, obtained from the completed slice-wise construction. -/
abbrev homSheaf (X : Scheme.{u}) (E F : X.Modules) : X.Modules where
  val := internalHom X.presheaf E.val F.val
  isSheaf := internalHom_isSheaf X.presheaf E.val F.val F.isSheaf

abbrev endSheaf (X : Scheme.{u}) (E : X.Modules) : X.Modules := homSheaf X E E

section PresheafScalars

variable {C : Type u} [Category.{u} C] (O : Cᵒᵖ ⥤ CommRingCat.{u})
  (E : PresheafOfModules.{u} (Oforget O))

/-- Multiplication by a section on the actual restricted presheaf. -/
def scalarAtOfPresheaf (U : C) :
    ModuleCat.of ((Oforget O).obj (op U)) ((Oforget O).obj (op U)) ⟶
      internalHomObj O E E U := by
  letI := homModule O E E U
  exact ModuleCat.ofHom
    (X := ModuleCat.of ((Oforget O).obj (op U)) ((Oforget O).obj (op U)))
    (Y := internalHomObj O E E U)
    { toFun := fun c ↦ multEndoHom O E U c
      map_add' := by
        intro c d
        apply PresheafOfModules.hom_ext
        intro W
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro x
        change fRestr O U (c + d) W • x = fRestr O U c W • x + fRestr O U d W • x
        rw [fRestr, fRestr, fRestr, map_add, add_smul]
      map_smul' := by
        intro c d
        apply PresheafOfModules.hom_ext
        intro W
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro x
        change fRestr O U (c * d) W • x = fRestr O U c W • (fRestr O U d W • x)
        rw [fRestr, fRestr, fRestr, map_mul, mul_smul] }

/-- Scalar multiplication is an actual internal-endomorphism presheaf map. -/
def scalarPresheaf : PresheafOfModules.unit (Oforget O) ⟶ internalHom O E E where
  app U := scalarAtOfPresheaf O E U.unop
  naturality := by
    intro U V f
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro c
    apply PresheafOfModules.hom_ext
    intro W
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change fRestr O V.unop (((Oforget O).map f).hom c) W • x =
      fRestr O U.unop c ((Over.map f.unop).op.obj W) • x
    congr 1
    dsimp only [fRestr]
    change ((Oforget O).map W.unop.hom.op).hom (((Oforget O).map f).hom c) =
      ((Oforget O).map (W.unop.hom ≫ f.unop).op).hom c
    rw [op_comp, Functor.map_comp]
    rfl

end PresheafScalars

/-- Scalar multiplication on restrictions gives the actual bundle-endomorphism sheaf map. -/
def scalarEndomorphisms (X : Scheme.{u}) (E : X.Modules) :
    structureModule X ⟶ endSheaf X E where
  val := scalarPresheaf (C := X.Opens) X.presheaf E.val

instance localRing_commRing (X : Scheme.{u}) (U : X.Opens) :
    CommRing (X.ringCatSheaf.obj.obj (op U)) :=
  inferInstanceAs (CommRing (X.presheaf.obj (op U)))

/-- Evaluation of a local internal endomorphism on the terminal slice object. -/
def localEndomorphism (X : Scheme.{u}) (E : X.Modules) (U : X.Opens)
    (a : (endSheaf X E).val.obj (op U)) :
    Module.End (X.ringCatSheaf.obj.obj (op U)) (E.val.obj (op U)) :=
  (a.app (op (Over.mk (𝟙 U)))).hom

/-- The trace of a rank-`r` vector bundle, pinned on finite affine frames by the
matrix trace; its scalar law fixes the rank. Affine opens on which `E` has a
basis cover `X` because `E` is locally free of rank `r`, so the trace is unique.
On a non-affine open, a basis of global sections need not trivialize the sheaf. -/
structure TraceData (X : Scheme.{u}) (E : X.Modules) (r : ℕ) where
  vectorBundle : IsVectorBundle E r
  trace : endSheaf X E ⟶ structureModule X
  frame_trace : ∀ (U : X.Opens), IsAffineOpen U →
    ∀
      (b : Basis (Fin r) (X.ringCatSheaf.obj.obj (op U)) (E.val.obj (op U)))
      (a : (endSheaf X E).val.obj (op U)),
    (show X.ringCatSheaf.obj.obj (op U) from (trace.val.app (op U)).hom a) =
      (LinearMap.toMatrix b b (localEndomorphism X E U a)).trace
  scalar_trace : scalarEndomorphisms X E ≫ trace = r • 𝟙 (structureModule X)

/-- The actual trace-free endomorphism sheaf. -/
abbrev traceFreeSheaf {X : Scheme.{u}} {E : X.Modules} {r : ℕ}
    (T : TraceData X E r) : X.Modules := kernel T.trace

/-- The actual map on the already-fixed right-derived global-section modules. -/
def traceOnCohomology {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) {E : X.Modules} {r : ℕ}
    (T : TraceData X E r) (n : ℕ) :
    cohomology f (endSheaf X E) n ⟶ cohomology f (structureModule X) n :=
  ((sectionsFunctor f).rightDerived n).map T.trace

/-- Scalars act through the actual derived map of the geometric multiplication morphism. -/
def scalarsOnCohomology {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) (E : X.Modules) (n : ℕ) :
    cohomology f (structureModule X) n ⟶ cohomology f (endSheaf X E) n :=
  ((sectionsFunctor f).rightDerived n).map (scalarEndomorphisms X E)

/-- The scalar/trace composition is multiplication by the actual bundle rank in every degree. -/
theorem scalarsOnCohomology_comp_trace {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) {E : X.Modules} {r : ℕ}
    (T : TraceData X E r) (n : ℕ) :
    scalarsOnCohomology f E n ≫ traceOnCohomology f T n =
      r • 𝟙 (cohomology f (structureModule X) n) := by
  let := CategoryTheory.DerivedLinear.rightDerived_additive (sectionsFunctor f) n
  dsimp only [scalarsOnCohomology, traceOnCohomology]
  rw [← Functor.map_comp, T.scalar_trace, Functor.map_nsmul,
    CategoryTheory.Functor.map_id]

/-- The actual trace-zero subspace of the endomorphism-sheaf cohomology. -/
abbrev traceFreeCohomology {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) {E : X.Modules} {r : ℕ}
    (T : TraceData X E r) (n : ℕ) := (traceOnCohomology f T n).hom.ker

end MathlibExt.AlgebraicGeometry.BundleTrace
