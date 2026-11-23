/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Topology.Category.CGWH.NativeMappingPath

/-!
# Evaluation at the two ORIGINAL native interval endpoints

The maps are the original closed-category evaluation after the actual
realized endpoint and unit map. Their naturality and full-boundary
factorization identify global unit endpoints by the original source maps.
-/

noncomputable section

open CategoryTheory MonoidalCategory MonoidalClosed
open scoped Simplicial

universe u v

namespace CGWH

/-- The actual native evaluation at an ORIGINAL realized interval endpoint. -/
public abbrev nativeIntervalEvaluation (ε : Fin 2) (M : CGWH.{u, v}) :
    (ihom nativeInterval.{u, v}).obj M ⟶ M :=
  (λ_ ((ihom nativeInterval.{u, v}).obj M)).inv ≫
    (nativeIntervalEndpoint.{u, v} ε ▷ (ihom nativeInterval.{u, v}).obj M) ≫ (ihom.ev nativeInterval.{u, v}).app M

/-- Evaluation after a whole native homotopy map is its SAME original
endpoint restriction and original unit isomorphism. -/
@[reassoc]
public theorem nativeIntervalEvaluation_comp
    {A M : CGWH.{u, v}} (s : A ⟶ (ihom nativeInterval.{u, v}).obj M) (ε : Fin 2) :
    s ≫ nativeIntervalEvaluation.{u, v} ε M =
      (λ_ A).inv ≫ (nativeIntervalEndpoint.{u, v} ε ▷ A) ≫ MonoidalClosed.uncurry s := by
  let E := (ihom nativeInterval.{u, v}).obj M
  let e := nativeIntervalEndpoint.{u, v} ε
  let ev := (ihom.ev nativeInterval.{u, v}).app M
  calc
    s ≫ nativeIntervalEvaluation.{u, v} ε M = (s ≫ (λ_ E).inv) ≫ (e ▷ E) ≫ ev := by
      unfold nativeIntervalEvaluation
      simp only [E, e, ev, Category.assoc]
    _ = (λ_ A).inv ≫ (𝟙_ CGWH.{u, v} ◁ s) ≫ (e ▷ E) ≫ ev :=
      (congrArg (fun f => f ≫ (e ▷ E) ≫ ev) (leftUnitor_inv_naturality s)).trans
        (by simp only [Category.assoc])
    _ = (λ_ A).inv ≫ (e ▷ A) ≫ (nativeInterval.{u, v} ◁ s) ≫ ev := by
      simpa only [Category.assoc] using
        congrArg (fun f => (λ_ A).inv ≫ f ≫ ev) (whisker_exchange e s)
    _ = (λ_ A).inv ≫ (e ▷ A) ≫ MonoidalClosed.uncurry s := by
      rw [MonoidalClosed.uncurry_eq]

/-- Equality on the WHOLE original interval boundary retains equality
at BOTH original endpoint maps. -/
public theorem nativeIntervalEvaluation_eq_of_boundary
    {A M : CGWH.{u, v}} (s t : A ⟶ (ihom nativeInterval.{u, v}).obj M)
    (hb : s ≫ (MonoidalClosed.pre nativeIntervalBoundary.{u, v}).app M =
      t ≫ (MonoidalClosed.pre nativeIntervalBoundary.{u, v}).app M) (ε : Fin 2) :
    s ≫ nativeIntervalEvaluation.{u, v} ε M = t ≫ nativeIntervalEvaluation.{u, v} ε M := by
  have hB : (nativeIntervalBoundary.{u, v} ▷ A) ≫ MonoidalClosed.uncurry s =
      (nativeIntervalBoundary.{u, v} ▷ A) ≫ MonoidalClosed.uncurry t := by
    simpa only [MonoidalClosed.uncurry_pre_app] using congrArg
      (fun f : A ⟶ (ihom (SSet.toCGWH.{u, v}.obj (∂Δ[1] : SSet.{v}))).obj M =>
        MonoidalClosed.uncurry f) hb
  have htri : (nativeIntervalBoundaryEndpoint.{u, v} ε ▷ A) ≫ (nativeIntervalBoundary.{u, v} ▷ A) =
      nativeIntervalEndpoint.{u, v} ε ▷ A :=
    (MonoidalCategory.comp_whiskerRight _ _ _).symm.trans
      (congrArg (fun f => f ▷ A) (nativeIntervalBoundaryEndpoint_comp.{u, v} ε))
  have he : (nativeIntervalEndpoint.{u, v} ε ▷ A) ≫ MonoidalClosed.uncurry s =
      (nativeIntervalEndpoint.{u, v} ε ▷ A) ≫ MonoidalClosed.uncurry t := by
    simpa only [← Category.assoc, htri] using
      congrArg (fun f => (nativeIntervalBoundaryEndpoint.{u, v} ε ▷ A) ≫ f) hB
  rw [nativeIntervalEvaluation_comp.{u, v}, nativeIntervalEvaluation_comp.{u, v}]
  exact congrArg (fun f => (λ_ A).inv ≫ f) he

variable {A M : CGWH.{u, u}} [T2Space A] {f g : C(A, M)}

/-- The original first compact-open endpoint is the literal zero
evaluation of its DERIVED native homotopy map. -/
public theorem nativeMappingPathCurry_evaluation_zero (p : Path f g) :
    nativeMappingPathCurry p ≫ nativeIntervalEvaluation.{u, u} 0 M = ConcreteCategory.ofHom f := by
  rw [nativeIntervalEvaluation_comp.{u, u}]
  apply ConcreteCategory.hom_ext
  intro a
  let z := (λ_ A).inv a
  have ha : CartesianMonoidalCategory.snd (𝟙_ CGWH.{u, u}) A z = a := by
    simpa only [ConcreteCategory.comp_apply, ConcreteCategory.id_apply] using
      ConcreteCategory.congr_hom (CartesianMonoidalCategory.leftUnitor_inv_snd A) a
  have hz : tensorMk (CartesianMonoidalCategory.fst (𝟙_ CGWH.{u, u}) A z) a = z :=
    (congrArg (tensorMk (CartesianMonoidalCategory.fst (𝟙_ CGWH.{u, u}) A z)) ha.symm).trans
      (tensorMk_fst_snd z)
  rw [ConcreteCategory.comp_apply]
  change ((nativeIntervalEndpoint.{u, u} 0 ▷ A) ≫ MonoidalClosed.uncurry (nativeMappingPathCurry p)) z = f a
  rw [← hz, ConcreteCategory.comp_apply, tensorMk_whiskerRight,
    nativeMappingPathCurry_uncurry_apply, nativeIntervalClock_zero.{u, u}]
  exact congrArg (fun h : C(A, M) => h a) p.source

/-- The original second compact-open endpoint is the literal one
evaluation of its DERIVED native homotopy map. -/
public theorem nativeMappingPathCurry_evaluation_one (p : Path f g) :
    nativeMappingPathCurry p ≫ nativeIntervalEvaluation.{u, u} 1 M = ConcreteCategory.ofHom g := by
  rw [nativeIntervalEvaluation_comp.{u, u}]
  apply ConcreteCategory.hom_ext
  intro a
  let z := (λ_ A).inv a
  have ha : CartesianMonoidalCategory.snd (𝟙_ CGWH.{u, u}) A z = a := by
    simpa only [ConcreteCategory.comp_apply, ConcreteCategory.id_apply] using
      ConcreteCategory.congr_hom (CartesianMonoidalCategory.leftUnitor_inv_snd A) a
  have hz : tensorMk (CartesianMonoidalCategory.fst (𝟙_ CGWH.{u, u}) A z) a = z :=
    (congrArg (tensorMk (CartesianMonoidalCategory.fst (𝟙_ CGWH.{u, u}) A z)) ha.symm).trans
      (tensorMk_fst_snd z)
  rw [ConcreteCategory.comp_apply]
  change ((nativeIntervalEndpoint.{u, u} 1 ▷ A) ≫ MonoidalClosed.uncurry (nativeMappingPathCurry p)) z = g a
  rw [← hz, ConcreteCategory.comp_apply, tensorMk_whiskerRight,
    nativeMappingPathCurry_uncurry_apply, nativeIntervalClock_one.{u, u}]
  exact congrArg (fun h : C(A, M) => h a) p.target

end CGWH

end
