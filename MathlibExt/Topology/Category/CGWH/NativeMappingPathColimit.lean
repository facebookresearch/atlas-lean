/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Topology.Category.CGWH.CompatibleMappingPaths
public import MathlibExt.Topology.Category.CGWH.NativeIntervalEvaluation
public import MathlibExt.Topology.Category.CGWH.CartesianMonoidalComputations

/-!
# Descending the original whole compatible interval paths

The existing colimit universal property descends the DERIVED strict path
cocone. Complete original endpoint-map equations on every stage identify
the two global maps. The original zero-stage interval map is retained
strictly. Neither a global family nor a compatible cocone is supplied.
-/

noncomputable section

open CategoryTheory Limits MonoidalCategory MonoidalClosed HomotopicalAlgebra
open scoped CGWH.modelCategory

universe u

namespace CGWH

/-- Actual consecutive whole path comparisons descend through an original
colimit, retaining BOTH full global endpoint maps and the strict zero stage. -/
public theorem exists_nativeMappingPath_on_colimit
    (F : ℕ ⥤ CGWH.{u, u}) [∀ n, T2Space (F.obj n)]
    (C : Cocone F) (hC : IsColimit C) (M : CGWH.{u, u}) [IsFibrant M]
    (hobjects : ∀ n, IsCofibrant (F.obj n))
    (hcof : ∀ n, Cofibration (F.map (homOfLE (Nat.le_succ n))))
    (f₀ g₀ : C.pt ⟶ M) (f g : (n : ℕ) → C(F.obj n, M))
    (p q : (n : ℕ) → Path (f n) (g n))
    (hrestrict : ∀ n t a, q n t a = p (n + 1) t (F.map (homOfLE (Nat.le_succ n)) a))
    (hcompare : ∀ n, (p n).Homotopic (q n))
    (hf : ∀ n, ConcreteCategory.ofHom (f n) = C.ι.app n ≫ f₀)
    (hg : ∀ n, ConcreteCategory.ofHom (g n) = C.ι.app n ≫ g₀) :
    ∃ s : C.pt ⟶ (ihom nativeInterval.{u, u}).obj M,
      s ≫ nativeIntervalEvaluation 0 M = f₀ ∧
      s ≫ nativeIntervalEvaluation 1 M = g₀ ∧
      C.ι.app 0 ≫ s = nativeMappingPathCurry (p 0) := by
  let E := (ihom nativeInterval.{u, u}).obj M
  let r := (MonoidalClosed.pre nativeIntervalBoundary).app M
  obtain ⟨c, hc₀, hc⟩ := exists_compatibleMappingPathCocone
    F M hobjects hcof f g p q hrestrict hcompare
  let s := hC.desc (Cocone.mk E c)
  have hs (n : ℕ) : C.ι.app n ≫ s = c.app n := hC.fac (Cocone.mk E c) n
  have hb (n : ℕ) : c.app n ≫ r = nativeMappingPathCurry (p n) ≫ r := (hc n).choose
  have hzero : s ≫ nativeIntervalEvaluation 0 M = f₀ := by
    apply hC.hom_ext
    intro n
    calc
      C.ι.app n ≫ s ≫ nativeIntervalEvaluation 0 M =
          (C.ι.app n ≫ s) ≫ nativeIntervalEvaluation 0 M := (Category.assoc _ _ _).symm
      _ = c.app n ≫ nativeIntervalEvaluation 0 M := congrArg (fun k => k ≫ _) (hs n)
      _ = nativeMappingPathCurry (p n) ≫ nativeIntervalEvaluation 0 M :=
        nativeIntervalEvaluation_eq_of_boundary _ _ (hb n) 0
      _ = ConcreteCategory.ofHom (f n) := nativeMappingPathCurry_evaluation_zero (p n)
      _ = C.ι.app n ≫ f₀ := hf n
  have hone : s ≫ nativeIntervalEvaluation 1 M = g₀ := by
    apply hC.hom_ext
    intro n
    calc
      C.ι.app n ≫ s ≫ nativeIntervalEvaluation 1 M =
          (C.ι.app n ≫ s) ≫ nativeIntervalEvaluation 1 M := (Category.assoc _ _ _).symm
      _ = c.app n ≫ nativeIntervalEvaluation 1 M := congrArg (fun k => k ≫ _) (hs n)
      _ = nativeMappingPathCurry (p n) ≫ nativeIntervalEvaluation 1 M :=
        nativeIntervalEvaluation_eq_of_boundary _ _ (hb n) 1
      _ = ConcreteCategory.ofHom (g n) := nativeMappingPathCurry_evaluation_one (p n)
      _ = C.ι.app n ≫ g₀ := hg n
  exact ⟨s, hzero, hone, (hs 0).trans hc₀⟩

/-- A strict original stage restriction and its actual constant value fix
the original image point throughout the WHOLE native interval family. -/
public theorem nativeIntervalHomotopy_point_of_stage
    {D A M : CGWH.{u, u}} (i : D ⟶ A) (d : D) (a : A) (hia : i d = a)
    (H : nativeInterval.{u, u} ⊗ A ⟶ M)
    (k : D ⟶ (ihom nativeInterval).obj M)
    (hstage : (nativeInterval ◁ i) ≫ H = MonoidalClosed.uncurry k)
    (m : M) (hconstant : ∀ s, MonoidalClosed.uncurry k (tensorMk s d) = m) :
    ∀ s, H (tensorMk s a) = m := by
  intro s
  have h := ConcreteCategory.congr_hom hstage (tensorMk s d)
  have h' : H (tensorMk s (i d)) = MonoidalClosed.uncurry k (tensorMk s d) := by
    simpa only [ConcreteCategory.comp_apply, tensorMk_whiskerLeft] using h
  exact (congrArg (fun b => H (tensorMk s b)) hia).symm.trans (h'.trans (hconstant s))

end CGWH

end
