/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.ManifoldComponentModuleMaps
import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing

/-!
# Native component module assembly

The native component assembly unit is an isomorphism for a finite
component partition.
-/

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open MathlibExt.AlgebraicGeometry
open KahlerClassGeometry HarmonicHolomorphicModuleModels HolomorphicCotangentModuleModels
open HolomorphicSheafHiggsModels ManifoldComponentModuleMaps
open scoped Manifold ContDiff

private theorem disjoint_gluing {M : Type} [TopologicalSpace M]
    (F : TopCat.Sheaf AddCommGrpCat (TopCat.of M)) (P : FiniteComponentPartition (M := M))
    (V : Opens M) (U : Fin P.count → Opens M) (r : ∀ i, U i ⟶ V)
    (hU : ∀ i, U i ≤ P.component i) (hcover : V ≤ iSup U)
    (sf : ∀ i, F.obj.obj (op (U i))) :
    ∃! s : F.obj.obj (op V), ∀ i, F.obj.map (r i).op s = sf i := by
  apply F.existsUnique_gluing' U V r hcover sf
  intro i j
  by_cases hij : i = j
  · subst j
    congr 1
  · apply F.eq_of_locally_eq' (fun _ : Empty => ⊥) (U i ⊓ U j)
      (fun k => k.elim) _ _ _ (fun k => k.elim)
    simp only [iSup_of_empty, le_bot_iff]
    apply Opens.ext
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro x hx
    exact Set.disjoint_left.mp (P.disjoint i j hij) (hU i hx.1) (hU j hx.2)

set_option backward.isDefEq.respectTransparency false in
/-- The same actual module is recovered from its actual native component restrictions. -/
public theorem native_component_module_assembly_isIso {n : ℕ} {M : Type}
    [TopologicalSpace M] [ChartedSpace (Coordinates n) M]
    [IsManifold 𝓘(ℂ, Coordinates n) ∞ M]
    [HolomorphicCoefficientSheaves.SheafCondition (Coordinates n) M]
    (P : FiniteComponentPartition (M := M))
    (E : HolomorphicModules (n := n) (M := M)) : IsIso (componentAssemblyUnit (n := n) P E) := by
  rw [← isIso_iff_of_reflects_iso _ (SheafOfModules.toSheaf _)]
  rw [← isIso_iff_of_reflects_iso _ (sheafToPresheaf _ _)]
  rw [NatTrans.isIso_iff_isIso_app]
  intro V
  rw [ConcreteCategory.isIso_iff_bijective]
  change Function.Bijective ((componentAssemblyUnit (n := n) P E).val.app V)
  let D := Discrete.functor (fun i : Fin P.count =>
    (componentPushforward (n := n) (P.component i)).obj
      ((componentRestriction (n := n) (P.component i)).obj E))
  let F : TopCat.Sheaf AddCommGrpCat (TopCat.of M) := ⟨E.val.presheaf, E.isSheaf⟩
  let U : Fin P.count → Opens M := fun i => P.component i ⨯ V.unop
  let r : ∀ i, U i ⟶ V.unop := fun _ => prod.snd
  have hU : ∀ i, U i ≤ P.component i := fun _ => prod.fst.le
  have hcover : V.unop ≤ iSup U := by
    intro x hx
    obtain ⟨i, hi⟩ := P.covers x
    apply Opens.mem_iSup.mpr
    refine ⟨i, ?_⟩
    have hinf : P.component i ⊓ V.unop ≤ U i :=
      (prod.lift (homOfLE inf_le_left : P.component i ⊓ V.unop ⟶ P.component i)
        (homOfLE inf_le_right : P.component i ⊓ V.unop ⟶ V.unop)).le
    exact hinf ⟨hi, hx⟩
  have hπ (i : Fin P.count) (s : E.val.obj V) :
      (limit.π D ⟨i⟩).val.app V ((componentAssemblyUnit (n := n) P E).val.app V s) =
        E.val.map (r i).op s := by
    change ((componentAssemblyUnit (n := n) P E ≫ limit.π D ⟨i⟩).val.app V) s = _
    dsimp only [D]
    simp only [componentAssemblyUnit, limit.lift_π]
    change E.val.map ((Over.forgetAdjStar (P.component i)).counit.app V.unop).op s = _
    rw [Over.forgetAdjStar_counit_app]
    rfl
  constructor
  · intro s t hst
    apply F.eq_of_locally_eq' U V.unop r hcover
    intro i
    change E.val.map (r i).op s = E.val.map (r i).op t
    rw [← hπ i s, ← hπ i t, hst]
  · intro t
    obtain ⟨s, hs, _⟩ := disjoint_gluing F P V.unop U r hU hcover
      (fun i => (limit.π D ⟨i⟩).val.app V t)
    refine ⟨s, ?_⟩
    apply Concrete.isLimit_ext (D ⋙ SheafOfModules.evaluation _ V)
      (isLimitOfPreserves (SheafOfModules.evaluation _ V) (limit.isLimit D))
    intro i
    exact (hπ i.as s).trans (hs i.as)
