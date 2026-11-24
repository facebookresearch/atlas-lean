/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.AlgebraicTopology.Quasicategory.Core
public import MathlibExt.AlgebraicTopology.Quasicategory.RelativeOuterHornN2
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback

/-!
# Cores of strict pullbacks along inner fibrations

The canonical comparison from the core of a pullback to the pullback of
cores is defined for arbitrary simplicial sets. It is an isomorphism when
one leg is an inner fibration and the base and the other source are
quasicategories. The inner source and the pullback are then quasicategories
as well.

An edge of the pullback is an equivalence exactly when both projections
are equivalences. The reverse implication uses two strict relative right
two-horn fillers and inverse algebra in the ordinary homotopy category.
The full base triangles are prescribed; no second unit for a fixed inverse
edge is imposed. This is a project proof from the opposite of Joyal's
Theorem 4.13, in its quasicategory scope.
-/

@[expose] public section

set_option autoImplicit false

open CategoryTheory Limits Opposite
open scoped Simplicial

universe u

namespace SSet

variable {X Y S : SSet.{u}}

/-- The canonical comparison from the core of a pullback to the pullback
of cores, obtained by restricting its two projections. -/
noncomputable def core.pullbackComparison (p : X ⟶ S) (q : Y ⟶ S)
    [HasPullback p q] [HasPullback (core.map p) (core.map q)] :
    (core (pullback p q : SSet.{u}) : SSet.{u}) ⟶
      pullback (core.map p) (core.map q) :=
  pullback.lift (core.map (pullback.fst (f := p) (g := q)))
    (core.map (pullback.snd (f := p) (g := q))) (by
    rw [← core.map_comp, ← core.map_comp, pullback.condition])

/-- The comparison map projects to `SSet.core.map` of the first leg. -/
@[reassoc (attr := simp)]
theorem core.pullbackComparison_fst (p : X ⟶ S) (q : Y ⟶ S)
    [HasPullback p q] [HasPullback (core.map p) (core.map q)] :
    core.pullbackComparison p q ≫ pullback.fst (core.map p) (core.map q) =
      core.map (pullback.fst p q) :=
  pullback.lift_fst _ _ _

/-- The comparison map projects to `SSet.core.map` of the second leg. -/
@[reassoc (attr := simp)]
theorem core.pullbackComparison_snd (p : X ⟶ S) (q : Y ⟶ S)
    [HasPullback p q] [HasPullback (core.map p) (core.map q)] :
    core.pullbackComparison p q ≫ pullback.snd (core.map p) (core.map q) =
      core.map (pullback.snd p q) :=
  pullback.lift_snd _ _ _

/-- A strict pullback of an inner fibration over a quasicategory source
is a quasicategory. The other source and the common base need not be
quasicategories for this assertion. -/
theorem quasicategory_pullback_of_innerFibration (p : X ⟶ S) (q : Y ⟶ S)
    [InnerFibration p] [Quasicategory Y] : Quasicategory (pullback p q) := by
  have : InnerFibration (pullback.snd p q) :=
    ⟨innerFibrations.pullback_snd p q (mem_innerFibrations p)⟩
  exact quasicategory_of_innerFibration (pullback.snd p q)

/-- Lift the entire inverse-unit triangle in `Y`. Its paired triangle
in the strict pullback gives a left inverse relation for the supplied
edge in the homotopy category. -/
private theorem exists_left_inverse_in_pullback (p : X ⟶ S) (q : Y ⟶ S)
    [InnerFibration p] [Quasicategory S] [Quasicategory Y]
    {x₀ x₁ : (pullback p q : SSet.{u}) _⦋0⦌} (e : Edge x₀ x₁)
    (heX : (e.map (pullback.fst p q)).IsEquivalence)
    (heY : (e.map (pullback.snd p q)).IsEquivalence) :
    ∃ v : Edge x₁ x₀, Nonempty (Edge.CompStruct v e (Edge.id x₁)) := by
  let eX := e.map (pullback.fst p q)
  let eY := e.map (pullback.snd p q)
  obtain ⟨I⟩ := heY.nonempty_invStruct
  let a : (Δ[1] : SSet.{u}) ⟶ X := yonedaEquiv.symm eX.edge
  let b : (Δ[1] : SSet.{u}) ⟶ X :=
    yonedaEquiv.symm (Edge.id ((pullback.fst p q).app _ x₁)).edge
  let tY : (Δ[2] : SSet.{u}) ⟶ Y := yonedaEquiv.symm I.invHomId.simplex
  have hab : stdSimplex.δ (0 : Fin 2) ≫ a = stdSimplex.δ (0 : Fin 2) ≫ b := by
    dsimp only [a, b]
    rw [stdSimplex.δ_comp_yonedaEquiv_symm, stdSimplex.δ_comp_yonedaEquiv_symm,
      eX.tgt_eq, Edge.tgt_eq]
  let f : ∀ (j : Fin 3) (_ : j ≠ 2), (Δ[1] : SSet.{u}) ⟶ X :=
    fun j _ ↦ ![a, b, b] j
  have hf : horn.IsCompatible f := by
    rw [horn.isCompatible_iff]
    intro j k hj hk hjk
    fin_cases j <;> fin_cases k <;>
      simp only [f, Fin.lt_def, Nat.reduceAdd, Fin.reduceFinMk, Fin.reducePred,
        Fin.isValue, Nat.succ_eq_add_one, Matrix.cons_val] at hjk ⊢ <;> simp_all
  let σ₀ : (Λ[2, 2] : SSet.{u}) ⟶ X := hf.desc
  have σ₀0 : horn.ι 2 0 (by decide) ≫ σ₀ = a := hf.ι_desc 0 (by decide)
  have σ₀1 : horn.ι 2 1 (by decide) ≫ σ₀ = b := hf.ι_desc 1 (by decide)
  have ha : a ≫ p = stdSimplex.δ (0 : Fin 3) ≫ (tY ≫ q) := by
    dsimp only [a, tY]
    rw [← Category.assoc, stdSimplex.δ_comp_yonedaEquiv_symm, I.invHomId.d₀,
      yonedaEquiv_symm_comp, yonedaEquiv_symm_comp]
    change yonedaEquiv.symm ((pullback.fst p q ≫ p).app _ e.edge) =
      yonedaEquiv.symm ((pullback.snd p q ≫ q).app _ e.edge)
    rw [pullback.condition]
  have hvertex : p.app _ ((pullback.fst p q).app _ x₁) =
      q.app _ ((pullback.snd p q).app _ x₁) :=
    ConcreteCategory.congr_hom (congr_app (pullback.condition (f := p) (g := q)) _) x₁
  have hb : b ≫ p = stdSimplex.δ (1 : Fin 3) ≫ (tY ≫ q) := by
    dsimp only [b, tY]
    rw [← Category.assoc, stdSimplex.δ_comp_yonedaEquiv_symm, I.invHomId.d₁,
      yonedaEquiv_symm_comp, yonedaEquiv_symm_comp,
      ← Edge.map_edge, Edge.map_id, ← Edge.map_edge, Edge.map_id, hvertex]
  have hsq : σ₀ ≫ p = Λ[2, 2].ι ≫ (tY ≫ q) := by
    apply horn.hom_ext'
    intro j hj
    fin_cases j <;> simp only [Fin.isValue, Fin.reduceFinMk]
    · rw [← Category.assoc, σ₀0, horn.ι_ι_assoc]
      exact ha
    · rw [← Category.assoc, σ₀1, horn.ι_ι_assoc]
      exact hb
    · exact (hj rfl).elim
  have hcritical : (Edge.mk'
      (yonedaEquiv (horn.ι 2 0 (by decide) ≫ σ₀))).IsEquivalence := by
    rw [σ₀0]
    exact heX.of_edge_eq (by dsimp only [a]; rw [Equiv.apply_symm_apply]; rfl)
  obtain ⟨tX, htX, htBase⟩ :=
    exists_fill_relativeSpecialOuterHorn_two_two σ₀ (tY ≫ q) hsq hcritical
  have tX0 : stdSimplex.δ (0 : Fin 3) ≫ tX = a := by
    rw [← σ₀0, ← htX, horn.ι_ι_assoc]
  have tX1 : stdSimplex.δ (1 : Fin 3) ≫ tX = b := by
    rw [← σ₀1, ← htX, horn.ι_ι_assoc]
  let T : (Δ[2] : SSet.{u}) ⟶ pullback p q := pullback.lift tX tY htBase
  have T0 : stdSimplex.δ (0 : Fin 3) ≫ T = yonedaEquiv.symm e.edge := by
    apply pullback.hom_ext
    · dsimp only [T]
      rw [Category.assoc, pullback.lift_fst, tX0, yonedaEquiv_symm_comp]
      rfl
    · dsimp only [T, tY]
      rw [Category.assoc, pullback.lift_snd, stdSimplex.δ_comp_yonedaEquiv_symm,
        I.invHomId.d₀, yonedaEquiv_symm_comp]
      rfl
  have T1 : stdSimplex.δ (1 : Fin 3) ≫ T = yonedaEquiv.symm (Edge.id x₁).edge := by
    apply pullback.hom_ext
    · dsimp only [T, b]
      rw [Category.assoc, pullback.lift_fst, tX1, yonedaEquiv_symm_comp,
        ← Edge.map_edge, Edge.map_id]
    · dsimp only [T, tY]
      rw [Category.assoc, pullback.lift_snd, stdSimplex.δ_comp_yonedaEquiv_symm,
        I.invHomId.d₁, yonedaEquiv_symm_comp, ← Edge.map_edge, Edge.map_id]
  have t0 : (pullback p q : SSet.{u}).δ 0 (yonedaEquiv T) = e.edge := by
    rw [← stdSimplex.yonedaEquiv_δ_comp, T0, Equiv.apply_symm_apply]
  have t1 : (pullback p q : SSet.{u}).δ 1 (yonedaEquiv T) = (Edge.id x₁).edge := by
    rw [← stdSimplex.yonedaEquiv_δ_comp, T1, Equiv.apply_symm_apply]
  obtain ⟨z₀, z₁, z₂, v, e', h, c, hc⟩ := Edge.CompStruct.exists_of_simplex (yonedaEquiv T)
  have he' : e'.edge = e.edge := by rw [← c.d₀, hc]; exact t0
  have hh : h.edge = (Edge.id x₁).edge := by rw [← c.d₁, hc]; exact t1
  have hz₀ : z₀ = x₁ := by rw [← h.src_eq, hh, Edge.src_eq]
  have hz₁ : z₁ = x₀ := by rw [← e'.src_eq, he', e.src_eq]
  exact ⟨v.ofEq hz₀ hz₁, ⟨c.ofEq rfl he' hh⟩⟩

/-- In this strict pullback, an edge is an equivalence exactly when
both projections are equivalences. The source of `p` is a
quasicategory by `quasicategory_of_innerFibration`. -/
theorem Edge.isEquivalence_pullback_iff (p : X ⟶ S) (q : Y ⟶ S)
    [InnerFibration p] [Quasicategory S] [Quasicategory Y]
    {x₀ x₁ : (pullback p q : SSet.{u}) _⦋0⦌} (e : Edge x₀ x₁) :
    e.IsEquivalence ↔ (e.map (pullback.fst p q)).IsEquivalence ∧
      (e.map (pullback.snd p q)).IsEquivalence := by
  refine ⟨fun he ↦ ⟨he.map _, he.map _⟩, fun ⟨heX, heY⟩ ↦ ?_⟩
  obtain ⟨v, ⟨hv⟩⟩ := exists_left_inverse_in_pullback p q e heX heY
  have hvEquiv {Z : SSet.{u}} (π : pullback p q ⟶ Z)
      (he : (e.map π).IsEquivalence) : (v.map π).IsEquivalence := by
    have : IsIso (e.map π).toHoHom := he
    have : IsIso ((v.map π).toHoHom ≫ (e.map π).toHoHom) := by
      rw [Edge.toHoHom_comp (hv.map π), Edge.map_id, Edge.toHoHom_id]
      infer_instance
    exact IsIso.of_isIso_comp_right (v.map π).toHoHom (e.map π).toHoHom
  obtain ⟨w, ⟨hw⟩⟩ := exists_left_inverse_in_pullback p q v
    (hvEquiv _ heX) (hvEquiv _ heY)
  have hve : v.toHoHom ≫ e.toHoHom = 𝟙 _ := by
    rw [Edge.toHoHom_comp hv, Edge.toHoHom_id]
  have hwv : w.toHoHom ≫ v.toHoHom = 𝟙 _ := by
    rw [Edge.toHoHom_comp hw, Edge.toHoHom_id]
  have hew : e.toHoHom = w.toHoHom := by
    calc
      e.toHoHom = (w.toHoHom ≫ v.toHoHom) ≫ e.toHoHom := by rw [hwv, Category.id_comp]
      _ = w.toHoHom ≫ (v.toHoHom ≫ e.toHoHom) := Category.assoc _ _ _
      _ = w.toHoHom := by rw [hve, Category.comp_id]
  exact ⟨⟨v.toHoHom, by rw [hew]; exact hwv, hve⟩⟩

/-- Cores preserve the strict pullback of an inner fibration with
quasicategory base along any map with quasicategory source. -/
theorem core.isIso_pullbackComparison (p : X ⟶ S) (q : Y ⟶ S)
    [InnerFibration p] [Quasicategory S] [Quasicategory Y] :
    IsIso (core.pullbackComparison p q) := by
  let K := pullback (core.map p) (core.map q)
  let a : K ⟶ X := pullback.fst (core.map p) (core.map q) ≫ (core X).ι
  let b : K ⟶ Y := pullback.snd (core.map p) (core.map q) ≫ (core Y).ι
  have hab : a ≫ p = b ≫ q := by
    dsimp only [a, b]
    rw [Category.assoc, ← core.map_ι, ← Category.assoc, pullback.condition,
      Category.assoc, core.map_ι, ← Category.assoc]
  let g : K ⟶ pullback p q := pullback.lift a b hab
  have hg : Subcomplex.range g ≤ core (pullback p q) := by
    apply (le_core_iff _).mpr
    intro s hs
    obtain ⟨t, rfl⟩ := hs
    apply (Edge.isEquivalence_pullback_iff p q (Edge.mk' (g.app _ t))).mpr
    constructor
    · apply (mem_core_obj_one_iff.mp
        (((pullback.fst (core.map p) (core.map q)).app _ t).2)).of_edge_eq
      change ((pullback.fst (core.map p) (core.map q)).app _ t).1 =
        (g ≫ pullback.fst p q).app _ t
      exact (ConcreteCategory.congr_hom (congr_app (pullback.lift_fst a b hab) _) t).symm
    · apply (mem_core_obj_one_iff.mp
        (((pullback.snd (core.map p) (core.map q)).app _ t).2)).of_edge_eq
      change ((pullback.snd (core.map p) (core.map q)).app _ t).1 =
        (g ≫ pullback.snd p q).app _ t
      exact (ConcreteCategory.congr_hom (congr_app (pullback.lift_snd a b hab) _) t).symm
  let l : K ⟶ (core (pullback p q) : SSet.{u}) := Subcomplex.lift g hg
  refine ⟨⟨l, ?_, ?_⟩⟩
  · apply (cancel_mono (core (pullback p q)).ι).mp
    change core.pullbackComparison p q ≫ l ≫ (core (pullback p q)).ι =
      𝟙 _ ≫ (core (pullback p q)).ι
    rw [Subcomplex.lift_ι, Category.id_comp]
    apply pullback.hom_ext
    · dsimp only [g, a]
      rw [Category.assoc, pullback.lift_fst, ← Category.assoc,
        core.pullbackComparison_fst, core.map_ι]
    · dsimp only [g, b]
      rw [Category.assoc, pullback.lift_snd, ← Category.assoc,
        core.pullbackComparison_snd, core.map_ι]
  · apply pullback.hom_ext
    · apply (cancel_mono (core X).ι).mp
      simp only [Category.assoc, core.pullbackComparison_fst_assoc,
        Category.id_comp, core.map_ι]
      rw [← Category.assoc, Subcomplex.lift_ι]
      exact pullback.lift_fst a b hab
    · apply (cancel_mono (core Y).ι).mp
      simp only [Category.assoc, core.pullbackComparison_snd_assoc,
        Category.id_comp, core.map_ι]
      rw [← Category.assoc, Subcomplex.lift_ι]
      exact pullback.lift_snd a b hab

end SSet
