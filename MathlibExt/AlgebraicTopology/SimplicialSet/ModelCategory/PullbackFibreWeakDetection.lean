/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.ScalarFibreWeakDetection
public import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.FunctorialFactorizations
public import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.RightProper
public import MathlibExt.AlgebraicTopology.ModelCategory.HomotopyPullback

/-!
# Weak maps detected on same-base pullback fibres

For fibrations `s : E ⟶ B` and `t : D ⟶ B` over any base, an arbitrary
commuting map `c : E ⟶ D` is a realization weak equivalence exactly when
every chosen point-pullback map is. The maps use the original `pullback.map`
with identity maps on the base and `Δ[0]`.

The proof uses the existing criterion for fibrations, native fibre/pullback
isomorphisms, factorization, and homotopy pullback invariance.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u

open CategoryTheory CategoryTheory.Limits Opposite HomotopicalAlgebra
open scoped Simplicial SSet.modelCategoryQuillen

namespace SSet

private def endpointSameBaseMap {E D B : SSet.{u}}
    (c : E ⟶ D) (s : E ⟶ B) (t : D ⟶ B) (h : c ≫ t = s)
    (b : (Δ[0] : SSet.{u}) ⟶ B) : pullback s b ⟶ pullback t b :=
  pullback.map s b t b c (𝟙 _) (𝟙 _) (by simpa using h.symm) (by simp)

@[reassoc]
private theorem endpointSameBaseMap_fst {E D B : SSet.{u}}
    (c : E ⟶ D) (s : E ⟶ B) (t : D ⟶ B) (h : c ≫ t = s)
    (b : (Δ[0] : SSet.{u}) ⟶ B) :
    endpointSameBaseMap c s t h b ≫ pullback.fst t b = pullback.fst s b ≫ c :=
  pullback.lift_fst _ _ _

@[reassoc]
private theorem endpointSameBaseMap_snd {E D B : SSet.{u}}
    (c : E ⟶ D) (s : E ⟶ B) (t : D ⟶ B) (h : c ≫ t = s)
    (b : (Δ[0] : SSet.{u}) ⟶ B) :
    endpointSameBaseMap c s t h b ≫ pullback.snd t b = pullback.snd s b := by
  exact (pullback.lift_snd _ _ _).trans (Category.comp_id _)

private theorem endpointSameBaseMap_eq_limitMap {E D B : SSet.{u}}
    (c : E ⟶ D) (s : E ⟶ B) (t : D ⟶ B) (h : c ≫ t = s)
    (b : (Δ[0] : SSet.{u}) ⟶ B) :
    endpointSameBaseMap c s t h b =
      lim.map (cospanHomMk (F := cospan s b) (G := cospan t b)
        (𝟙 B) c (𝟙 (Δ[0] : SSet.{u})) (by simpa using h.symm) (by simp)) := by
  apply pullback.hom_ext
  · rw [endpointSameBaseMap_fst]
    exact (limit.map_π
      (cospanHomMk (F := cospan s b) (G := cospan t b)
        (𝟙 B) c (𝟙 (Δ[0] : SSet.{u})) (by simpa using h.symm) (by simp))
      WalkingCospan.left).symm
  · rw [endpointSameBaseMap_snd]
    let a := cospanHomMk (F := cospan s b) (G := cospan t b)
      (𝟙 B) c (𝟙 (Δ[0] : SSet.{u})) (by simpa using h.symm) (by simp)
    have hr := (limit.map_π a WalkingCospan.right).symm
    change pullback.snd s b ≫ 𝟙 (Δ[0] : SSet.{u}) = lim.map a ≫ pullback.snd t b at hr
    simpa only [Category.comp_id] using hr

private theorem endpointSameBaseMap_weak {E D B : SSet.{u}}
    (c : E ⟶ D) (s : E ⟶ B) (t : D ⟶ B) (h : c ≫ t = s)
    [Fibration s] [Fibration t]
    (hc : realizationWeakEquivalences c) (b : (Δ[0] : SSet.{u}) ⟶ B) :
    realizationWeakEquivalences (endpointSameBaseMap c s t h b) := by
  let _ : ModelCategory SSet.{u} := modelCategoryQuillen.modelCategory
  let _ : WeakEquivalence c := (weakEquivalence_iff c).mpr hc
  let F := cospan s b
  let G := cospan t b
  let a : F ⟶ G := cospanHomMk (𝟙 B) c (𝟙 (Δ[0] : SSet.{u}))
    (by change s ≫ 𝟙 B = c ≫ t; simpa using h.symm)
    (by change b ≫ 𝟙 B = 𝟙 (Δ[0] : SSet.{u}) ≫ b; simp)
  let _ : Fibration (F.map WalkingCospan.Hom.inl) := by change Fibration s; infer_instance
  let _ : Fibration (G.map WalkingCospan.Hom.inl) := by change Fibration t; infer_instance
  have hw : WeakEquivalence (lim.map a) :=
    weakEquivalence_limitMap_of_rightProper_inl a (by
      rintro (_ | _ | _)
      · change WeakEquivalence (𝟙 B); infer_instance
      · change WeakEquivalence c; infer_instance
      · change WeakEquivalence (𝟙 (Δ[0] : SSet.{u})); infer_instance)
  rw [endpointSameBaseMap_eq_limitMap]
  exact (weakEquivalence_iff _).mp hw


private def endpointNativeFibreIso {E B : SSet.{u}} (s : E ⟶ B) (b : B _⦋0⦌) :
    (Subcomplex.fiber s b : SSet.{u}) ≅ pullback s (const (X := Δ[0]) b) :=
  (Subcomplex.fiber_isPullback s b).isoIsPullback _ _
    (IsPullback.of_hasPullback s (const (X := Δ[0]) b))

@[reassoc]
private theorem endpointNativeFibreIso_hom_fst {E B : SSet.{u}}
    (s : E ⟶ B) (b : B _⦋0⦌) :
    (endpointNativeFibreIso s b).hom ≫ pullback.fst s (const (X := Δ[0]) b) =
      (Subcomplex.fiber s b).ι :=
  IsPullback.isoIsPullback_hom_fst _ _ (Subcomplex.fiber_isPullback s b)
    (IsPullback.of_hasPullback s (const (X := Δ[0]) b))

@[reassoc]
private theorem endpointNativeFibreIso_inv_fst {E B : SSet.{u}}
    (s : E ⟶ B) (b : B _⦋0⦌) :
    (endpointNativeFibreIso s b).inv ≫ (Subcomplex.fiber s b).ι =
      pullback.fst s (const (X := Δ[0]) b) :=
  IsPullback.isoIsPullback_inv_fst _ _ (Subcomplex.fiber_isPullback s b)
    (IsPullback.of_hasPullback s (const (X := Δ[0]) b))

private def endpointNativeFibreArrowIso {E D B : SSet.{u}}
    (c : E ⟶ D) (s : E ⟶ B) (t : D ⟶ B) (h : c ≫ t = s) (b : B _⦋0⦌) :
    Arrow.mk (Subcomplex.mapFiber (f := s) (f' := t) c (𝟙 B)
      (h.trans (Category.comp_id s).symm) (y := b) (y' := b) rfl) ≅
      Arrow.mk (endpointSameBaseMap c s t h (const (X := Δ[0]) b)) := by
  refine Arrow.isoMk (endpointNativeFibreIso s b) (endpointNativeFibreIso t b) ?_
  change (endpointNativeFibreIso s b).hom ≫
      endpointSameBaseMap c s t h (const (X := Δ[0]) b) =
    Subcomplex.mapFiber (f := s) (f' := t) c (𝟙 B)
      (h.trans (Category.comp_id s).symm) (y := b) (y' := b) rfl ≫
        (endpointNativeFibreIso t b).hom
  apply pullback.hom_ext
  · simp only [Category.assoc, endpointSameBaseMap_fst,
      endpointNativeFibreIso_hom_fst_assoc, endpointNativeFibreIso_hom_fst,
      Subcomplex.mapFiber_ι]
  · exact stdSimplex.isTerminalObj₀.hom_ext _ _

private theorem endpointFibration_weak_iff {E D B : SSet.{u}}
    (p : E ⟶ D) (s : E ⟶ B) (t : D ⟶ B) (h : p ≫ t = s)
    [Fibration p] [Fibration t] :
    realizationWeakEquivalences p ↔
      ∀ b : B _⦋0⦌, realizationWeakEquivalences
        (endpointSameBaseMap p s t h (const (X := Δ[0]) b)) := by
  rw [realizationWeakEquivalence_iff_fibrewise_of_fibrations p s t h]
  apply forall_congr'
  intro b
  exact realizationWeakEquivalences.arrow_mk_iso_iff (endpointNativeFibreArrowIso p s t h b)

private theorem endpointSameBaseMap_comp {E M D B : SSet.{u}}
    (i : E ⟶ M) (p : M ⟶ D) (c : E ⟶ D)
    (s : E ⟶ B) (m : M ⟶ B) (t : D ⟶ B)
    (hi : i ≫ m = s) (hp : p ≫ t = m) (hc : c ≫ t = s) (fac : i ≫ p = c)
    (b : (Δ[0] : SSet.{u}) ⟶ B) :
    endpointSameBaseMap i s m hi b ≫ endpointSameBaseMap p m t hp b =
      endpointSameBaseMap c s t hc b := by
  apply pullback.hom_ext
  · simp only [Category.assoc, endpointSameBaseMap_fst,
      endpointSameBaseMap_fst_assoc, fac]
  · simp only [Category.assoc, endpointSameBaseMap_snd]

private theorem endpointArbitraryMap_weak_iff {E D B : SSet.{u}}
    (c : E ⟶ D) (s : E ⟶ B) (t : D ⟶ B) (h : c ≫ t = s)
    [Fibration s] [Fibration t] :
    realizationWeakEquivalences c ↔
      ∀ b : B _⦋0⦌, realizationWeakEquivalences
        (endpointSameBaseMap c s t h (const (X := Δ[0]) b)) := by
  let _ : ModelCategory SSet.{u} := modelCategoryQuillen.modelCategory
  let d := MorphismProperty.factorizationData
    (trivialCofibrations SSet.{u}) (fibrations SSet.{u}) c
  let m := d.p ≫ t
  let _ : Fibration d.p := (fibration_iff d.p).mpr d.hp
  let _ : Fibration m := by dsimp only [m]; infer_instance
  let _ : WeakEquivalence d.i := ((mem_trivialCofibrations_iff d.i).mp d.hi).2
  have hi : realizationWeakEquivalences d.i := (weakEquivalence_iff d.i).mp inferInstance
  have his : d.i ≫ m = s := by rw [← h]; dsimp only [m]; rw [← Category.assoc, d.fac]
  have hcomp (b : B _⦋0⦌) :
      endpointSameBaseMap d.i s m his (const (X := Δ[0]) b) ≫
          endpointSameBaseMap d.p m t rfl (const (X := Δ[0]) b) =
        endpointSameBaseMap c s t h (const (X := Δ[0]) b) :=
    endpointSameBaseMap_comp d.i d.p c s m t his rfl h d.fac _
  constructor
  · intro hc b
    have hp : realizationWeakEquivalences d.p :=
      realizationWeakEquivalences.of_precomp d.i d.p hi (by simpa only [d.fac] using hc)
    have hpb := (endpointFibration_weak_iff d.p m t rfl).mp hp b
    have hib := endpointSameBaseMap_weak d.i s m his hi (const (X := Δ[0]) b)
    rw [← hcomp b]
    exact realizationWeakEquivalences.comp_mem _ _ hib hpb
  · intro hf
    have hp : realizationWeakEquivalences d.p := (endpointFibration_weak_iff d.p m t rfl).mpr (by
      intro b
      have hib := endpointSameBaseMap_weak d.i s m his hi (const (X := Δ[0]) b)
      exact realizationWeakEquivalences.of_precomp _ _ hib (by rw [hcomp b]; exact hf b))
    simpa only [d.fac] using realizationWeakEquivalences.comp_mem d.i d.p hi hp

private theorem endpointArbitraryMap_weak_iff_pointMap {E D B : SSet.{u}}
    (c : E ⟶ D) (s : E ⟶ B) (t : D ⟶ B) (h : c ≫ t = s)
    [Fibration s] [Fibration t] :
    realizationWeakEquivalences c ↔
      ∀ b : (Δ[0] : SSet.{u}) ⟶ B, realizationWeakEquivalences
        (endpointSameBaseMap c s t h b) := by
  rw [endpointArbitraryMap_weak_iff c s t h]
  constructor
  · intro hf b
    obtain ⟨b₀, rfl⟩ : ∃ b₀ : B _⦋0⦌, const (X := Δ[0]) b₀ = b := by
      refine ⟨yonedaEquiv b, ?_⟩
      rw [← yonedaEquiv_symm_zero]
      exact yonedaEquiv.symm_apply_apply b
    exact hf b₀
  · intro hf b
    exact hf (const (X := Δ[0]) b)

end SSet

namespace SSet

/-- An arbitrary original map between fibrations over one base is weak exactly
when all its same-base chosen pullback fibre maps are weak. No fibration
hypothesis is imposed on the comparison map itself. -/
theorem realizationWeakEquivalence_iff_pullbackFibrewise_of_base_fibrations
    {E D B : SSet.{u}} (c : E ⟶ D) (s : E ⟶ B) (t : D ⟶ B)
    (h : c ≫ t = s) [Fibration s] [Fibration t] :
    realizationWeakEquivalences c ↔
      ∀ b : (Δ[0] : SSet.{u}) ⟶ B, realizationWeakEquivalences
        (pullback.map s b t b c (𝟙 _) (𝟙 _)
          (by simpa using h.symm) (by simp)) := by
  simpa only [endpointSameBaseMap] using
    (endpointArbitraryMap_weak_iff_pointMap c s t h)

end SSet
