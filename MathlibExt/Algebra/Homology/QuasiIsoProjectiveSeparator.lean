/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Copyright (c) 2026 Tsutomu Okano. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tsutomu Okano
-/
module

public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Generator.Basic
public import Mathlib.CategoryTheory.Preadditive.LiftToFinset
public import Mathlib.CategoryTheory.Presentable.Finite

/-!
# Quasi-isomorphisms detected by projective separating families

This file gives a criterion for a degreewise monomorphism of homological
complexes to be a quasi-isomorphism when sufficiently many iterates factor
maps from a projective separating family through it.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe v u w

namespace CategoryTheory

/-- A map from a finitely presentable object into a coproduct factors through
a finite subcoproduct. -/
theorem IsFinitelyPresentable.exists_factor_through_finiteSubcoproduct
    {C : Type u} [Category.{v} C] [HasFiniteCoproducts C] [HasCoequalizers C]
    {α : Type w} [HasCoproducts.{w} C]
    (G : C) [IsFinitelyPresentable.{w} G]
    (f : α → C) [HasCoproduct f] (x : G ⟶ ∐ f) :
    ∃ (S : Finset (Discrete α))
      (y : G ⟶ (CoproductsFromFiniteFiltered.liftToFinsetObj
        (Discrete.functor f)).obj S),
      y ≫ (CoproductsFromFiniteFiltered.finiteSubcoproductsCocone f).ι.app S = x := by
  let _ : HasColimitsOfSize.{w, w} C :=
    has_colimits_of_hasCoequalizers_and_coproducts
  exact IsFinitelyPresentable.exists_hom_of_isColimit
    (CoproductsFromFiniteFiltered.isColimitFiniteSubproductsCocone f) x

end CategoryTheory

namespace HomologicalComplex

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {ι κ : Type*} {c : ComplexShape ι}
variable {K L : HomologicalComplex C c}

/-- A degreewise monomorphism is a quasi-isomorphism when homologically trivial
iterates eventually factor every map from a projective separating family. -/
theorem quasiIso_of_eventually_factors_through_projective_separating
    (f : K ⟶ L) [∀ i, Mono (f.f i)]
    [∀ i, K.HasHomology i] [∀ i, L.HasHomology i]
    (P : ObjectProperty C) (hP : P.IsSeparating)
    (hprojective : ∀ G, P G → Projective G)
    (s : κ → (K ⟶ K)) (t : κ → (L ⟶ L))
    (hs : ∀ k i, homologyMap (s k) i = 𝟙 _)
    (ht : ∀ k i, homologyMap (t k) i = 𝟙 _)
    (hcompat : ∀ k, s k ≫ f = f ≫ t k)
    (hfactor : ∀ (G : C), P G → ∀ i (x : G ⟶ L.X i),
      ∃ k, ∃ y : G ⟶ K.X i, y ≫ f.f i = x ≫ (t k).f i) : QuasiIso f := by
  rw [quasiIso_iff]
  intro i
  rw [quasiIsoAt_iff_isIso_homologyMap]
  apply hP.isDetecting
  intro G hG x
  let _ : Projective G := hprojective G hG
  let z : G ⟶ L.cycles i := Projective.factorThru x (L.homologyπ i)
  have hz : z ≫ L.homologyπ i = x := Projective.factorThru_comp _ _
  obtain ⟨k, y, hy⟩ := hfactor G hG i (z ≫ L.iCycles i)
  have hycycle : y ≫ K.d i (c.next i) = 0 := by
    apply (cancel_mono (f.f (c.next i))).mp
    calc
      (y ≫ K.d i (c.next i)) ≫ f.f (c.next i) =
          (y ≫ f.f i) ≫ L.d i (c.next i) := by
            simpa only [Category.assoc] using
              congrArg (fun q => y ≫ q) (f.comm i (c.next i)).symm
      _ = ((z ≫ L.iCycles i) ≫ (t k).f i) ≫ L.d i (c.next i) := by
            simpa only [Category.assoc] using
              congrArg (fun q => q ≫ L.d i (c.next i)) hy
      _ = (z ≫ L.iCycles i) ≫ L.d i (c.next i) ≫ (t k).f (c.next i) := by
            simpa only [Category.assoc] using
              congrArg (fun q => (z ≫ L.iCycles i) ≫ q) ((t k).comm i (c.next i))
      _ = 0 ≫ f.f (c.next i) := by
            simpa only [Category.assoc, zero_comp, comp_zero] using congrArg
              (fun q => z ≫ q ≫ (t k).f (c.next i)) (L.iCycles_d i (c.next i))
  let ycycles : G ⟶ K.cycles i := K.liftCycles y (c.next i) rfl hycycle
  have hycycles : ycycles ≫ cyclesMap f i = z ≫ cyclesMap (t k) i := by
    apply (cancel_mono (L.iCycles i)).mp
    rw [Category.assoc, cyclesMap_i, ← Category.assoc, K.liftCycles_i,
      Category.assoc, cyclesMap_i]
    simpa only [Category.assoc] using hy
  let yhom : G ⟶ K.homology i := ycycles ≫ K.homologyπ i
  have hyhom : yhom ≫ homologyMap f i = x := by
    dsimp [yhom]
    rw [Category.assoc, homologyπ_naturality, ← Category.assoc, hycycles,
      Category.assoc, ← homologyπ_naturality, ← Category.assoc, hz,
      ht, Category.comp_id]
  refine ⟨yhom, hyhom, ?_⟩
  intro y' hy'
  have hdifference : (y' - yhom) ≫ homologyMap f i = 0 := by
    rw [Preadditive.sub_comp, hy', hyhom, sub_self]
  let z' : G ⟶ K.cycles i := Projective.factorThru (y' - yhom) (K.homologyπ i)
  have hz' : z' ≫ K.homologyπ i = y' - yhom := Projective.factorThru_comp _ _
  have hz'fπ : z' ≫ cyclesMap f i ≫ L.homologyπ i = 0 := by
    calc
      z' ≫ cyclesMap f i ≫ L.homologyπ i =
          z' ≫ K.homologyπ i ≫ homologyMap f i := by
            rw [← homologyπ_naturality]
      _ = 0 := by rw [← Category.assoc, hz', hdifference]
  let S : ShortComplex C :=
    ShortComplex.mk (L.toCycles (c.prev i) i) (L.homologyπ i)
      (L.toCycles_comp_homologyπ (c.prev i) i)
  have hS : S.Exact :=
    S.exact_of_g_is_cokernel (L.homologyIsCokernel (c.prev i) i rfl)
  have hz'fπ' : (z' ≫ cyclesMap f i) ≫ S.g = 0 := by simpa [S] using hz'fπ
  let b : G ⟶ L.X (c.prev i) := hS.liftFromProjective (z' ≫ cyclesMap f i) hz'fπ'
  have hb : b ≫ L.toCycles (c.prev i) i = z' ≫ cyclesMap f i := by
    exact hS.liftFromProjective_comp (z' ≫ cyclesMap f i) hz'fπ'
  obtain ⟨k, a, ha⟩ := hfactor G hG (c.prev i) b
  have hboundary : z' ≫ cyclesMap (s k) i = a ≫ K.toCycles (c.prev i) i := by
    apply (cancel_mono (K.iCycles i)).mp
    apply (cancel_mono (f.f i)).mp
    simp only [Category.assoc]
    have hcompat_i : (s k).f i ≫ f.f i = f.f i ≫ (t k).f i := by
      simpa only [HomologicalComplex.comp_f] using
        congrArg (fun q : K ⟶ L => q.f i) (hcompat k)
    calc
      z' ≫ cyclesMap (s k) i ≫ K.iCycles i ≫ f.f i =
          z' ≫ K.iCycles i ≫ (s k).f i ≫ f.f i := by
            simpa only [Category.assoc] using congrArg
              (fun q => (z' ≫ q) ≫ f.f i) (cyclesMap_i (s k) i)
      _ = (z' ≫ K.iCycles i) ≫ f.f i ≫ (t k).f i := by
            simpa only [Category.assoc] using
              congrArg (fun q => (z' ≫ K.iCycles i) ≫ q) hcompat_i
      _ = (z' ≫ cyclesMap f i) ≫ L.iCycles i ≫ (t k).f i := by
            simpa only [Category.assoc] using congrArg
              (fun q => (z' ≫ q) ≫ (t k).f i) (cyclesMap_i f i).symm
      _ = (b ≫ L.toCycles (c.prev i) i) ≫ L.iCycles i ≫ (t k).f i := by
            simpa only [Category.assoc] using congrArg
              (fun q => q ≫ L.iCycles i ≫ (t k).f i) hb.symm
      _ = (b ≫ L.d (c.prev i) i) ≫ (t k).f i := by
            simpa only [Category.assoc] using congrArg
              (fun q => b ≫ q ≫ (t k).f i) (L.toCycles_i (c.prev i) i)
      _ = (b ≫ (t k).f (c.prev i)) ≫ L.d (c.prev i) i := by
            simpa only [Category.assoc] using congrArg
              (fun q => b ≫ q) ((t k).comm (c.prev i) i).symm
      _ = (a ≫ f.f (c.prev i)) ≫ L.d (c.prev i) i := by
            simpa only [Category.assoc] using
              congrArg (fun q => q ≫ L.d (c.prev i) i) ha.symm
      _ = a ≫ K.d (c.prev i) i ≫ f.f i := by
            simpa only [Category.assoc] using
              congrArg (fun q => a ≫ q) (f.comm (c.prev i) i)
      _ = a ≫ K.toCycles (c.prev i) i ≫ K.iCycles i ≫ f.f i := by
            simpa only [Category.assoc] using congrArg
              (fun q => (a ≫ q) ≫ f.f i) (K.toCycles_i (c.prev i) i).symm
  apply sub_eq_zero.mp
  rw [← hz']
  calc
    z' ≫ K.homologyπ i = z' ≫ K.homologyπ i ≫ homologyMap (s k) i := by
      rw [hs, Category.comp_id]
    _ = z' ≫ cyclesMap (s k) i ≫ K.homologyπ i := by
      rw [← homologyπ_naturality]
    _ = a ≫ K.toCycles (c.prev i) i ≫ K.homologyπ i := by
      simpa only [Category.assoc] using
        congrArg (fun q => q ≫ K.homologyπ i) hboundary
    _ = 0 := by rw [K.toCycles_comp_homologyπ, comp_zero]

/-- The singleton-separator form of
`quasiIso_of_eventually_factors_through_projective_separating`. -/
theorem quasiIso_of_eventually_factors_through_projective_separator
    (f : K ⟶ L) [∀ i, Mono (f.f i)]
    [∀ i, K.HasHomology i] [∀ i, L.HasHomology i]
    (G : C) [Projective G] (hG : IsSeparator G)
    (s : κ → (K ⟶ K)) (t : κ → (L ⟶ L))
    (hs : ∀ k i, homologyMap (s k) i = 𝟙 _)
    (ht : ∀ k i, homologyMap (t k) i = 𝟙 _)
    (hcompat : ∀ k, s k ≫ f = f ≫ t k)
    (hfactor : ∀ i (x : G ⟶ L.X i),
      ∃ k, ∃ y : G ⟶ K.X i, y ≫ f.f i = x ≫ (t k).f i) : QuasiIso f := by
  apply quasiIso_of_eventually_factors_through_projective_separating f
    (.singleton G) hG (s := s) (t := t)
  · intro H hH
    rw [ObjectProperty.singleton_iff] at hH
    subst H
    infer_instance
  · exact hs
  · exact ht
  · exact hcompat
  · intro H hH
    rw [ObjectProperty.singleton_iff] at hH
    subst H
    exact hfactor

end HomologicalComplex
