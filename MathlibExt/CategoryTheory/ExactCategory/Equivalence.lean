/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.CategoryTheory.ExactCategory.Basic

import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels
import Mathlib.CategoryTheory.Preadditive.Transfer
import MathlibExt.CategoryTheory.ExactCategory.MorphismProperty
import MathlibExt.CategoryTheory.ExactCategory.Split

/-!
# Transporting exact structures along equivalences

An additive equivalence transports an exact structure from its target back to
its source.  Admissible exact sequences are those whose images are
admissible.  Kernel, cokernel, pushout, and pullback witnesses are reflected
through the equivalence; no arbitrary limits or colimits are assumed.

The construction is a definition rather than a global instance, since an
additive category can carry more than one exact structure.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits Preadditive

universe v v' u u'

namespace CategoryTheory

namespace ExactCategory

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C]
variable {D : Type u'} [Category.{v'} D] [Preadditive D]
  [HasZeroObject D] [HasBinaryBiproducts D] [ExactCategory D]

/-- The predicate on short complexes pulled back along an additive
equivalence. -/
@[no_expose]
abbrev transportedAdmissibleExact (e : C ≌ D)
    (S : ShortComplex C) : Prop :=
  ExactCategory.IsAdmissibleExact (S.map e.functor)

@[no_expose]
noncomputable def reflectKernelFork
    (e : C ≌ D) [e.functor.Additive]
    {S : ShortComplex C}
    (h : IsLimit (KernelFork.ofι (S.map e.functor).f
      (S.map e.functor).zero)) :
    IsLimit (KernelFork.ofι S.f S.zero) := by
  apply isLimitOfReflects e.functor
  exact (isLimitMapConeForkEquiv' e.functor S.zero).symm
    (by simpa using h)

@[no_expose]
noncomputable def reflectCokernelCofork
    (e : C ≌ D) [e.functor.Additive]
    {S : ShortComplex C}
    (h : IsColimit (CokernelCofork.ofπ (S.map e.functor).g
      (S.map e.functor).zero)) :
    IsColimit (CokernelCofork.ofπ S.g S.zero) := by
  apply isColimitOfReflects e.functor
  exact (isColimitMapCoconeCoforkEquiv'
    e.functor S.zero).symm (by simpa using h)

set_option linter.defProp false in
@[no_expose]
def transportedAdmissibleMono_iff
    (e : C ≌ D) [e.functor.Additive]
    {X Y : C} (f : X ⟶ Y) :
    admissibleMonosOf C (transportedAdmissibleExact e) f ↔
      ExactCategory.IsAdmissibleMono (e.functor.map f) := by
  let F := e.functor
  let G := e.inverse
  let _ : G.Additive := e.inverse_additive
  constructor
  · rintro ⟨Z, p, w, hS⟩
    let S : ShortComplex C := ShortComplex.mk f p w
    change ExactCategory.IsAdmissibleExact (S.map F) at hS
    exact ⟨F.obj Z, (S.map F).g, (S.map F).zero, hS⟩
  · rintro ⟨W, p, w, hT⟩
    let q : Y ⟶ G.obj W := e.unitIso.hom.app Y ≫ G.map p
    have wq : f ≫ q = 0 := by
      calc
        f ≫ q = (f ≫ e.unitIso.hom.app Y) ≫ G.map p := by
          simp only [q, Category.assoc]
        _ = (e.unitIso.hom.app X ≫ G.map (F.map f)) ≫
            G.map p := by
          exact congrArg (· ≫ G.map p) (e.unitIso.hom.naturality f)
        _ = e.unitIso.hom.app X ≫ G.map (F.map f ≫ p) := by
          simp only [Category.assoc, G.map_comp]
        _ = 0 := by rw [w, G.map_zero, comp_zero]
    let S : ShortComplex C := ShortComplex.mk f q wq
    let T : ShortComplex D := ShortComplex.mk (F.map f) p w
    have hMap : S.map F ≅ T :=
      ShortComplex.isoMk (Iso.refl _) (Iso.refl _)
        (e.counitIso.app W)
        (by simp [S, T])
        (by
          dsimp [S, T]
          calc
            𝟙 _ ≫ p = (F.map (e.unitIso.hom.app Y) ≫
                e.counitIso.hom.app (F.obj Y)) ≫ p := by
              exact congrArg (· ≫ p) (e.functor_unitIso_comp Y).symm
            _ = F.map (e.unitIso.hom.app Y) ≫
                (e.counitIso.hom.app (F.obj Y) ≫ p) :=
              Category.assoc _ _ _
            _ = F.map (e.unitIso.hom.app Y) ≫
                (F.map (G.map p) ≫ e.counitIso.hom.app W) := by
              exact congrArg (F.map (e.unitIso.hom.app Y) ≫ ·)
                (e.counitIso.hom.naturality p).symm
            _ = F.map q ≫ e.counitIso.hom.app W := by
              simp only [q, F.map_comp, Category.assoc])
    refine ⟨G.obj W, q, wq, ?_⟩
    exact ExactCategory.isAdmissibleExact_of_iso hMap.symm hT

set_option linter.defProp false in
@[no_expose]
def transportedAdmissibleEpi_iff
    (e : C ≌ D) [e.functor.Additive]
    {X Y : C} (f : X ⟶ Y) :
    admissibleEpisOf C (transportedAdmissibleExact e) f ↔
      ExactCategory.IsAdmissibleEpi (e.functor.map f) := by
  let F := e.functor
  let G := e.inverse
  let _ : G.Additive := e.inverse_additive
  constructor
  · rintro ⟨Z, i, w, hS⟩
    let S : ShortComplex C := ShortComplex.mk i f w
    change ExactCategory.IsAdmissibleExact (S.map F) at hS
    exact ⟨F.obj Z, (S.map F).f, (S.map F).zero, hS⟩
  · rintro ⟨W, i, w, hT⟩
    let j : G.obj W ⟶ X := G.map i ≫ e.unitIso.inv.app X
    have wj : j ≫ f = 0 := by
      calc
        j ≫ f = G.map i ≫ (e.unitIso.inv.app X ≫ f) := by
          simp only [j, Category.assoc]
        _ = G.map i ≫
            (G.map (F.map f) ≫ e.unitIso.inv.app Y) := by
          exact congrArg (G.map i ≫ ·)
            (e.unitIso.inv.naturality f).symm
        _ = G.map (i ≫ F.map f) ≫ e.unitIso.inv.app Y := by
          simp only [← Category.assoc, G.map_comp]
        _ = 0 := by rw [w, G.map_zero, zero_comp]
    let S : ShortComplex C := ShortComplex.mk j f wj
    let T : ShortComplex D := ShortComplex.mk i (F.map f) w
    have hTriangle : e.counitIso.hom.app (F.obj X) =
        F.map (e.unitIso.inv.app X) := by
      change e.counitIso.hom.app (e.functor.obj X) =
        e.functor.map (e.unitIso.inv.app X)
      apply (cancel_epi (e.functor.map (e.unitIso.hom.app X))).mp
      exact (e.functor_unitIso_comp X).trans
        (e.functor.mapIso (e.unitIso.app X)).hom_inv_id.symm
    have hMap : S.map F ≅ T :=
      ShortComplex.isoMk (e.counitIso.app W)
        (Iso.refl _) (Iso.refl _)
        (by
          dsimp [S, T]
          calc
            e.counitIso.hom.app W ≫ i =
                F.map (G.map i) ≫
                  e.counitIso.hom.app (F.obj X) :=
              (e.counitIso.hom.naturality i).symm
            _ = F.map (G.map i) ≫
                F.map (e.unitIso.inv.app X) := by rw [hTriangle]
            _ = F.map j ≫ 𝟙 _ := by
              simp only [j, F.map_comp, Category.comp_id])
        (by simp [S, T])
    refine ⟨G.obj W, j, wj, ?_⟩
    exact ExactCategory.isAdmissibleExact_of_iso hMap.symm hT

/-- Pull an exact structure back along an additive categorical equivalence.

This declaration does not install a global instance. -/
@[instance_reducible]
noncomputable def ofEquivalence
    (e : C ≌ D) [e.functor.Additive] : ExactCategory C := by
  let F := e.functor
  let G := e.inverse
  let _ : G.Additive := e.inverse_additive
  let P : ShortComplex C → Prop := transportedAdmissibleExact e
  have mono_iff {X Y : C} (f : X ⟶ Y) :
      admissibleMonosOf C P f ↔
        ExactCategory.IsAdmissibleMono (F.map f) :=
    transportedAdmissibleMono_iff e f
  have epi_iff {X Y : C} (f : X ⟶ Y) :
      admissibleEpisOf C P f ↔
        ExactCategory.IsAdmissibleEpi (F.map f) :=
    transportedAdmissibleEpi_iff e f
  exact
    { IsAdmissibleExact := P
      shortExact_of_isAdmissibleExact := by
        intro S hS
        change ExactCategory.IsAdmissibleExact (S.map F) at hS
        have hMap : (S.map F).ShortExact :=
          ExactCategory.shortExact_of_isAdmissibleExact hS
        have hBack : ((S.map F).map G).ShortExact :=
          hMap.map_of_exact G
        let eUnit : S ≅ (S.map F).map G :=
          ShortComplex.isoMk (e.unitIso.app S.X₁)
            (e.unitIso.app S.X₂) (e.unitIso.app S.X₃)
            (e.unitIso.hom.naturality S.f).symm
            (e.unitIso.hom.naturality S.g).symm
        exact ShortComplex.shortExact_of_iso eUnit.symm hBack
      isLimit_kernelFork := by
        intro S hS
        change ExactCategory.IsAdmissibleExact (S.map F) at hS
        exact ⟨reflectKernelFork e
          (ExactCategory.isLimit_kernelFork_of_isAdmissibleExact hS)⟩
      isColimit_cokernelCofork := by
        intro S hS
        change ExactCategory.IsAdmissibleExact (S.map F) at hS
        exact ⟨reflectCokernelCofork e
          (ExactCategory.isColimit_cokernelCofork_of_isAdmissibleExact hS)⟩
      isAdmissibleExact_of_iso := by
        intro S T hST hS
        change ExactCategory.IsAdmissibleExact (S.map F) at hS
        change ExactCategory.IsAdmissibleExact (T.map F)
        exact ExactCategory.isAdmissibleExact_of_iso
          (F.mapShortComplex.mapIso hST) hS
      isAdmissibleExact_split := by
        intro X Y
        change ExactCategory.IsAdmissibleExact
          ((ShortComplex.mk (biprod.inl : X ⟶ X ⊞ Y)
            biprod.snd (by simp)).map F)
        exact ExactCategory.isAdmissibleExact_of_splitting
          ((ShortComplex.Splitting.ofHasBinaryBiproduct X Y).map F)
      admissibleMono_comp := by
        constructor
        intro X Y Z f g hf hg
        apply (mono_iff (f ≫ g)).mpr
        rw [F.map_comp]
        exact ExactCategory.admissibleMono_comp.comp_mem _ _
          ((mono_iff f).mp hf) ((mono_iff g).mp hg)
      admissibleEpi_comp := by
        constructor
        intro X Y Z f g hf hg
        apply (epi_iff (f ≫ g)).mpr
        rw [F.map_comp]
        exact ExactCategory.admissibleEpi_comp.comp_mem _ _
          ((epi_iff f).mp hf) ((epi_iff g).mp hg)
      admissibleMono_pushout := by
        intro X Y i hi X' f
        obtain ⟨Q, inl, inr, sq, hinl⟩ :=
          ExactCategory.admissibleMono_pushout
            (F.obj X) (F.obj Y) (F.map i) ((mono_iff i).mp hi)
            (F.obj X') (F.map f)
        let inlC : X' ⟶ G.obj Q :=
          e.unitIso.hom.app X' ≫ G.map inl
        let inrC : Y ⟶ G.obj Q :=
          e.unitIso.hom.app Y ≫ G.map inr
        have sqG : IsPushout (G.map (F.map f)) (G.map (F.map i))
            (G.map inl) (G.map inr) := Functor.map_isPushout G sq
        have sqC : IsPushout f i inlC inrC := by
          exact sqG.of_iso (e.unitIso.app X).symm
            (e.unitIso.app X').symm (e.unitIso.app Y).symm
            (Iso.refl _) (e.unitIso.inv.naturality f)
            (e.unitIso.inv.naturality i)
            (by simp [inlC]) (by simp [inrC])
        have hinlMap : ExactCategory.IsAdmissibleMono (F.map inlC) := by
          have heq : F.map inlC ≫ e.counitIso.hom.app Q = inl := by
            change F.map (e.unitIso.hom.app X' ≫ G.map inl) ≫
              e.counitIso.hom.app Q = inl
            calc
              _ = F.map (e.unitIso.hom.app X') ≫
                  (F.map (G.map inl) ≫ e.counitIso.hom.app Q) := by
                simp only [F.map_comp, Category.assoc]
              _ = F.map (e.unitIso.hom.app X') ≫
                  (e.counitIso.hom.app (F.obj X') ≫ inl) := by
                exact congrArg (F.map (e.unitIso.hom.app X') ≫ ·)
                  (e.counitIso.hom.naturality inl)
              _ = (F.map (e.unitIso.hom.app X') ≫
                  e.counitIso.hom.app (F.obj X')) ≫ inl := by
                rw [Category.assoc]
              _ = inl := by
                simpa only [Category.id_comp] using congrArg (· ≫ inl)
                  (e.functor_unitIso_comp X')
          have hcomp : ExactCategory.IsAdmissibleMono
              (F.map inlC ≫ e.counitIso.hom.app Q) := by
            rw [heq]
            exact hinl
          exact ((admissibleMonosOf D
            ExactCategory.IsAdmissibleExact).cancel_right_of_respectsIso
              (F.map inlC) (e.counitIso.hom.app Q)).mp hcomp
        exact ⟨G.obj Q, inlC, inrC, sqC, (mono_iff inlC).mpr hinlMap⟩
      admissibleEpi_pullback := by
        intro Y Z p hp Z' g
        obtain ⟨Q, fst, snd, sq, hfst⟩ :=
          ExactCategory.admissibleEpi_pullback
            (F.obj Y) (F.obj Z) (F.map p) ((epi_iff p).mp hp)
            (F.obj Z') (F.map g)
        let fstC : G.obj Q ⟶ Z' :=
          G.map fst ≫ e.unitIso.inv.app Z'
        let sndC : G.obj Q ⟶ Y :=
          G.map snd ≫ e.unitIso.inv.app Y
        have sqG : IsPullback (G.map fst) (G.map snd)
            (G.map (F.map g)) (G.map (F.map p)) :=
          Functor.map_isPullback G sq
        have sqC : IsPullback fstC sndC g p := by
          exact sqG.of_iso (Iso.refl _) (e.unitIso.app Z').symm
            (e.unitIso.app Y).symm (e.unitIso.app Z).symm
            (by simp [fstC]) (by simp [sndC])
            (e.unitIso.inv.naturality g)
            (e.unitIso.inv.naturality p)
        have hfstMap : ExactCategory.IsAdmissibleEpi (F.map fstC) := by
          have heq : e.counitIso.inv.app Q ≫ F.map fstC = fst := by
            change e.counitIso.inv.app Q ≫
              F.map (G.map fst ≫ e.unitIso.inv.app Z') = fst
            calc
              _ = (e.counitIso.inv.app Q ≫ F.map (G.map fst)) ≫
                  F.map (e.unitIso.inv.app Z') := by
                simp only [F.map_comp, Category.assoc]
              _ = (fst ≫ e.counitIso.inv.app (F.obj Z')) ≫
                  F.map (e.unitIso.inv.app Z') := by
                exact congrArg (· ≫ F.map (e.unitIso.inv.app Z'))
                  (e.counitIso.inv.naturality fst).symm
              _ = fst ≫ (e.counitIso.inv.app (F.obj Z') ≫
                  F.map (e.unitIso.inv.app Z')) := by
                rw [Category.assoc]
              _ = fst ≫ 𝟙 _ := by
                exact congrArg (fst ≫ ·) (e.counitInv_functor_comp Z')
              _ = fst := Category.comp_id _
          have hcomp : ExactCategory.IsAdmissibleEpi
              (e.counitIso.inv.app Q ≫ F.map fstC) := by
            rw [heq]
            exact hfst
          exact ((admissibleEpisOf D
            ExactCategory.IsAdmissibleExact).cancel_left_of_respectsIso
              (e.counitIso.inv.app Q) (F.map fstC)).mp hcomp
        exact ⟨G.obj Q, fstC, sndC, sqC, (epi_iff fstC).mpr hfstMap⟩ }

/-- Under the exact structure transported along an additive equivalence, a
short complex is admissible exact exactly when its image is. -/
theorem ofEquivalence_isAdmissibleExact_iff
    (e : C ≌ D) [e.functor.Additive] (S : ShortComplex C) :
    letI : ExactCategory C := ofEquivalence e
    ExactCategory.IsAdmissibleExact S ↔
      ExactCategory.IsAdmissibleExact (S.map e.functor) :=
  Iff.rfl

/-- Characterization of admissible monos under the transported exact
structure. -/
theorem ofEquivalence_isAdmissibleMono_iff
    (e : C ≌ D) [e.functor.Additive] {X Y : C} (f : X ⟶ Y) :
    letI : ExactCategory C := ofEquivalence e
    ExactCategory.IsAdmissibleMono f ↔
      ExactCategory.IsAdmissibleMono (e.functor.map f) :=
  transportedAdmissibleMono_iff e f

/-- Characterization of admissible epis under the transported exact
structure. -/
theorem ofEquivalence_isAdmissibleEpi_iff
    (e : C ≌ D) [e.functor.Additive] {X Y : C} (f : X ⟶ Y) :
    letI : ExactCategory C := ofEquivalence e
    ExactCategory.IsAdmissibleEpi f ↔
      ExactCategory.IsAdmissibleEpi (e.functor.map f) :=
  transportedAdmissibleEpi_iff e f

end ExactCategory

end CategoryTheory

end
