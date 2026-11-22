/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.FreePathCompletionNerveWeak
import MathlibExt.CategoryTheory.Category.RelativeFreePresentation

/-!
# The actual completion unit on a full free-path presentation

A constructed full free-path presentation gives a genuine equivalence
with its original category. Its entire native groupoid completion is
compared using both actual inverse functors. The same original unit
commutes exactly with this comparison, so the proved free-path theorem
gives weakness of the actual original unit nerve.
-/

noncomputable section
universe u v z
open CategoryTheory

namespace CategoryTheory.RelativeWords.FreePresentation

section IndependentUniverses
variable {O : Type u} {C : Category.{v} O} (P : FreePresentation.{u,v,z} C)

/-- Read every actual original Hom by the full native path inverse. -/
def inverseMap {a b : O} : @Quiver.Hom O C.toQuiver a b → @Quiver.Path O P.quiver a b :=
  (Equiv.ofBijective (@P.map a b) (P.bijective a b)).symm

/-- The inverse keeps the SAME actual original identity. -/
theorem inverseMap_id (a : O) : inverseMap P (@CategoryStruct.id O C.toCategoryStruct a) =
    @Quiver.Path.nil O P.quiver a := by
  apply (P.bijective a a).1
  exact (Equiv.apply_symm_apply (Equiv.ofBijective (@P.map a a) (P.bijective a a)) _).trans
    (P.map_id a).symm

/-- The inverse keeps every SAME actual original composition. -/
theorem inverseMap_comp {a b d : O} (f : @Quiver.Hom O C.toQuiver a b)
    (g : @Quiver.Hom O C.toQuiver b d) :
    inverseMap P (@CategoryStruct.comp O C.toCategoryStruct a b d f g) =
      @Quiver.Path.comp O P.quiver a b d (inverseMap P f) (inverseMap P g) := by
  apply (P.bijective a d).1
  rw [P.map_comp]
  have hfg := Equiv.apply_symm_apply (Equiv.ofBijective (@P.map a d) (P.bijective a d))
    (@CategoryStruct.comp O C.toCategoryStruct a b d f g)
  have hf := Equiv.apply_symm_apply (Equiv.ofBijective (@P.map a b) (P.bijective a b)) f
  have hg := Equiv.apply_symm_apply (Equiv.ofBijective (@P.map b d) (P.bijective b d)) g
  exact hfg.trans (congrArg₂ (@CategoryStruct.comp O C.toCategoryStruct a b d) hf.symm hg.symm)

/-- The full actual original inverse presentation, on the same individual labels. -/
def inverse : @Functor O C (Paths O) (@Paths.categoryPaths O P.quiver) :=
  @Functor.mk O C (Paths O) (@Paths.categoryPaths O P.quiver) (fun a => a)
    (fun {_ _} f => inverseMap P f) (inverseMap_id P) (fun {_ _ _} f g => inverseMap_comp P f g)

/-- Both original full presentation functors recover every original native path. -/
theorem functor_inverse :
    @Functor.comp (Paths O) (@Paths.categoryPaths O P.quiver) O C (Paths O)
      (@Paths.categoryPaths O P.quiver) P.functor P.inverse =
      @Functor.id (Paths O) (@Paths.categoryPaths O P.quiver) :=
  @Functor.hext (Paths O) (@Paths.categoryPaths O P.quiver) (Paths O)
    (@Paths.categoryPaths O P.quiver) _ _ (fun _ => rfl)
    (fun a b p => heq_of_eq (Equiv.symm_apply_apply
      (Equiv.ofBijective (@P.map a b) (P.bijective a b)) p))

/-- Both original full presentation functors recover every actual original Hom. -/
theorem inverse_functor :
    @Functor.comp O C (Paths O) (@Paths.categoryPaths O P.quiver) O C P.inverse P.functor =
      @Functor.id O C :=
  @Functor.hext O C O C _ _ (fun _ => rfl)
    (fun a b f => heq_of_eq (Equiv.apply_symm_apply
      (Equiv.ofBijective (@P.map a b) (P.bijective a b)) f))

/-- The actual original free presentation is a genuine equivalence with both complete inverse functors. -/
def equivalence : @Equivalence (Paths O) O (@Paths.categoryPaths O P.quiver) C :=
  @Equivalence.mk (Paths O) (@Paths.categoryPaths O P.quiver) O C P.functor P.inverse
    (eqToIso (functor_inverse P).symm) (eqToIso (inverse_functor P))

/-- The actual original free presentation induces an equivalence of full native groupoid completions. -/
def completionEquivalence :
    @FreeGroupoid (Paths O) (@Paths.categoryPaths O P.quiver) ≌ @FreeGroupoid O C := by
  letI : Category.{v} O := C
  letI : Quiver.{z} O := P.quiver
  let F := FreeGroupoid.map P.functor
  let G := FreeGroupoid.map P.inverse
  have hF : F ⋙ G = 𝟭 _ := by
    rw [← FreeGroupoid.map_comp, functor_inverse, FreeGroupoid.map_id]
  have hG : G ⋙ F = 𝟭 _ := by
    rw [← FreeGroupoid.map_comp, inverse_functor, FreeGroupoid.map_id]
  exact Equivalence.mk F G (eqToIso hF.symm) (eqToIso hG)

end IndependentUniverses

universe a
variable {O : Type a} {C : Category.{a} O} (P : FreePresentation.{a,a,a} C)

include P in
/-- The SAME actual original unit nerve is weak for a full constructed free presentation. -/
theorem unit_nerve_weak :
    letI : Category.{a} O := C
    SSet.realizationWeakEquivalences (nerveMap (FreeGroupoid.of O)) := by
  let : Category.{a} O := C
  let : Quiver.{a} O := P.quiver
  let F := P.functor
  let ce := P.completionEquivalence
  let _ : F.IsEquivalence := P.equivalence.isEquivalence_functor
  let _ : (FreeGroupoid.map F).IsEquivalence := ce.isEquivalence_functor
  have hp : SSet.realizationWeakEquivalences (nerveMap F) :=
    nerveMap_mem_realizationWeakEquivalences_of_isEquivalence F
  have hc : SSet.realizationWeakEquivalences (nerveMap (FreeGroupoid.map F)) :=
    nerveMap_mem_realizationWeakEquivalences_of_isEquivalence _
  have hpath := FreePathNerveCoordinates.original_path_unit_nerve_weak O
  have hsquare : nerveMap F ≫ nerveMap (FreeGroupoid.of O) =
      nerveMap (FreeGroupoid.of (Paths O)) ≫ nerveMap (FreeGroupoid.map F) := by
    apply NatTrans.ext
    funext d
    apply ConcreteCategory.hom_ext
    intro w
    rfl
  have hcomp := SSet.realizationWeakEquivalences.comp_mem _ _ hpath hc
  exact SSet.realizationWeakEquivalences.of_precomp (nerveMap F) _ hp (hsquare.symm ▸ hcomp)

end CategoryTheory.RelativeWords.FreePresentation
