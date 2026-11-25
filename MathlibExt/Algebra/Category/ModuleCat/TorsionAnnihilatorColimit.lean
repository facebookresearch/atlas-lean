/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/
module

public import MathlibExt.Algebra.Category.ModuleCat.DirectedSubmoduleColimit
public import MathlibExt.Algebra.Category.ModuleCat.TorsionFunctor

/-!
# The actual primary component as the colimit of its power annihilators

The categorical natural-number diagram uses the original torsionBySet submodules
of the same carrier. Its native directed supremum is exactly Ideal.primaryComponent.
Actual coefficient maps and index inclusions supply the cocone and its naturality.
No ring object, quotient-Hom model, second colimit engine or book proof is used.
-/

@[expose] public section
noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v

namespace ModuleCat.Torsion

variable {R : Type u} [CommRing R]

/-- The original annihilator of all scalars in the actual n-th ideal power. -/
def powerAnnihilator (I : Ideal R) (M : ModuleCat.{v} R) (n : ℕ) : Submodule R M :=
  Submodule.torsionBySet R M (I ^ n : Ideal R)

/-- The native ideal-power law makes the actual annihilator family increasing. -/
lemma powerAnnihilator_monotone (I : Ideal R) (M : ModuleCat.{v} R) :
    Monotone (powerAnnihilator I M) :=
  fun i j hij => Submodule.torsionBySet_le_torsionBySet_pow i j hij I

/-- The native natural-number category indexes the original stage inclusions. -/
def annihilatorDiagram (I : Ideal R) (M : ModuleCat.{v} R) : ℕ ⥤ ModuleCat.{v} R :=
  DirectedSubmoduleColimit.diagram (powerAnnihilator I M) (powerAnnihilator_monotone I M)

/-- The cocone point is the native supremum in the unchanged original carrier. -/
def annihilatorCocone (I : Ideal R) (M : ModuleCat.{v} R) : Cocone (annihilatorDiagram I M) :=
  DirectedSubmoduleColimit.cocone (powerAnnihilator I M) (powerAnnihilator_monotone I M)

/-- That point is literally the already canonical primary-component functor object. -/
lemma annihilatorCocone_point (I : Ideal R) (M : ModuleCat.{v} R) :
    (annihilatorCocone I M).pt = (functor I).obj M := rfl

/-- Stage inclusion into the actual primary component, with no comparison certificate. -/
def annihilatorInclusion (I : Ideal R) (M : ModuleCat.{v} R) (n : ℕ) :
    ModuleCat.of R (powerAnnihilator I M n) ⟶ (functor I).obj M :=
  (annihilatorCocone I M).ι.app n

/-- Its value remains the original coefficient. -/
lemma annihilatorInclusion_val (I : Ideal R) (M : ModuleCat.{v} R)
    (n : ℕ) (x : powerAnnihilator I M n) :
    ((annihilatorInclusion I M n).hom x).val = x.val := rfl

/-- Actual native directed-union data earns the module categorical universal property. -/
def annihilatorIsColimit (I : Ideal R) (M : ModuleCat.{v} R) :
    IsColimit (annihilatorCocone I M) :=
  DirectedSubmoduleColimit.isColimit (powerAnnihilator I M) (powerAnnihilator_monotone I M)

/-- Only this particular annihilator diagram needs a colimit witness. -/
instance annihilatorHasColimit (I : Ideal R) (M : ModuleCat.{v} R) :
    HasColimit (annihilatorDiagram I M) := ⟨_, annihilatorIsColimit I M⟩

/-- All actual natural-number index maps commute with the stage cocone. -/
lemma annihilator_index_naturality (I : Ideal R) (M : ModuleCat.{v} R)
    {i j : ℕ} (hij : i ≤ j) :
    (annihilatorDiagram I M).map (homOfLE hij) ≫ annihilatorInclusion I M j =
      annihilatorInclusion I M i :=
  (annihilatorCocone I M).w (homOfLE hij)

/-- A genuine linear coefficient map preserves every actual annihilator stage. -/
lemma map_mem_powerAnnihilator (I : Ideal R) {M N : ModuleCat.{v} R}
    (f : M ⟶ N) (n : ℕ) (x : M) (hx : x ∈ powerAnnihilator I M n) :
    f.hom x ∈ powerAnnihilator I N n := by
  apply (Submodule.mem_torsionBySet_iff ((I ^ n : Ideal R) : Set R) (f.hom x)).mpr
  intro r
  have hr : (r : R) • x = 0 :=
    ((Submodule.mem_torsionBySet_iff ((I ^ n : Ideal R) : Set R) x).mp hx) r
  change (r : R) • f.hom x = 0
  rw [← map_smul, hr, map_zero]

/-- The original coefficient map, restricted at every power stage. -/
def annihilatorDiagramMap (I : Ideal R) {M N : ModuleCat.{v} R} (f : M ⟶ N) :
    annihilatorDiagram I M ⟶ annihilatorDiagram I N :=
  DirectedSubmoduleColimit.coefficientDiagramMap
    (powerAnnihilator I M) (powerAnnihilator_monotone I M)
    (powerAnnihilator I N) (powerAnnihilator_monotone I N) f.hom
    (fun n x hx => map_mem_powerAnnihilator I f n x hx)

/-- Stage coefficient maps retain the actual original linear map value. -/
lemma annihilatorDiagramMap_val (I : Ideal R) {M N : ModuleCat.{v} R}
    (f : M ⟶ N) (n : ℕ) (x : powerAnnihilator I M n) :
    (((annihilatorDiagramMap I f).app n).hom x).val = f.hom x.val := rfl

/-- Coefficient dependence is a genuine functor to actual categorical diagrams. -/
def annihilatorDiagramFunctor (I : Ideal R) :
    ModuleCat.{v} R ⥤ (ℕ ⥤ ModuleCat.{v} R) where
  obj := annihilatorDiagram I
  map := annihilatorDiagramMap I
  map_id M := by
    apply NatTrans.ext
    funext n
    apply ModuleCat.hom_ext
    ext x
    rfl
  map_comp f g := by
    apply NatTrans.ext
    funext n
    apply ModuleCat.hom_ext
    ext x
    rfl

/-- The stage cocone commutes with the actual native primary-component map. -/
lemma annihilator_coefficient_naturality (I : Ideal R) {M N : ModuleCat.{v} R}
    (f : M ⟶ N) (n : ℕ) :
    annihilatorInclusion I M n ≫ (functor I).map f =
      (annihilatorDiagramMap I f).app n ≫ annihilatorInclusion I N n := by
  apply ModuleCat.hom_ext
  ext x
  rfl

/-- Universal descent equals that same native map, rather than an assumed comparison. -/
lemma primaryComponentMap_eq_annihilatorDesc (I : Ideal R) {M N : ModuleCat.{v} R}
    (f : M ⟶ N) :
    (annihilatorIsColimit I M).desc
      ((Cocone.precompose (annihilatorDiagramMap I f)).obj (annihilatorCocone I N)) =
        (functor I).map f := by
  apply (annihilatorIsColimit I M).hom_ext
  intro n
  exact ((annihilatorIsColimit I M).fac _ n).trans
    (annihilator_coefficient_naturality I f n).symm

end ModuleCat.Torsion
