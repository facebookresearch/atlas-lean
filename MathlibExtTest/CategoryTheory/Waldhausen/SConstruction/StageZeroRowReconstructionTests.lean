/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.CategoryTheory.Waldhausen.SConstruction.StageZeroRowReconstruction

/-!
# Tests for finite Stage reconstruction from the zero row

These tests consume the extracted admissible flag, canonical cell cokernels,
the zero-row hom equivalence, final-zero-row extensionality,
Stage-isomorphism coherence, degrees zero through three, mixed universes, and the comparison with
`AdmissibleMonoFlag.toStage`.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false

open CategoryTheory Limits ZeroObject
open CategoryTheory.ExactCategory

universe v u

namespace MathlibExtTest.CategoryTheory.Waldhausen.SConstruction.StageZeroRowReconstructionTests

open _root_.CategoryTheory.Waldhausen.SConstruction

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C]

local instance stageZeroRowTestsWaldhausenCategory : WaldhausenCategoryWithoutGluing C :=
  ExactCategory.waldhausenCategory C

section GenericCells

variable {n : ℕ} (A : Stage C n)

example : AdmissibleMonoFlag C n :=
  A.toAdmissibleMonoFlag

example (j : Fin (n + 1)) :
    A.zeroRowChain.obj j = A.zeroRowObj j :=
  A.zeroRowChain_obj j

example {i j : Fin (n + 1)} (hij : i ≤ j) :
    A.zeroRowChain.map (homOfLE hij) =
      A.obj.map (horiz (Fin.zero_le i) hij) :=
  A.zeroRowChain_map hij

example (i : Fin n) :
    A.zeroRowChain.map' i.val (i.val + 1)
        (Nat.le_succ i.val) (Nat.succ_le_iff.mpr i.isLt) =
      A.zeroRowSuccMap i :=
  A.zeroRowChain_map_succ i

example {i j : Fin (n + 1)} (hij : i ≤ j) :
    A.zeroRowChain.map (homOfLE hij) ≫
      A.zeroRowCellProjection hij = 0 :=
  A.zeroRowCell_comp_projection hij

example {i j : Fin (n + 1)} (hij : i ≤ j) :
    IsAdmissibleExact
      (ShortComplex.mk (A.zeroRowChain.map (homOfLE hij))
        (A.zeroRowCellProjection hij)
        (A.zeroRowCell_comp_projection hij)) :=
  A.zeroRowCell_exact hij

example {i j : Fin (n + 1)} (hij : i ≤ j) :
    IsColimit (CokernelCofork.ofπ (A.zeroRowCellProjection hij)
      (A.zeroRowCell_comp_projection hij)) :=
  A.zeroRowCellIsColimit hij

example {i j : Fin (n + 1)} (hij : i ≤ j) :
    IsAdmissibleEpi (A.zeroRowCellProjection hij) :=
  A.zeroRowCellProjection_admissibleEpi hij

example {i j i' j' : Fin (n + 1)}
    (hij : i ≤ j) (hi'j' : i' ≤ j')
    (hii' : i ≤ i') (hjj' : j ≤ j') :
    A.zeroRowCellProjection hij ≫
        A.obj.map (intervalHomOfLE hij hi'j' hii' hjj') =
      A.zeroRowChain.map (homOfLE hjj') ≫
        A.zeroRowCellProjection hi'j' :=
  A.zeroRowCellProjection_naturality hij hi'j' hii' hjj'

end GenericCells

section HomExtension

variable {n : ℕ} {A B D : Stage C n}
variable (f : A.zeroRowChain ⟶ B.zeroRowChain)
  (g : B.zeroRowChain ⟶ D.zeroRowChain)

example : A ⟶ B :=
  A.homOfZeroRowHom f

example {i j : Fin (n + 1)} (hij : i ≤ j) :
    A.zeroRowCellProjection hij ≫ A.cellHomOfZeroRowHom f hij =
      f.app j ≫ B.zeroRowCellProjection hij :=
  A.zeroRowCellProjection_cellHomOfZeroRowHom f hij

example {i j : Fin (n + 1)} (hij : i ≤ j) :
    (A.homOfZeroRowHom f).hom.app (interval i j hij) =
      A.cellHomOfZeroRowHom f hij :=
  A.homOfZeroRowHom_app_interval f hij

example (j : Fin (n + 1)) :
    (A.homOfZeroRowHom f).hom.app
        (interval 0 j (Fin.zero_le j)) = f.app j :=
  A.homOfZeroRowHom_app_zeroRow f j

example : A.zeroRowHom (A.homOfZeroRowHom f) = f :=
  A.zeroRowHom_homOfZeroRowHom f

example (h : A ⟶ B) : A.homOfZeroRowHom (A.zeroRowHom h) = h :=
  A.homOfZeroRowHom_zeroRowHom h

example : (A ⟶ B) ≃ (A.zeroRowChain ⟶ B.zeroRowChain) :=
  A.homEquivZeroRow B

example : A.homOfZeroRowHom (𝟙 A.zeroRowChain) = 𝟙 A :=
  A.homOfZeroRowHom_id

example : A.homOfZeroRowHom (f ≫ g) =
    A.homOfZeroRowHom f ≫ B.homOfZeroRowHom g :=
  A.homOfZeroRowHom_comp f g

end HomExtension

section FinalRowExtensionality

variable {n : ℕ} {A B : Stage C n}

example (A : Stage C n) (j : Fin (n + 1)) :
    IsAdmissibleMono
      (A.zeroRowChain.map (homOfLE (Fin.le_last j))) :=
  A.zeroRowChain_map_to_last_admissibleMono j

example {f g : A ⟶ B}
    (h : (A.zeroRowHom f).app (Fin.last n) =
      (A.zeroRowHom g).app (Fin.last n)) :
    f = g :=
  Stage.hom_ext_zeroRow_last h

/- At the final index, the cancellable zero-row map is the identity map. -/
example (A : Stage C n) :
    A.zeroRowChain.map (homOfLE (Fin.le_last (Fin.last n))) =
      𝟙 (A.zeroRowChain.obj (Fin.last n)) := by
  rw [Subsingleton.elim
    (homOfLE (Fin.le_last (Fin.last n))) (𝟙 (Fin.last n)),
    A.zeroRowChain.map_id]

/- An interior component equality alone is intentionally not a Stage
extensionality principle. -/
#guard_msgs (error, substring := true) in
example {A B : Stage C 2} {f g : A ⟶ B}
    (h : (A.zeroRowHom f).app (1 : Fin 3) =
      (A.zeroRowHom g).app (1 : Fin 3)) :
    f = g :=
  Stage.hom_ext_zeroRow_last h

end FinalRowExtensionality

section InteriorCancellation

variable (B : Stage C 2)

/- Cancellation through a genuinely non-final zero-row map is the
load-bearing step in final-row extensionality. -/
example {X : C}
    (u v : X ⟶ B.zeroRowChain.obj (1 : Fin 3))
    (h : u ≫ B.zeroRowChain.map
        (homOfLE (Fin.le_last (1 : Fin 3))) =
      v ≫ B.zeroRowChain.map
        (homOfLE (Fin.le_last (1 : Fin 3)))) :
    u = v := by
  let _ : Mono (B.zeroRowChain.map
      (homOfLE (Fin.le_last (1 : Fin 3)))) :=
    (B.zeroRowChain_map_to_last_admissibleMono (1 : Fin 3)).mono
  exact (cancel_mono _).1 h

end InteriorCancellation

section IsoExtension

variable {n : ℕ} {A B D : Stage C n}
variable (e : A.zeroRowChain ≅ B.zeroRowChain)
  (f : B.zeroRowChain ≅ D.zeroRowChain)

example : A ≅ B :=
  A.isoOfZeroRowIso e

example {i j : Fin (n + 1)} (hij : i ≤ j) :
    (A.isoOfZeroRowIso e).hom.hom.app (interval i j hij) =
      A.cellHomOfZeroRowHom e.hom hij :=
  A.isoOfZeroRowIso_hom_app_interval e hij

example {i j : Fin (n + 1)} (hij : i ≤ j) :
    (A.isoOfZeroRowIso e).inv.hom.app (interval i j hij) =
      B.cellHomOfZeroRowHom e.inv hij :=
  A.isoOfZeroRowIso_inv_app_interval e hij

example (j : Fin (n + 1)) :
    (A.isoOfZeroRowIso e).hom.hom.app
        (interval 0 j (Fin.zero_le j)) = e.hom.app j :=
  A.isoOfZeroRowIso_hom_app_zeroRow e j

example : Stage.zeroRowIsoOfIso (A.isoOfZeroRowIso e) = e :=
  Stage.zeroRowIsoOfIso_isoOfZeroRowIso e

example : A.isoOfZeroRowIso (Iso.refl A.zeroRowChain) = Iso.refl A :=
  A.isoOfZeroRowIso_refl

example : A.isoOfZeroRowIso (e.trans f) =
    (A.isoOfZeroRowIso e).trans (B.isoOfZeroRowIso f) :=
  A.isoOfZeroRowIso_trans e f

example : B.isoOfZeroRowIso e.symm = (A.isoOfZeroRowIso e).symm :=
  A.isoOfZeroRowIso_symm e

end IsoExtension

section CompletionComparison

variable {n : ℕ} (A : Stage C n)

example : A.toAdmissibleMonoFlag.chain ≅
    A.toAdmissibleMonoFlag.toStage.zeroRowChain :=
  A.toAdmissibleMonoFlag.zeroRowNatIso

example : A ≅ A.toAdmissibleMonoFlag.toStage :=
  A.toAdmissibleMonoFlagToStageIso

example (j : Fin (n + 1)) :
    A.toAdmissibleMonoFlagToStageIso.hom.hom.app
        (interval 0 j (Fin.zero_le j)) =
      A.toAdmissibleMonoFlag.intervalπ 0 j (Fin.zero_le j) :=
  A.toAdmissibleMonoFlagToStageIso_hom_app_zeroRow j

example {i j : Fin (n + 1)} (hij : i ≤ j) :
    A.zeroRowCellProjection hij ≫
        A.toAdmissibleMonoFlagToStageIso.hom.hom.app
          (interval i j hij) =
      A.toAdmissibleMonoFlag.zeroRowNatIso.hom.app j ≫
        A.toAdmissibleMonoFlag.toStage.zeroRowCellProjection hij :=
  A.zeroRowCellProjection_toAdmissibleMonoFlagToStageIso_hom_app hij

example {i j k : Fin (n + 1)} (hij : i ≤ j) (hjk : j ≤ k) :
    IsPushout
      (A.toAdmissibleMonoFlag.intervalπ i j hij)
      (A.toAdmissibleMonoFlag.chain.map (homOfLE hjk))
      (A.toAdmissibleMonoFlag.intervalMap hij (hij.trans hjk) le_rfl hjk)
      (A.toAdmissibleMonoFlag.intervalπ i k (hij.trans hjk)) :=
  A.toAdmissibleMonoFlag.intervalSquare_isPushout hij hjk

example {i j k : Fin (n + 1)} (hij : i ≤ j) (hjk : j ≤ k) :
    IsAdmissibleExact
      (ShortComplex.mk
        (A.toAdmissibleMonoFlag.intervalMap hij
          (hij.trans hjk) le_rfl hjk)
        (A.toAdmissibleMonoFlag.intervalMap
          (hij.trans hjk) hjk hij le_rfl)
        (A.toAdmissibleMonoFlag.intervalMap_comp_eq_zero hij hjk)) :=
  A.toAdmissibleMonoFlag.interval_triple_exact hij hjk

end CompletionComparison

/-! Fixed-degree clients cover every interval and nested-interval map in
degrees zero through three. -/

section DegreeZero

variable (A : Stage C 0)

example : IsAdmissibleMono
    (A.zeroRowChain.map (homOfLE (Fin.le_last (Fin.last 0)))) :=
  A.zeroRowChain_map_to_last_admissibleMono (Fin.last 0)

example {B : Stage C 0} {f g : A ⟶ B}
    (h : (A.zeroRowHom f).app (Fin.last 0) =
      (A.zeroRowHom g).app (Fin.last 0)) :
    f = g :=
  Stage.hom_ext_zeroRow_last h

example {i j : Fin 1} (hij : i ≤ j) :
    IsColimit (CokernelCofork.ofπ (A.zeroRowCellProjection hij)
      (A.zeroRowCell_comp_projection hij)) :=
  A.zeroRowCellIsColimit hij

example {i j i' j' : Fin 1} (hij : i ≤ j) (hi'j' : i' ≤ j')
    (hii' : i ≤ i') (hjj' : j ≤ j') :
    A.zeroRowCellProjection hij ≫
        A.obj.map (intervalHomOfLE hij hi'j' hii' hjj') =
      A.zeroRowChain.map (homOfLE hjj') ≫
        A.zeroRowCellProjection hi'j' :=
  A.zeroRowCellProjection_naturality hij hi'j' hii' hjj'

end DegreeZero

section DegreeOne

variable (A : Stage C 1)

example : IsAdmissibleMono
    (A.zeroRowChain.map (homOfLE (Fin.le_last (0 : Fin 2)))) :=
  A.zeroRowChain_map_to_last_admissibleMono (0 : Fin 2)

example {B : Stage C 1} {f g : A ⟶ B}
    (h : (A.zeroRowHom f).app (Fin.last 1) =
      (A.zeroRowHom g).app (Fin.last 1)) :
    f = g :=
  Stage.hom_ext_zeroRow_last h

example {i j : Fin 2} (hij : i ≤ j) :
    IsColimit (CokernelCofork.ofπ (A.zeroRowCellProjection hij)
      (A.zeroRowCell_comp_projection hij)) :=
  A.zeroRowCellIsColimit hij

example {i j i' j' : Fin 2} (hij : i ≤ j) (hi'j' : i' ≤ j')
    (hii' : i ≤ i') (hjj' : j ≤ j') :
    A.zeroRowCellProjection hij ≫
        A.obj.map (intervalHomOfLE hij hi'j' hii' hjj') =
      A.zeroRowChain.map (homOfLE hjj') ≫
        A.zeroRowCellProjection hi'j' :=
  A.zeroRowCellProjection_naturality hij hi'j' hii' hjj'

end DegreeOne

section DegreeTwo

variable (A : Stage C 2)

example : IsAdmissibleMono
    (A.zeroRowChain.map (homOfLE (Fin.le_last (1 : Fin 3)))) :=
  A.zeroRowChain_map_to_last_admissibleMono (1 : Fin 3)

example {B : Stage C 2} {f g : A ⟶ B}
    (h : (A.zeroRowHom f).app (Fin.last 2) =
      (A.zeroRowHom g).app (Fin.last 2)) :
    f = g :=
  Stage.hom_ext_zeroRow_last h

example {i j : Fin 3} (hij : i ≤ j) :
    IsColimit (CokernelCofork.ofπ (A.zeroRowCellProjection hij)
      (A.zeroRowCell_comp_projection hij)) :=
  A.zeroRowCellIsColimit hij

example {i j i' j' : Fin 3} (hij : i ≤ j) (hi'j' : i' ≤ j')
    (hii' : i ≤ i') (hjj' : j ≤ j') :
    A.zeroRowCellProjection hij ≫
        A.obj.map (intervalHomOfLE hij hi'j' hii' hjj') =
      A.zeroRowChain.map (homOfLE hjj') ≫
        A.zeroRowCellProjection hi'j' :=
  A.zeroRowCellProjection_naturality hij hi'j' hii' hjj'

end DegreeTwo

section DegreeThree

variable (A : Stage C 3)

example {i j : Fin 4} (hij : i ≤ j) :
    IsColimit (CokernelCofork.ofπ (A.zeroRowCellProjection hij)
      (A.zeroRowCell_comp_projection hij)) :=
  A.zeroRowCellIsColimit hij

example {i j i' j' : Fin 4} (hij : i ≤ j) (hi'j' : i' ≤ j')
    (hii' : i ≤ i') (hjj' : j ≤ j') :
    A.zeroRowCellProjection hij ≫
        A.obj.map (intervalHomOfLE hij hi'j' hii' hjj') =
      A.zeroRowChain.map (homOfLE hjj') ≫
        A.zeroRowCellProjection hi'j' :=
  A.zeroRowCellProjection_naturality hij hi'j' hii' hjj'

end DegreeThree

section UniverseZero

variable {C₀ : Type} [Category C₀] [Preadditive C₀]
  [HasZeroObject C₀] [HasBinaryBiproducts C₀] [ExactCategory C₀]

local instance universeZeroWaldhausenCategory : WaldhausenCategoryWithoutGluing C₀ :=
  ExactCategory.waldhausenCategory C₀

example {n : ℕ} {A B : Stage C₀ n}
    (e : A.zeroRowChain ≅ B.zeroRowChain) : A ≅ B :=
  A.isoOfZeroRowIso e

end UniverseZero

section UniverseOne

variable {C₁ : Type 1} [Category.{1} C₁] [Preadditive C₁]
  [HasZeroObject C₁] [HasBinaryBiproducts C₁] [ExactCategory C₁]

local instance universeOneWaldhausenCategory : WaldhausenCategoryWithoutGluing C₁ :=
  ExactCategory.waldhausenCategory C₁

example {n : ℕ} {A B : Stage C₁ n}
    (e : A.zeroRowChain ≅ B.zeroRowChain) : A ≅ B :=
  A.isoOfZeroRowIso e

end UniverseOne

section MixedUniverses

variable {C₀₁ : Type} [Category.{1} C₀₁] [Preadditive C₀₁]
  [HasZeroObject C₀₁] [HasBinaryBiproducts C₀₁] [ExactCategory C₀₁]
variable {C₁₀ : Type 1} [Category.{0} C₁₀] [Preadditive C₁₀]
  [HasZeroObject C₁₀] [HasBinaryBiproducts C₁₀] [ExactCategory C₁₀]

local instance mixedZeroOneWaldhausenCategory : WaldhausenCategoryWithoutGluing C₀₁ :=
  ExactCategory.waldhausenCategory C₀₁
local instance mixedOneZeroWaldhausenCategory : WaldhausenCategoryWithoutGluing C₁₀ :=
  ExactCategory.waldhausenCategory C₁₀

example {n : ℕ} {A B : Stage C₀₁ n}
    (e : A.zeroRowChain ≅ B.zeroRowChain) : A ≅ B :=
  A.isoOfZeroRowIso e

example {n : ℕ} {A B : Stage C₁₀ n}
    (e : A.zeroRowChain ≅ B.zeroRowChain) : A ≅ B :=
  A.isoOfZeroRowIso e

example {n : ℕ} (A : Stage C₀₁ n) (j : Fin (n + 1)) :
    IsAdmissibleMono
      (A.zeroRowChain.map (homOfLE (Fin.le_last j))) :=
  A.zeroRowChain_map_to_last_admissibleMono j

example {n : ℕ} {A B : Stage C₀₁ n} {f g : A ⟶ B}
    (h : (A.zeroRowHom f).app (Fin.last n) =
      (A.zeroRowHom g).app (Fin.last n)) :
    f = g :=
  Stage.hom_ext_zeroRow_last h

example {n : ℕ} (A : Stage C₁₀ n) (j : Fin (n + 1)) :
    IsAdmissibleMono
      (A.zeroRowChain.map (homOfLE (Fin.le_last j))) :=
  A.zeroRowChain_map_to_last_admissibleMono j

example {n : ℕ} {A B : Stage C₁₀ n} {f g : A ⟶ B}
    (h : (A.zeroRowHom f).app (Fin.last n) =
      (A.zeroRowHom g).app (Fin.last n)) :
    f = g :=
  Stage.hom_ext_zeroRow_last h

end MixedUniverses

#print axioms CategoryTheory.Waldhausen.SConstruction.Stage.zeroRowChain_map_to_last_admissibleMono
#print axioms CategoryTheory.Waldhausen.SConstruction.Stage.hom_ext_zeroRow_last
#print axioms CategoryTheory.Waldhausen.SConstruction.Stage.zeroRowCellIsColimit
#print axioms CategoryTheory.Waldhausen.SConstruction.Stage.homEquivZeroRow
#print axioms CategoryTheory.Waldhausen.SConstruction.Stage.isoOfZeroRowIso
#print axioms CategoryTheory.Waldhausen.SConstruction.Stage.toAdmissibleMonoFlagToStageIso

end MathlibExtTest.CategoryTheory.Waldhausen.SConstruction.StageZeroRowReconstructionTests

end
