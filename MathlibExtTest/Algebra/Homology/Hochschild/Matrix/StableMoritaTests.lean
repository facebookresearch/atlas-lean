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

public import MathlibExt.Algebra.Homology.Hochschild.Matrix.StableMorita
public import Mathlib.Algebra.Category.ModuleCat.AB

/-!
# Growth maps of stable matrix diagrams

Any transformation of connected indexing functors gives a quasi-isomorphism
of their colimit complexes when the colimits are exact. The concrete client
uses successor growth over the Nat filtered shape, with a noncommutative
algebra, lifted coefficients and a larger common lift height.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits
open ModuleCat.Algebra.Hochschild.Matrix

universe t u v w j j'

namespace MathlibExtTest.StableHochschildMatrixMorita

attribute [local instance] Coefficients.leftModule Coefficients.rightModule
  Coefficients.commute Coefficients.leftTower Coefficients.rightTower
  ModuleCat.Algebra.Hochschild.uliftSMulCommClass IsFiltered.isConnected

variable (k : Type u) [CommRing k]
  (A : Type v) [Ring A] [Algebra k A]
  (M : Type w) [AddCommGroup M] [Module k M]
  [Module A M] [Module Aᵐᵒᵖ M] [SMulCommClass A Aᵐᵒᵖ M]
  [IsScalarTower k A M] [IsScalarTower k Aᵐᵒᵖ M]
  {J : Type j} [Category.{j'} J] [IsConnected J]
  [HasColimitsOfShape J (ModuleCat.{max u v w t} k)]
  [HasExactColimitsOfShape J (ModuleCat.{max u v w t} k)]

/-- The trace comparison makes every actual reindexing transition a quasi-isomorphism. -/
theorem reindexing_quasiIso {G G' : J ⥤ ℕ} (τ : G ⟶ G') :
    QuasiIso (StableMorita.stableMapAt.{t} k A M τ) := by
  rw [quasiIso_iff]
  intro n
  apply (quasiIsoAt_iff_isIso_homologyMap _ n).2
  let eS := StableMorita.stableHomologyIsoAt.{t} k A M G n
  let eT := StableMorita.stableHomologyIsoAt.{t} k A M G' n
  have he : HomologicalComplex.homologyMap (StableMorita.stableMapAt.{t} k A M τ) n =
      eS.hom ≫ eT.inv := by
    apply (cancel_mono eT.hom).mp
    rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    exact StableMorita.stableHomologyIsoAt_naturality.{t} k A M τ n
  rw [he]
  infer_instance

private def successor : ℕ ⥤ ℕ where
  obj n := n + 1
  map h := homOfLE (Nat.succ_le_succ (leOfHom h))
  map_id _ := Subsingleton.elim _ _
  map_comp _ _ := Subsingleton.elim _ _

private def growth : 𝟭 ℕ ⟶ successor where
  app n := homOfLE (Nat.le_succ n)
  naturality _ := Subsingleton.elim _ _

/-- Successor growth preserves the homology for the lifted noncommutative matrix client. -/
example : QuasiIso (StableMorita.stableMapAt.{3} ℤ (Matrix (Fin 2) (Fin 2) ℤ)
    (ULift.{2} (Matrix (Fin 2) (Fin 2) ℤ)) growth) := by
  let _ : AB5OfSize.{0, 0} (AddCommGrpCat.{3}) := AB5OfSize_of_univLE AddCommGrpCat.{3}
  let _ : HasExactColimitsOfShape ℕ (ModuleCat.{3} ℤ) :=
    HasExactColimitsOfShape.domain_of_functor ℕ
      (forget₂ (ModuleCat.{3} ℤ) AddCommGrpCat.{3})
  exact reindexing_quasiIso.{3} ℤ (Matrix (Fin 2) (Fin 2) ℤ)
    (ULift.{2} (Matrix (Fin 2) (Fin 2) ℤ)) growth

end MathlibExtTest.StableHochschildMatrixMorita
