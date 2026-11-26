/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @junekim623, Muse
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
public import MathlibExt.Algebra.Category.ModuleCat.Sheaf.Colimits
public import MathlibExt.Algebra.Category.ModuleCat.Sheaf.OverLocalSurjective

/-!
# Quasicoherence of the zero module sheaf

Let `(C,J)` be a site and `R : Sheaf J RingCat.{u}` a sheaf of rings. Assume weak
sheafification for `AddCommGrpCat.{u}` and the characterization of sheafification equivalences
as locally bijective maps, both on `J` and on every slice topology `J.over X`.

The zero object of `SheafOfModules.{u} R` is quasicoherent. On the maximal covering family `X
↦ X`, each restriction has a presentation with empty generating and relation families: both
free sheaves are zero, and the presentation map has zero kernel.
-/

@[expose] public section

universe u v₁ u₁

open _root_.CategoryTheory CategoryTheory Limits

-- Public initial-object types need public colimit evidence. Register the
-- universe-pinned discrete-colimit theorem only in this consumer.
attribute [local instance] SheafOfModules.hasColimitsOfShape_discrete

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C}
  {R : Sheaf J RingCat.{u}}
  [HasWeakSheafify J AddCommGrpCat.{u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ (X : C), HasWeakSheafify (J.over X) AddCommGrpCat.{u}]
  [∀ (X : C), (J.over X).WEqualsLocallyBijective AddCommGrpCat.{u}]

namespace SheafOfModules

variable {X : C}

-- The free sheaf on an empty index type is initial: it is the empty coproduct,
-- so maps out of it are uniquely determined by the colimit universal property.
-- Stated over a slice site, as used for the local presentations below.
private noncomputable def isInitial_free_empty :
    IsInitial (free (R := R.over X) (ULift.{u} (Fin 0) : Type u)) := by
  haveI : ∀ N, Unique (free (R := R.over X) (ULift.{u} (Fin 0) : Type u) ⟶ N) :=
    fun N => ⟨⟨(isColimitFreeCofan _).desc
      (Cofan.mk N (fun (i : ULift.{u} (Fin 0)) => Fin.elim0 i.down))⟩, fun f => by
      refine IsColimit.hom_ext (isColimitFreeCofan _) fun (j : Discrete (ULift.{u} (Fin 0))) =>
        Fin.elim0 j.as.down⟩
  exact IsInitial.ofUnique _

-- The empty generating family generates a zero sheaf: every map into it
-- is an epimorphism.
private def GeneratingSections.empty {M : SheafOfModules (R.over X)} (hM : IsZero M) :
    M.GeneratingSections where
  I := ULift.{u} (Fin 0)
  s := fun i => Fin.elim0 i.down
  epi := hM.epi _

-- The kernel of a map out of the initial free sheaf is zero: conclude
-- `𝟙 = 0` by cancelling the monomorphism `kernel.ι` on the right.
omit [HasWeakSheafify J AddCommGrpCat.{u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}] in
private theorem isZero_kernel_empty {M : SheafOfModules (R.over X)} (hM : IsZero M) :
    IsZero (kernel (GeneratingSections.empty hM).π) := by
  have hA : IsZero (free (R := R.over X) (ULift.{u} (Fin 0) : Type u)) :=
    isInitial_free_empty.isZero
  rw [IsZero.iff_id_eq_zero]
  refine (cancel_mono (kernel.ι (GeneratingSections.empty hM).π)).mp ?_
  rw [Category.id_comp, zero_comp]
  exact hA.eq_of_tgt _ _

-- The empty presentation of a zero sheaf: generators and relations are both
-- empty.
private noncomputable def Presentation.empty {M : SheafOfModules (R.over X)} (hM : IsZero M) :
    M.Presentation where
  generators := GeneratingSections.empty hM
  relations := GeneratingSections.empty (isZero_kernel_empty hM)

-- The zero sheaf is quasicoherent: the maximal cover (every object) carries
-- the empty local presentation. Only slice sheafification/local-bijectivity
-- is assumed; in particular no binary products.
/-- Let `C : Type u₁` be a category with morphism universe `v₁`, `J` a Grothendieck topology, and
`R : Sheaf J RingCat.{u}`. Assume `HasWeakSheafify J AddCommGrpCat.{u}` and
`J.WEqualsLocallyBijective AddCommGrpCat.{u}`, together with the corresponding hypotheses for
every `J.over X`. Then the zero object `⊥_ SheafOfModules.{u} R` satisfies
`SheafOfModules.IsQuasicoherent`. Its local presentations use the maximal cover of all objects
and empty generator and relation families. -/
theorem isQuasicoherent_zero :
    _root_.SheafOfModules.IsQuasicoherent (R := R)
      (⊥_ SheafOfModules.{u} R : SheafOfModules.{u} R) := by
  apply QuasicoherentData.isQuasicoherent
  refine { I := C, X := fun X => X, coversTop := ?_, presentation := fun X => ?_ }
  · intro W
    rw [Sieve.pullback_ofObjects_eq_top (fun X : C => X) (𝟙 W)]
    exact J.top_mem W
  · have hN : IsZero (((⊥_ SheafOfModules.{u} R).over X)) :=
      Functor.map_isZero _ initialIsInitial.isZero
    exact Presentation.empty hN

end SheafOfModules

end
