/-
Author: @toskua
Copyright (c) 2019 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Colimits

/-!
# Constant finite-support coproducts of left modules

This is the concrete coproduct construction from ModuleCat.Colimits at its
arbitrary-ring scope. Natural scalar multiplication on the linear-map space
gives the native finite-sum descent without requiring commuting R-scalars.
The carrier and all single-coordinate coproduct legs are the original ones.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits

namespace ModuleCat

universe w u

variable (R : Type w) [Ring R] (M I : Type u) [AddCommGroup M] [Module R M]

/-- The actual constant coproduct cofan has finite-support functions as its
carrier and the original single-coordinate linear maps as its legs. -/
def finsuppCofan : Cofan (fun _ : I => ModuleCat.of R M) :=
  Cofan.mk (ModuleCat.of R (I →₀ M)) (fun i =>
    ModuleCat.ofHom (Finsupp.lsingle i (R := R) (M := ModuleCat.of R M)))

/-- The constant finite-support cofan is colimiting over an arbitrary ring.
The descended finite sum is R-linear; its auxiliary scalar structure is Nat. -/
def finsuppCofanIsColimit : IsColimit (finsuppCofan R M I) :=
  Cofan.IsColimit.mk _
    (fun s => ModuleCat.ofHom <| Finsupp.lsum ℕ (N := s.pt) (fun i => (s.inj i).hom))
    (fun s i => by
      apply ModuleCat.hom_ext
      exact Finsupp.lsum_comp_lsingle ℕ (fun j => (s.inj j).hom) i)
    (fun s f h => by
      apply ModuleCat.hom_ext
      apply Finsupp.lhom_ext'
      intro i
      exact (congrArg ModuleCat.Hom.hom (h i)).trans
        (Finsupp.lsum_comp_lsingle ℕ (fun j => (s.inj j).hom) i).symm)

end ModuleCat
