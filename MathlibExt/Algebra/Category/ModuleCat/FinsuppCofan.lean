/-
Copyright (c) 2019 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-
Modified for Atlas library integration. Standalone author labels were removed;
source attributions are retained in NOTICE.
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

-- The native coproduct proof transports its concrete linear-map fields.
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The constant finite-support cofan is colimiting over an arbitrary ring.
The descended finite sum is R-linear; its auxiliary scalar structure is Nat. -/
def finsuppCofanIsColimit : IsColimit (finsuppCofan R M I) where
  desc s := ModuleCat.ofHom <|
    Finsupp.lsum ℕ (N := s.pt) (fun i => (s.ι.app ⟨i⟩).hom)
  fac := by aesop (add simp finsuppCofan)
  uniq s f h := by
    ext : 1
    exact Finsupp.lhom_ext' (fun i => LinearMap.ext (fun x => by
      simpa using! congr($(h ⟨i⟩) (x : M))))

end ModuleCat
