/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.GroupTheory.Abelianization.Defs
public import Mathlib.GroupTheory.QuotientGroup.Defs
public import Mathlib.GroupTheory.IsPerfect

/-!
# Abelianization of a surjection with perfect kernel

The original homomorphism induces a bijection on abelianizations. The
inverse is constructed by descending the original abelianization map
through its actual kernel quotient, then using the actual surjection.
-/

public section

noncomputable section
set_option autoImplicit false

universe u v

namespace Abelianization

variable {G : Type u} [Group G] {H : Type v} [Group H]

/-- The original abelianization map kills every element of a perfect subgroup. -/
theorem of_eq_one_of_mem_perfect_subgroup (P : Subgroup G) [Group.IsPerfect P]
    {g : G} (hg : g ∈ P) : (Abelianization.of g : Abelianization G) = 1 := by
  let q : P →* Abelianization G := Abelianization.of.comp P.subtype
  have hp : (⟨g, hg⟩ : P) ∈ commutator P := Group.IsPerfect.mem_commutator
  have hq := (Abelianization.commutator_subset_ker q) hp
  exact MonoidHom.mem_ker.mp hq

/-- A surjective homomorphism with perfect kernel induces a bijection on
its actual abelianizations, without a supplied quotient inverse. -/
theorem map_bijective_of_surjective_of_isPerfect_ker
    (f : G →* H) (hf : Function.Surjective f) [Group.IsPerfect f.ker] :
    Function.Bijective (Abelianization.map f) := by
  classical
  have hk : f.ker ≤ (Abelianization.of : G →* Abelianization G).ker := by
    intro g hg
    exact MonoidHom.mem_ker.mpr
      (of_eq_one_of_mem_perfect_subgroup f.ker hg)
  let q : G ⧸ f.ker →* Abelianization G :=
    QuotientGroup.lift f.ker Abelianization.of hk
  let e : G ⧸ f.ker ≃* H := QuotientGroup.liftEquiv f.ker hf rfl
  let s : H →* Abelianization G := q.comp e.symm.toMonoidHom
  have hs (g : G) : s (f g) = Abelianization.of g := by
    change q (e.symm (f g)) = Abelianization.of g
    have he : e (g : G ⧸ f.ker) = f g :=
      QuotientGroup.liftEquiv_mk f.ker hf rfl g
    rw [← he, e.symm_apply_apply]
    exact QuotientGroup.lift_mk f.ker hk g
  let back : Abelianization H →* Abelianization G := Abelianization.lift s
  have hleft : back.comp (Abelianization.map f) =
      MonoidHom.id (Abelianization G) := by
    apply Abelianization.hom_ext
    apply MonoidHom.ext
    intro g
    change back (Abelianization.map f (Abelianization.of g)) = Abelianization.of g
    rw [Abelianization.map_of]
    change Abelianization.lift s (Abelianization.of (f g)) = Abelianization.of g
    rw [Abelianization.lift_apply_of]
    exact hs g
  constructor
  · intro a b hab
    have ha : back (Abelianization.map f a) = a := DFunLike.congr_fun hleft a
    have hb : back (Abelianization.map f b) = b := DFunLike.congr_fun hleft b
    exact ha.symm.trans ((congrArg back hab).trans hb)
  · intro z
    induction z using QuotientGroup.induction_on with
    | _ h =>
      obtain ⟨g, rfl⟩ := hf h
      exact ⟨Abelianization.of g, Abelianization.map_of f g⟩

end Abelianization

end
