/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Co1BinaryPolarDuality
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Co1BinaryEquivariantScalars

/-! The actual Conway action has a unique nonzero invariant bilinear form. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- Every bilinear form invariant under the actual Conway action is a scalar polar form. -/
theorem co1BinaryAction_invariant_bilinear_scalar
    (B : LinearMap.BilinForm (ZMod 2) (Fin 24 → ZMod 2))
    (hB : ∀ g : Co1, ∀ x y,
      B (co1BinaryAction g x) (co1BinaryAction g y) = B x y) :
    ∃ a : ZMod 2, B = a • co1BinaryPolar := by
  let T := co1BinaryPolarEquiv.symm.toLinearMap.comp B
  have ht (x y : Fin 24 → ZMod 2) : co1BinaryPolar (T x) y = B x y := by
    exact congrArg (fun f : (Fin 24 → ZMod 2) →ₗ[ZMod 2] ZMod 2 => f y)
      (co1BinaryPolarEquiv.apply_symm_apply (B x))
  have he : ∀ g : Co1, ∀ x,
      T (co1BinaryAction g x) = co1BinaryAction g (T x) := by
    intro g x
    apply co1BinaryPolarEquiv.injective
    apply LinearMap.ext
    intro y
    obtain ⟨z, rfl⟩ := (co1BinaryAction g).surjective y
    change co1BinaryPolar (T (co1BinaryAction g x)) (co1BinaryAction g z) =
      co1BinaryPolar (co1BinaryAction g (T x)) (co1BinaryAction g z)
    rw [ht, co1BinaryPolar_invariant, ht, hB]
  obtain ⟨a, ha⟩ := co1BinaryAction_equivariant_scalar T he
  refine ⟨a, LinearMap.ext fun x => LinearMap.ext fun y => ?_⟩
  rw [← ht, ha]
  simp only [LinearMap.smul_apply, LinearMap.id_apply, map_smul]

/-- Over the actual binary field the invariant bilinear forms are precisely zero and polar. -/
theorem co1BinaryAction_invariant_bilinear_zero_or_polar
    (B : LinearMap.BilinForm (ZMod 2) (Fin 24 → ZMod 2))
    (hB : ∀ g : Co1, ∀ x y,
      B (co1BinaryAction g x) (co1BinaryAction g y) = B x y) :
    B = 0 ∨ B = co1BinaryPolar := by
  obtain ⟨a, ha⟩ := co1BinaryAction_invariant_bilinear_scalar B hB
  have hbits : ∀ b : ZMod 2, b = 0 ∨ b = 1 := by decide +kernel
  rcases hbits a with hz | ho
  · left; simpa only [hz, zero_smul] using ha
  · right; simpa only [ho, one_smul] using ha

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
