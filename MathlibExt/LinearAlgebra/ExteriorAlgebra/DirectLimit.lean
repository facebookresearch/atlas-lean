/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import Mathlib.Algebra.Colimit.DirectLimit
public import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic

/-!
# Exterior algebras of native directed module limits

The native directed-limit carrier is used for both the modules and their
exterior algebras. The existing module lift gives the generator map; its
square-zero property is checked on an actual finite-stage representative.
The exterior universal property and native algebra lift then give inverse
maps, proved inverse on generators. No comparison equivalence is an input.
-/

@[expose] public section

noncomputable section

universe u v w

namespace ExteriorAlgebra

variable (R : Type u) [CommRing R]
  {I : Type v} [Preorder I]
  (M : I → Type w) [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)]
  (f : ∀ i j, i ≤ j → M i →ₗ[R] M j) [DirectedSystem M (f · · ·)]

/-- The actual exterior maps induced by the original directed linear transitions. -/
def directLimitTransition (i j : I) (h : i ≤ j) :
    ExteriorAlgebra R (M i) →ₐ[R] ExteriorAlgebra R (M j) := map (f i j h)

/-- Native exterior maps inherit the original directed-system identity and composition. -/
instance directLimitTransition_directedSystem : DirectedSystem
    (fun i => ExteriorAlgebra R (M i)) (directLimitTransition R M f · · ·) where
  map_self := by
    intro i x
    change map (f i i le_rfl) x = x
    have hf : f i i le_rfl = LinearMap.id := by
      ext y
      exact DirectedSystem.map_self' f y
    rw [hf, map_id]
    rfl
  map_map := by
    intro k j i hij hjk x
    change map (f j k hjk) (map (f i j hij) x) = map (f i k (hij.trans hjk)) x
    have hf : (f j k hjk).comp (f i j hij) = f i k (hij.trans hjk) := by
      ext y
      exact DirectedSystem.map_map' f hij hjk y
    exact DFunLike.congr_fun
      ((map_comp_map (f i j hij) (f j k hjk)).trans (congrArg map hf)) x

variable [IsDirectedOrder I] [Nonempty I]

/-- The native directed limit of the original exterior algebras. -/
abbrev directLimitAlgebra :=
  DirectLimit (fun i => ExteriorAlgebra R (M i)) (directLimitTransition R M f)

/-- The actual limit-module generator map into the native limit of the exterior algebras. -/
def directLimitGenerator : DirectLimit M f →ₗ[R] directLimitAlgebra R M f :=
  DirectLimit.Module.lift R I M f
    (fun i => (DirectLimit.Algebra.of (fun a => ExteriorAlgebra R (M a))
      (directLimitTransition R M f) i).toLinearMap.comp (ι R))
    (by
      intro i j h x
      change DirectLimit.Algebra.of (fun a => ExteriorAlgebra R (M a))
          (directLimitTransition R M f) j (ι R (f i j h x)) =
        DirectLimit.Algebra.of (fun a => ExteriorAlgebra R (M a)) (directLimitTransition R M f) i (ι R x)
      rw [← map_apply_ι (f i j h) x]
      exact DirectLimit.Algebra.of_f (R := R) (G := fun a => ExteriorAlgebra R (M a))
        (f := directLimitTransition R M f) (i := i) (j := j) h (ι R x))

/-- The generator map keeps the original stage generator and canonical algebra injection. -/
theorem directLimitGenerator_of (i : I) (x : M i) :
    directLimitGenerator R M f (DirectLimit.Module.of R I M f i x) =
      DirectLimit.Algebra.of (fun a => ExteriorAlgebra R (M a)) (directLimitTransition R M f) i
        (ι R x) := by
  rw [directLimitGenerator, DirectLimit.Module.lift_of]
  rfl

/-- Every actual limit-module generator still squares to zero. -/
theorem directLimitGenerator_sq_zero (x : DirectLimit M f) :
    directLimitGenerator R M f x * directLimitGenerator R M f x = 0 := by
  obtain ⟨i, y, rfl⟩ := DirectLimit.exists_eq_mk f x
  change directLimitGenerator R M f (DirectLimit.Module.of R I M f i y) *
      directLimitGenerator R M f (DirectLimit.Module.of R I M f i y) = 0
  rw [directLimitGenerator_of, ← map_mul, ι_sq_zero, map_zero]

/-- The exterior universal property gives the canonical map into the native exterior-algebra limit. -/
def toDirectLimit : ExteriorAlgebra R (DirectLimit M f) →ₐ[R] directLimitAlgebra R M f :=
  lift R ⟨directLimitGenerator R M f, directLimitGenerator_sq_zero R M f⟩

/-- Native algebra descent sends each original exterior stage to the actual exterior algebra of the module limit. -/
def fromDirectLimit : directLimitAlgebra R M f →ₐ[R] ExteriorAlgebra R (DirectLimit M f) :=
  DirectLimit.Algebra.lift (fun i => ExteriorAlgebra R (M i)) (directLimitTransition R M f)
    (ExteriorAlgebra R (DirectLimit M f)) (fun i => map (DirectLimit.Module.of R I M f i))
    (by
      intro i j h x
      have hof : (DirectLimit.Module.of R I M f j).comp (f i j h) = DirectLimit.Module.of R I M f i := by
        ext y
        exact DirectLimit.Module.of_f
      have hc := (map_comp_map (f i j h) (DirectLimit.Module.of R I M f j)).trans (congrArg map hof)
      exact DFunLike.congr_fun hc x)

/-- The map out of the native algebra limit retains the original exterior map of each module injection. -/
theorem fromDirectLimit_of (i : I) (x : ExteriorAlgebra R (M i)) :
    fromDirectLimit R M f
        (DirectLimit.Algebra.of (fun a => ExteriorAlgebra R (M a)) (directLimitTransition R M f) i x) =
      map (DirectLimit.Module.of R I M f i) x := by
  rw [fromDirectLimit, DirectLimit.Algebra.lift_of]

/-- The inverse comparison keeps every original finite-stage generator. -/
theorem toDirectLimit_ι_of (i : I) (x : M i) :
    toDirectLimit R M f (ι R (DirectLimit.Module.of R I M f i x)) =
      DirectLimit.Algebra.of (fun a => ExteriorAlgebra R (M a)) (directLimitTransition R M f) i
        (ι R x) := by
  rw [toDirectLimit, lift_ι_apply, directLimitGenerator_of]

/-- The two canonical maps are inverse on the actual exterior algebra of the limit module. -/
theorem fromDirectLimit_comp_toDirectLimit :
    (fromDirectLimit R M f).comp (toDirectLimit R M f) =
      AlgHom.id R (ExteriorAlgebra R (DirectLimit M f)) := by
  apply hom_ext
  apply LinearMap.ext
  intro x
  obtain ⟨i, y, rfl⟩ := DirectLimit.exists_eq_mk f x
  change fromDirectLimit R M f (toDirectLimit R M f (ι R (DirectLimit.Module.of R I M f i y))) =
    ι R (DirectLimit.Module.of R I M f i y)
  rw [toDirectLimit_ι_of, fromDirectLimit_of, map_apply_ι]

/-- The same native generators determine the inverse law on the directed exterior-algebra limit. -/
theorem toDirectLimit_comp_fromDirectLimit :
    (toDirectLimit R M f).comp (fromDirectLimit R M f) =
      AlgHom.id R (directLimitAlgebra R M f) := by
  apply DirectLimit.Algebra.hom_ext
  intro i
  apply hom_ext
  apply LinearMap.ext
  intro x
  change toDirectLimit R M f
      (fromDirectLimit R M f
        (DirectLimit.Algebra.of (fun a => ExteriorAlgebra R (M a)) (directLimitTransition R M f) i
          (ι R x))) =
    DirectLimit.Algebra.of (fun a => ExteriorAlgebra R (M a)) (directLimitTransition R M f) i
      (ι R x)
  rw [fromDirectLimit_of, map_apply_ι, toDirectLimit_ι_of]

/-- The actual native directed exterior-algebra limit is canonically the exterior algebra of the native module limit. -/
def directLimitEquiv : directLimitAlgebra R M f ≃ₐ[R] ExteriorAlgebra R (DirectLimit M f) :=
  AlgEquiv.ofBijective (fromDirectLimit R M f) (by
    constructor
    · intro x y hxy
      have hx := DFunLike.congr_fun (toDirectLimit_comp_fromDirectLimit R M f) x
      have hy := DFunLike.congr_fun (toDirectLimit_comp_fromDirectLimit R M f) y
      have h := congrArg (toDirectLimit R M f) hxy
      exact hx.symm.trans (h.trans hy)
    · intro x
      exact ⟨toDirectLimit R M f x,
        DFunLike.congr_fun (fromDirectLimit_comp_toDirectLimit R M f) x⟩)

/-- The canonical comparison retains the complete exterior map at every original stage. -/
theorem directLimitEquiv_of (i : I) (x : ExteriorAlgebra R (M i)) :
    directLimitEquiv R M f
        (DirectLimit.Algebra.of (fun a => ExteriorAlgebra R (M a)) (directLimitTransition R M f) i x) =
      map (DirectLimit.Module.of R I M f i) x :=
  fromDirectLimit_of R M f i x

end ExteriorAlgebra
