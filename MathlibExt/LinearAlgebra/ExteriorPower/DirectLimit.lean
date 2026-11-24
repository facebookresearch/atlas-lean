/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import Mathlib.Algebra.Colimit.Module
public import Mathlib.LinearAlgebra.ExteriorPower.Basic
public import MathlibExt.LinearAlgebra.ExteriorAlgebra.DirectLimit

/-!
# Homogeneous exterior powers commute with directed module limits

Every finite tuple in the native module limit has a common original stage.
This earns surjectivity on pure wedges. The canonical exterior-algebra
comparison and its native zero criterion earn injectivity without flatness,
freeness or a field. No homogeneous comparison is supplied by a caller.
-/

@[expose] public section

noncomputable section

universe u v w

namespace exteriorPower

variable (R : Type u) [CommRing R]
  {I : Type v} [Preorder I] [IsDirectedOrder I] [Nonempty I]
  (M : I → Type w) [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)]
  (f : ∀ i j, i ≤ j → M i →ₗ[R] M j) [DirectedSystem M (f · · ·)]

open Classical in
/-- The original linear transitions induce the actual homogeneous exterior transitions. -/
def directLimitTransition (n : ℕ) (i j : I) (h : i ≤ j) :
    (⋀[R]^n (M i)) →ₗ[R] (⋀[R]^n (M j)) := map n (f i j h)

open Classical in
/-- Exterior-power transitions inherit the original directed-system equations. -/
instance directLimitTransition_directedSystem (n : ℕ) : DirectedSystem
    (fun i => ⋀[R]^n (M i)) (directLimitTransition R M f n · · ·) where
  map_self := by
    intro i x
    have h : f i i le_rfl = LinearMap.id := by
      ext y
      exact DirectedSystem.map_self' f y
    change map n (f i i le_rfl) x = x
    rw [h, map_id]
    rfl
  map_map := by
    intro k j i hij hjk x
    have h : (f j k hjk).comp (f i j hij) = f i k (hij.trans hjk) := by
      ext y
      exact DirectedSystem.map_map' f hij hjk y
    exact DFunLike.congr_fun ((map_comp (f i j hij) (f j k hjk)).symm.trans
      (congrArg (map n) h)) x

open Classical in
/-- Native module descent gives the canonical homogeneous power comparison. -/
def directLimitComparison (n : ℕ) :
    Module.DirectLimit (fun i => ⋀[R]^n (M i)) (directLimitTransition R M f n) →ₗ[R]
      (⋀[R]^n (DirectLimit M f)) :=
  Module.DirectLimit.lift R I (fun i => ⋀[R]^n (M i)) (directLimitTransition R M f n)
    (fun i => map n (DirectLimit.Module.of R I M f i)) (by
      intro i j h x
      have hof : (DirectLimit.Module.of R I M f j).comp (f i j h) =
          DirectLimit.Module.of R I M f i := by
        ext y
        exact DirectLimit.Module.of_f
      exact DFunLike.congr_fun ((map_comp (f i j h) (DirectLimit.Module.of R I M f j)).symm.trans
        (congrArg (map n) hof)) x)

open Classical in
/-- The actual homogeneous comparison retains every original exterior map of an injection. -/
theorem directLimitComparison_of (n : ℕ) (i : I) (x : ⋀[R]^n (M i)) :
    directLimitComparison R M f n
        (Module.DirectLimit.of R I (fun i => ⋀[R]^n (M i)) (directLimitTransition R M f n) i x) =
      map n (DirectLimit.Module.of R I M f i) x := by
  rw [directLimitComparison, Module.DirectLimit.lift_of]

open Classical in
/-- A finite tuple in the actual native limit is represented in one original module stage. -/
theorem exists_common_stage (n : ℕ) (a : Fin n → DirectLimit M f) :
    ∃ i, ∃ b : Fin n → M i, ∀ j, DirectLimit.Module.of R I M f i (b j) = a j := by
  induction n with
  | zero =>
      refine ⟨Classical.arbitrary I, fun j => j.elim0, ?_⟩
      intro j
      exact j.elim0
  | succ n ih =>
      obtain ⟨i, x, hx⟩ := DirectLimit.exists_eq_mk f (a 0)
      have h0 : DirectLimit.Module.of R I M f i x = a 0 := hx.symm
      obtain ⟨j, b, hb⟩ := ih (Fin.tail a)
      obtain ⟨k, hik, hjk⟩ := exists_ge_ge i j
      refine ⟨k, Fin.cons (f i k hik x) (fun t => f j k hjk (b t)), ?_⟩
      intro t
      refine Fin.cases ?_ (fun q => ?_) t
      · rw [Fin.cons_zero]
        exact (DirectLimit.Module.of_f).trans h0
      · rw [Fin.cons_succ]
        exact (DirectLimit.Module.of_f).trans (hb q)

open Classical in
/-- Pure wedges and the actual common-stage theorem earn surjectivity over an arbitrary ground ring. -/
theorem directLimitComparison_surjective (n : ℕ) :
    Function.Surjective (directLimitComparison R M f n) := by
  apply LinearMap.range_eq_top.mp
  apply top_unique
  rw [← ιMulti_span R n (DirectLimit M f)]
  apply Submodule.span_le.mpr
  rintro _ ⟨a, rfl⟩
  obtain ⟨i, b, hb⟩ := exists_common_stage R M f n a
  refine ⟨Module.DirectLimit.of R I (fun i => ⋀[R]^n (M i)) (directLimitTransition R M f n) i
    (ιMulti R n b), ?_⟩
  rw [directLimitComparison_of, map_apply_ιMulti]
  exact congrArg (ιMulti R n) (funext hb)

open Classical in
private theorem powerToAlgebra_compatibility (n : ℕ) (i j : I) (h : i ≤ j) (x : ⋀[R]^n (M i)) :
    ((DirectLimit.Algebra.of (fun a => ExteriorAlgebra R (M a))
        (ExteriorAlgebra.directLimitTransition R M f) j).toLinearMap.comp
      (Submodule.subtype (⋀[R]^n (M j)))) (directLimitTransition R M f n i j h x) =
    ((DirectLimit.Algebra.of (fun a => ExteriorAlgebra R (M a))
        (ExteriorAlgebra.directLimitTransition R M f) i).toLinearMap.comp
      (Submodule.subtype (⋀[R]^n (M i)))) x := by
  change DirectLimit.Algebra.of (fun a => ExteriorAlgebra R (M a))
      (ExteriorAlgebra.directLimitTransition R M f) j (map n (f i j h) x : ExteriorAlgebra R (M j)) =
    DirectLimit.Algebra.of (fun a => ExteriorAlgebra R (M a))
      (ExteriorAlgebra.directLimitTransition R M f) i (x : ExteriorAlgebra R (M i))
  rw [coe_map]
  exact DirectLimit.Algebra.of_f (R := R) (G := fun a => ExteriorAlgebra R (M a))
    (f := ExteriorAlgebra.directLimitTransition R M f) (i := i) (j := j) h (x : ExteriorAlgebra R (M i))

open Classical in
private def powerToAlgebra (n : ℕ) :
    Module.DirectLimit (fun i => ⋀[R]^n (M i)) (directLimitTransition R M f n) →ₗ[R]
      ExteriorAlgebra.directLimitAlgebra R M f :=
  Module.DirectLimit.lift R I (fun i => ⋀[R]^n (M i)) (directLimitTransition R M f n)
    (fun i => (DirectLimit.Algebra.of (fun a => ExteriorAlgebra R (M a))
      (ExteriorAlgebra.directLimitTransition R M f) i).toLinearMap.comp (Submodule.subtype _))
    (powerToAlgebra_compatibility R M f n)

open Classical in
private theorem powerToAlgebra_of (n : ℕ) (i : I) (x : ⋀[R]^n (M i)) :
    powerToAlgebra R M f n
        (Module.DirectLimit.of R I (fun i => ⋀[R]^n (M i)) (directLimitTransition R M f n) i x) =
      DirectLimit.Algebra.of (fun a => ExteriorAlgebra R (M a))
        (ExteriorAlgebra.directLimitTransition R M f) i (x : ExteriorAlgebra R (M i)) := by
  rw [powerToAlgebra, Module.DirectLimit.lift_of]
  rfl

open Classical in
private theorem powerToAlgebra_eq_zero (n : ℕ)
    (z : Module.DirectLimit (fun i => ⋀[R]^n (M i)) (directLimitTransition R M f n))
    (hz : powerToAlgebra R M f n z = 0) : z = 0 := by
  obtain ⟨i, x, rfl⟩ := Module.DirectLimit.exists_of z
  rw [powerToAlgebra_of] at hz
  change (⟦⟨i, (x : ExteriorAlgebra R (M i))⟩⟧ : ExteriorAlgebra.directLimitAlgebra R M f) = 0 at hz
  obtain ⟨j, hij, hx⟩ :=
    (DirectLimit.exists_eq_zero (f := ExteriorAlgebra.directLimitTransition R M f)
      ⟨i, (x : ExteriorAlgebra R (M i))⟩).mp hz
  have hp : map n (f i j hij) x = 0 := by
    apply Subtype.ext
    change (map n (f i j hij) x : ExteriorAlgebra R (M j)) = 0
    exact (coe_map (f i j hij) x).trans hx
  calc
    Module.DirectLimit.of R I (fun i => ⋀[R]^n (M i)) (directLimitTransition R M f n) i x =
        Module.DirectLimit.of R I (fun i => ⋀[R]^n (M i)) (directLimitTransition R M f n) j
          (directLimitTransition R M f n i j hij x) := (Module.DirectLimit.of_f).symm
    _ = 0 := by
      have htransition : directLimitTransition R M f n i j hij x = 0 := hp
      rw [htransition, map_zero]

open Classical in
private theorem powerToAlgebra_injective (n : ℕ) : Function.Injective (powerToAlgebra R M f n) := by
  intro x y hxy
  have hz : powerToAlgebra R M f n (x - y) = 0 := by rw [map_sub, hxy, sub_self]
  exact sub_eq_zero.mp (powerToAlgebra_eq_zero R M f n (x - y) hz)

open Classical in
private theorem fromDirectLimit_comp_powerToAlgebra (n : ℕ) :
    (ExteriorAlgebra.fromDirectLimit R M f).toLinearMap.comp (powerToAlgebra R M f n) =
      (Submodule.subtype (⋀[R]^n (DirectLimit M f))).comp (directLimitComparison R M f n) := by
  apply Module.DirectLimit.hom_ext
  intro i
  apply LinearMap.ext
  intro x
  change ExteriorAlgebra.fromDirectLimit R M f
      (powerToAlgebra R M f n
        (Module.DirectLimit.of R I (fun i => ⋀[R]^n (M i)) (directLimitTransition R M f n) i x)) =
    (directLimitComparison R M f n
      (Module.DirectLimit.of R I (fun i => ⋀[R]^n (M i)) (directLimitTransition R M f n) i x) :
        ExteriorAlgebra R (DirectLimit M f))
  rw [powerToAlgebra_of, ExteriorAlgebra.fromDirectLimit_of, directLimitComparison_of]
  exact (coe_map (DirectLimit.Module.of R I M f i) x).symm

open Classical in
/-- The earned exterior-algebra comparison and native zero criterion earn homogeneous injectivity. -/
theorem directLimitComparison_injective (n : ℕ) : Function.Injective (directLimitComparison R M f n) := by
  intro x y hxy
  apply powerToAlgebra_injective R M f n
  apply (ExteriorAlgebra.directLimitEquiv R M f).injective
  have hx := LinearMap.congr_fun (fromDirectLimit_comp_powerToAlgebra R M f n) x
  have hy := LinearMap.congr_fun (fromDirectLimit_comp_powerToAlgebra R M f n) y
  exact hx.trans ((congrArg (fun z : ⋀[R]^n (DirectLimit M f) => (z : ExteriorAlgebra R (DirectLimit M f)))
    hxy).trans hy.symm)

open Classical in
/-- The canonical homogeneous comparison is an actual linear equivalence, without flatness or field assumptions. -/
def directLimitEquiv (n : ℕ) :
    Module.DirectLimit (fun i => ⋀[R]^n (M i)) (directLimitTransition R M f n) ≃ₗ[R]
      (⋀[R]^n (DirectLimit M f)) :=
  LinearEquiv.ofBijective (directLimitComparison R M f n)
    ⟨directLimitComparison_injective R M f n, directLimitComparison_surjective R M f n⟩

end exteriorPower
