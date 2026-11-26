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
# Exterior powers of directed module limits

For a coherent system of `R`-modules over a nonempty directed preorder and every `n : ℕ`, the
comparison `lim_i Λ^n_R M_i → Λ^n_R(lim_i M_i)` sends the class of a stage element to its
exterior image under the stage map.

Every finite tuple in the module limit has representatives in one common stage. This gives the
wedge formula, and the comparison is both injective and surjective, hence an `R`-linear
equivalence.

Reference: Bourbaki, *Algebra*, Chapter III.
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
/-- Let `R` be a commutative ring, `I` a preorder, `M_i` be `R`-modules, and `f_ij : M_i →ₗ[R]
M_j` for `i≤j`. For `n : ℕ` and `i≤j`, the homogeneous transition is `exteriorPower.map n f_ij
: Λ^n_R M_i →ₗ[R] Λ^n_R M_j`. -/
def directLimitTransition (n : ℕ) (i j : I) (h : i ≤ j) :
    (⋀[R]^n (M i)) →ₗ[R] (⋀[R]^n (M j)) := map n (f i j h)

open Classical in
/-- Let `R` be a commutative ring, `I` a preorder, `M_i` be `R`-modules, and `f_ij : M_i →ₗ[R]
M_j` for `i≤j`. Assume `f_ii=id` and `f_jk ∘ f_ij=f_ik`, so the maps form a `DirectedSystem`.
For every `n : ℕ`, the maps `Λ^n f_ij` satisfy identity and composition and form
`DirectedSystem (fun i ↦ Λ^n_R M_i)`. -/
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
/-- Let `R` be a commutative ring, `I` a preorder, `M_i` be `R`-modules, and `f_ij : M_i →ₗ[R]
M_j` for `i≤j`. Assume `f_ii=id` and `f_jk ∘ f_ij=f_ik`, so the maps form a `DirectedSystem`.
Assume `I` nonempty and directed. Write `L=colim_i M_i`, `u_i : M_i → L`, and `C_n=colim_i
Λ^n_R M_i` in modules, with stage maps `v_i`. For `n : ℕ`, the `R`-linear map
`directLimitComparison R M f n : C_n → Λ^n_R L` sends `v_i(x)` to `exteriorPower.map n u_i x`. -/
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
/-- Let `R` be a commutative ring, `I` a preorder, `M_i` be `R`-modules, and `f_ij : M_i →ₗ[R]
M_j` for `i≤j`. Assume `f_ii=id` and `f_jk ∘ f_ij=f_ik`, so the maps form a `DirectedSystem`.
Assume `I` nonempty and directed. Write `L=colim_i M_i`, `u_i : M_i → L`, and `C_n=colim_i
Λ^n_R M_i` in modules, with stage maps `v_i`. For `n : ℕ`, `i : I`, and `x : Λ^n_R M_i`,
`directLimitComparison n (v_i x)=exteriorPower.map n u_i x`. -/
theorem directLimitComparison_of (n : ℕ) (i : I) (x : ⋀[R]^n (M i)) :
    directLimitComparison R M f n
        (Module.DirectLimit.of R I (fun i => ⋀[R]^n (M i)) (directLimitTransition R M f n) i x) =
      map n (DirectLimit.Module.of R I M f i) x := by
  rw [directLimitComparison, Module.DirectLimit.lift_of]

open Classical in
/-- Let `R` be a commutative ring, `I` a preorder, `M_i` be `R`-modules, and `f_ij : M_i →ₗ[R]
M_j` for `i≤j`. Assume `f_ii=id` and `f_jk ∘ f_ij=f_ik`, so the maps form a `DirectedSystem`.
Assume `I` nonempty and directed. Write `L=colim_i M_i`, `u_i : M_i → L`, and `C_n=colim_i
Λ^n_R M_i` in modules, with stage maps `v_i`. For `n : ℕ` and `a : Fin n → L`, there exist `i
: I` and `b : Fin n → M_i` with `u_i(b j)=a j` for every `j : Fin n`. -/
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
/-- Let `R` be a commutative ring, `I` a preorder, `M_i` be `R`-modules, and `f_ij : M_i →ₗ[R]
M_j` for `i≤j`. Assume `f_ii=id` and `f_jk ∘ f_ij=f_ik`, so the maps form a `DirectedSystem`.
Assume `I` nonempty and directed. Write `L=colim_i M_i`, `u_i : M_i → L`, and `C_n=colim_i
Λ^n_R M_i` in modules, with stage maps `v_i`. For every `n : ℕ`, `directLimitComparison R M f
n : C_n → Λ^n_R L` is surjective. -/
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
/-- Let `R` be a commutative ring, `I` a preorder, `M_i` be `R`-modules, and `f_ij : M_i →ₗ[R]
M_j` for `i≤j`. Assume `f_ii=id` and `f_jk ∘ f_ij=f_ik`, so the maps form a `DirectedSystem`.
Assume `I` nonempty and directed. Write `L=colim_i M_i`, `u_i : M_i → L`, and `C_n=colim_i
Λ^n_R M_i` in modules, with stage maps `v_i`. For every `n : ℕ`, `directLimitComparison R M f
n : C_n → Λ^n_R L` is injective. -/
theorem directLimitComparison_injective (n : ℕ) : Function.Injective (directLimitComparison R M f n) := by
  intro x y hxy
  apply powerToAlgebra_injective R M f n
  apply (ExteriorAlgebra.directLimitEquiv R M f).injective
  have hx := LinearMap.congr_fun (fromDirectLimit_comp_powerToAlgebra R M f n) x
  have hy := LinearMap.congr_fun (fromDirectLimit_comp_powerToAlgebra R M f n) y
  exact hx.trans ((congrArg (fun z : ⋀[R]^n (DirectLimit M f) => (z : ExteriorAlgebra R (DirectLimit M f)))
    hxy).trans hy.symm)

open Classical in
/-- Let `R` be a commutative ring, `I` a preorder, `M_i` be `R`-modules, and `f_ij : M_i →ₗ[R]
M_j` for `i≤j`. Assume `f_ii=id` and `f_jk ∘ f_ij=f_ik`, so the maps form a `DirectedSystem`.
Assume `I` nonempty and directed. Write `L=colim_i M_i`, `u_i : M_i → L`, and `C_n=colim_i
Λ^n_R M_i` in modules, with stage maps `v_i`. For every `n : ℕ`, `directLimitEquiv R M f n :
C_n ≃ₗ[R] Λ^n_R L` is the linear equivalence whose forward map is `directLimitComparison`. -/
def directLimitEquiv (n : ℕ) :
    Module.DirectLimit (fun i => ⋀[R]^n (M i)) (directLimitTransition R M f n) ≃ₗ[R]
      (⋀[R]^n (DirectLimit M f)) :=
  LinearEquiv.ofBijective (directLimitComparison R M f n)
    ⟨directLimitComparison_injective R M f n, directLimitComparison_surjective R M f n⟩

end exteriorPower
