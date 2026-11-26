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
# Exterior algebras of directed module colimits

Let `R` be a commutative ring and `(M_i,f_ij)` a coherent system of `R`-modules over a
nonempty directed preorder. If `L=colim_i M_i` and `C=colim_i ExteriorAlgebra R M_i`, the
stage maps induce an `R`-algebra equivalence `C ≃ₐ[R] ExteriorAlgebra R L`.

The forward map sends a stage element `j_i(a)` to `ExteriorAlgebra.map u_i a`. Its inverse
sends `ι(u_i x)` to `j_i(ι x)`. These formulas also specify the generator map `L → C` and its
square-zero relation.

Reference: Bourbaki, *Algebra*, Chapter III.
-/

@[expose] public section

noncomputable section

universe u v w

namespace ExteriorAlgebra

variable (R : Type u) [CommRing R]
  {I : Type v} [Preorder I]
  (M : I → Type w) [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)]
  (f : ∀ i j, i ≤ j → M i →ₗ[R] M j) [DirectedSystem M (f · · ·)]

/-- Let `R` be a commutative ring, `I` a preorder, `M_i` be `R`-modules, and `f_ij : M_i →ₗ[R]
M_j` for `i≤j`. The transition `directLimitTransition R M f i j h` is `ExteriorAlgebra.map
f_ij : ExteriorAlgebra R M_i →ₐ[R] ExteriorAlgebra R M_j`. -/
def directLimitTransition (i j : I) (h : i ≤ j) :
    ExteriorAlgebra R (M i) →ₐ[R] ExteriorAlgebra R (M j) := map (f i j h)

/-- Let `R` be a commutative ring, `I` a preorder, `M_i` be `R`-modules, and `f_ij : M_i →ₗ[R]
M_j` for `i≤j`. Assume `f_ii=id` and `f_jk ∘ f_ij=f_ik`, so the maps form a `DirectedSystem`.
The induced maps `ExteriorAlgebra.map f_ij` satisfy the identity and composition laws and form
a directed system of exterior algebras. -/
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

/-- Let `R` be a commutative ring, `I` a preorder, `M_i` be `R`-modules, and `f_ij : M_i →ₗ[R]
M_j` for `i≤j`. Assume `f_ii=id` and `f_jk ∘ f_ij=f_ik`, so the maps form a `DirectedSystem`.
Assume `I` is nonempty and directed. Write `L=colim_i M_i`, `u_i : M_i → L` for its stage
maps, `C=colim_i ExteriorAlgebra R M_i`, and `j_i` for the stage algebra maps.
`directLimitAlgebra R M f` is the algebra limit `C` with transitions `ExteriorAlgebra.map
f_ij`. -/
abbrev directLimitAlgebra :=
  DirectLimit (fun i => ExteriorAlgebra R (M i)) (directLimitTransition R M f)

/-- Let `R` be a commutative ring, `I` a preorder, `M_i` be `R`-modules, and `f_ij : M_i →ₗ[R]
M_j` for `i≤j`. Assume `f_ii=id` and `f_jk ∘ f_ij=f_ik`, so the maps form a `DirectedSystem`.
Assume `I` is nonempty and directed. Write `L=colim_i M_i`, `u_i : M_i → L` for its stage
maps, `C=colim_i ExteriorAlgebra R M_i`, and `j_i` for the stage algebra maps.
`directLimitGenerator R M f : L →ₗ[R] C` sends `u_i(x)` to `j_i(ι x)`. -/
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

/-- Let `R` be a commutative ring, `I` a preorder, `M_i` be `R`-modules, and `f_ij : M_i →ₗ[R]
M_j` for `i≤j`. Assume `f_ii=id` and `f_jk ∘ f_ij=f_ik`, so the maps form a `DirectedSystem`.
Assume `I` is nonempty and directed. Write `L=colim_i M_i`, `u_i : M_i → L` for its stage
maps, `C=colim_i ExteriorAlgebra R M_i`, and `j_i` for the stage algebra maps. For `i : I` and
`x : M_i`, `directLimitGenerator R M f (u_i x)=j_i(ι x)`. -/
theorem directLimitGenerator_of (i : I) (x : M i) :
    directLimitGenerator R M f (DirectLimit.Module.of R I M f i x) =
      DirectLimit.Algebra.of (fun a => ExteriorAlgebra R (M a)) (directLimitTransition R M f) i
        (ι R x) := by
  rw [directLimitGenerator, DirectLimit.Module.lift_of]
  rfl

/-- Let `R` be a commutative ring, `I` a preorder, `M_i` be `R`-modules, and `f_ij : M_i →ₗ[R]
M_j` for `i≤j`. Assume `f_ii=id` and `f_jk ∘ f_ij=f_ik`, so the maps form a `DirectedSystem`.
Assume `I` is nonempty and directed. Write `L=colim_i M_i`, `u_i : M_i → L` for its stage
maps, `C=colim_i ExteriorAlgebra R M_i`, and `j_i` for the stage algebra maps. For every `x :
L`, `directLimitGenerator R M f x * directLimitGenerator R M f x=0` in `C`. -/
theorem directLimitGenerator_sq_zero (x : DirectLimit M f) :
    directLimitGenerator R M f x * directLimitGenerator R M f x = 0 := by
  obtain ⟨i, y, rfl⟩ := DirectLimit.exists_eq_mk f x
  change directLimitGenerator R M f (DirectLimit.Module.of R I M f i y) *
      directLimitGenerator R M f (DirectLimit.Module.of R I M f i y) = 0
  rw [directLimitGenerator_of, ← map_mul, ι_sq_zero, map_zero]

/-- Let `R` be a commutative ring, `I` a preorder, `M_i` be `R`-modules, and `f_ij : M_i →ₗ[R]
M_j` for `i≤j`. Assume `f_ii=id` and `f_jk ∘ f_ij=f_ik`, so the maps form a `DirectedSystem`.
Assume `I` is nonempty and directed. Write `L=colim_i M_i`, `u_i : M_i → L` for its stage
maps, `C=colim_i ExteriorAlgebra R M_i`, and `j_i` for the stage algebra maps. The `R`-algebra
map `toDirectLimit : ExteriorAlgebra R L → C` sends `ι(x)` to `directLimitGenerator x` and
hence `ι(u_i x)` to `j_i(ι x)`. -/
def toDirectLimit : ExteriorAlgebra R (DirectLimit M f) →ₐ[R] directLimitAlgebra R M f :=
  lift R ⟨directLimitGenerator R M f, directLimitGenerator_sq_zero R M f⟩

/-- Let `R` be a commutative ring, `I` a preorder, `M_i` be `R`-modules, and `f_ij : M_i →ₗ[R]
M_j` for `i≤j`. Assume `f_ii=id` and `f_jk ∘ f_ij=f_ik`, so the maps form a `DirectedSystem`.
Assume `I` is nonempty and directed. Write `L=colim_i M_i`, `u_i : M_i → L` for its stage
maps, `C=colim_i ExteriorAlgebra R M_i`, and `j_i` for the stage algebra maps. The `R`-algebra
map `fromDirectLimit : C → ExteriorAlgebra R L` sends `j_i(a)` to `ExteriorAlgebra.map u_i a`. -/
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

/-- Let `R` be a commutative ring, `I` a preorder, `M_i` be `R`-modules, and `f_ij : M_i →ₗ[R]
M_j` for `i≤j`. Assume `f_ii=id` and `f_jk ∘ f_ij=f_ik`, so the maps form a `DirectedSystem`.
Assume `I` is nonempty and directed. Write `L=colim_i M_i`, `u_i : M_i → L` for its stage
maps, `C=colim_i ExteriorAlgebra R M_i`, and `j_i` for the stage algebra maps. For `i : I` and
`a : ExteriorAlgebra R M_i`, `fromDirectLimit(j_i a)=ExteriorAlgebra.map u_i a`. -/
theorem fromDirectLimit_of (i : I) (x : ExteriorAlgebra R (M i)) :
    fromDirectLimit R M f
        (DirectLimit.Algebra.of (fun a => ExteriorAlgebra R (M a)) (directLimitTransition R M f) i x) =
      map (DirectLimit.Module.of R I M f i) x := by
  rw [fromDirectLimit, DirectLimit.Algebra.lift_of]

/-- Let `R` be a commutative ring, `I` a preorder, `M_i` be `R`-modules, and `f_ij : M_i →ₗ[R]
M_j` for `i≤j`. Assume `f_ii=id` and `f_jk ∘ f_ij=f_ik`, so the maps form a `DirectedSystem`.
Assume `I` is nonempty and directed. Write `L=colim_i M_i`, `u_i : M_i → L` for its stage
maps, `C=colim_i ExteriorAlgebra R M_i`, and `j_i` for the stage algebra maps. For `i : I` and
`x : M_i`, `toDirectLimit(ι(u_i x))=j_i(ι x)`. -/
theorem toDirectLimit_ι_of (i : I) (x : M i) :
    toDirectLimit R M f (ι R (DirectLimit.Module.of R I M f i x)) =
      DirectLimit.Algebra.of (fun a => ExteriorAlgebra R (M a)) (directLimitTransition R M f) i
        (ι R x) := by
  rw [toDirectLimit, lift_ι_apply, directLimitGenerator_of]

/-- Let `R` be a commutative ring, `I` a preorder, `M_i` be `R`-modules, and `f_ij : M_i →ₗ[R]
M_j` for `i≤j`. Assume `f_ii=id` and `f_jk ∘ f_ij=f_ik`, so the maps form a `DirectedSystem`.
Assume `I` is nonempty and directed. Write `L=colim_i M_i`, `u_i : M_i → L` for its stage
maps, `C=colim_i ExteriorAlgebra R M_i`, and `j_i` for the stage algebra maps.
`fromDirectLimit ∘ toDirectLimit = id` as `R`-algebra maps on `ExteriorAlgebra R L`. -/
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

/-- Let `R` be a commutative ring, `I` a preorder, `M_i` be `R`-modules, and `f_ij : M_i →ₗ[R]
M_j` for `i≤j`. Assume `f_ii=id` and `f_jk ∘ f_ij=f_ik`, so the maps form a `DirectedSystem`.
Assume `I` is nonempty and directed. Write `L=colim_i M_i`, `u_i : M_i → L` for its stage
maps, `C=colim_i ExteriorAlgebra R M_i`, and `j_i` for the stage algebra maps. `toDirectLimit
∘ fromDirectLimit = id` as `R`-algebra maps on `C`. -/
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

/-- Let `R` be a commutative ring, `I` a preorder, `M_i` be `R`-modules, and `f_ij : M_i →ₗ[R]
M_j` for `i≤j`. Assume `f_ii=id` and `f_jk ∘ f_ij=f_ik`, so the maps form a `DirectedSystem`.
Assume `I` is nonempty and directed. Write `L=colim_i M_i`, `u_i : M_i → L` for its stage
maps, `C=colim_i ExteriorAlgebra R M_i`, and `j_i` for the stage algebra maps. The comparison
is the `R`-algebra equivalence `directLimitEquiv : C ≃ₐ[R] ExteriorAlgebra R L`, with forward
map `fromDirectLimit` and inverse `toDirectLimit`. -/
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

/-- Let `R` be a commutative ring, `I` a preorder, `M_i` be `R`-modules, and `f_ij : M_i →ₗ[R]
M_j` for `i≤j`. Assume `f_ii=id` and `f_jk ∘ f_ij=f_ik`, so the maps form a `DirectedSystem`.
Assume `I` is nonempty and directed. Write `L=colim_i M_i`, `u_i : M_i → L` for its stage
maps, `C=colim_i ExteriorAlgebra R M_i`, and `j_i` for the stage algebra maps. For `i : I` and
`a : ExteriorAlgebra R M_i`, `directLimitEquiv(j_i a)=ExteriorAlgebra.map u_i a`. -/
theorem directLimitEquiv_of (i : I) (x : ExteriorAlgebra R (M i)) :
    directLimitEquiv R M f
        (DirectLimit.Algebra.of (fun a => ExteriorAlgebra R (M a)) (directLimitTransition R M f) i x) =
      map (DirectLimit.Module.of R I M f i) x :=
  fromDirectLimit_of R M f i x

end ExteriorAlgebra
