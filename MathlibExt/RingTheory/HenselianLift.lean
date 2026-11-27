/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from `ZInQKernel/Contrib/G9/HenselEmb.lean`
(https://github.com/Deicyde/diophantine-z-q), compared with the source file at commit
`e9956cda4174c060ff85f5a6ddc7e4003e63fdd3`.
Copyright 2026 the contributors to Deicyde/diophantine-z-q.
Licensed under the Apache License, Version 2.0.
-/

module

public import Mathlib.FieldTheory.PrimitiveElement
public import Mathlib.RingTheory.Henselian

/-!
# Lifting finite separable extensions through a henselian residue map

Let `θ : R → Ω` be a surjective `K`-algebra map onto a field, where `R` is henselian along the
kernel of `θ` and every element outside the kernel is a unit (so `R` is local with residue map
`θ`). For a finite separable extension `L/K`, every `K`-algebra map `ι : L → Ω` lifts to a
`K`-algebra map `L → R` (`AlgHom.exists_comp_eq_of_henselianRing`): write `L = K(α)`; a root of
the minimal polynomial of `α` in `R` lifting `ι α` exists by Hensel's lemma, since the minimal
polynomial is separable. If `R` is a domain, the lift is unique (`AlgHom.ext_of_comp_eq`): two
roots of a separable polynomial with the same image under `θ` are equal.
-/

@[expose] public noncomputable section

open Polynomial

namespace AlgHom

variable {K R Ω : Type*} [Field K] [CommRing R] [Algebra K R] [Field Ω] [Algebra K Ω]

/-- If `R` is a domain, two roots `a, b ∈ R` of `P ∈ K[X]` with `θ a = θ b` are equal as soon as
`P'(θ b) ≠ 0`. -/
theorem eq_of_aeval_eq_zero_of_apply_eq [IsDomain R] (θ : R →ₐ[K] Ω) (P : K[X]) {a b : R}
    (ha : aeval a P = 0) (hb : aeval b P = 0) (hab : θ a = θ b)
    (hd : aeval (θ b) (derivative P) ≠ 0) : a = b := by
  obtain ⟨k, hk⟩ := (P.map (algebraMap K R)).binomExpansion b (a - b)
  rw [add_sub_cancel, eval_map_algebraMap, eval_map_algebraMap, ha, hb, derivative_map,
    eval_map_algebraMap, zero_add] at hk
  have hfac : (a - b) * (aeval b (derivative P) + k * (a - b)) = 0 := by
    linear_combination -hk
  rcases mul_eq_zero.mp hfac with h | h
  · exact sub_eq_zero.mp h
  · refine absurd ?_ hd
    have := congrArg θ h
    rwa [map_add, map_mul, map_sub, hab, sub_self, mul_zero, add_zero, map_zero,
      ← aeval_algHom_apply] at this

variable {L : Type*} [Field L] [Algebra K L] [FiniteDimensional K L] [Algebra.IsSeparable K L]

/-- **Hensel lifting of embeddings.** Let `θ : R → Ω` be a surjective `K`-algebra map onto a field,
with `R` henselian along `ker θ` and every element outside `ker θ` a unit. Then every `K`-algebra
map `ι : L → Ω` from a finite separable extension `L` of `K` lifts to a `K`-algebra map
`ι₀ : L → R` with `θ ∘ ι₀ = ι`. -/
theorem exists_comp_eq_of_henselianRing (θ : R →ₐ[K] Ω) (hsurj : Function.Surjective θ)
    [HenselianRing R (RingHom.ker θ)] (hunit : ∀ y, θ y ≠ 0 → IsUnit y) (ι : L →ₐ[K] Ω) :
    ∃ ι₀ : L →ₐ[K] R, θ.comp ι₀ = ι := by
  let pb := Field.powerBasisOfFiniteOfSeparable K L
  set P := minpoly K pb.gen
  have hP : P.Monic := minpoly.monic (Algebra.IsIntegral.isIntegral pb.gen)
  have hsep : P.Separable := Algebra.IsSeparable.isSeparable K pb.gen
  have hroot : aeval pb.gen P = 0 := minpoly.aeval K pb.gen
  obtain ⟨a₀, ha₀⟩ := hsurj (ι pb.gen)
  obtain ⟨a, haroot, hamem⟩ := HenselianRing.is_henselian (I := RingHom.ker θ)
    (P.map (algebraMap K R)) (hP.map _) a₀
    (by
      rw [RingHom.mem_ker, eval_map_algebraMap, ← aeval_algHom_apply, ha₀, aeval_algHom_apply,
        hroot, map_zero])
    (by
      refine IsUnit.map _ (hunit _ ?_)
      rw [derivative_map, eval_map_algebraMap, ← aeval_algHom_apply, ha₀, aeval_algHom_apply]
      exact (map_ne_zero ι).mpr (hsep.aeval_derivative_ne_zero hroot))
  have haP : aeval a P = 0 := by
    rw [← eval_map_algebraMap]
    exact haroot
  have hθa : θ a = ι pb.gen := by
    rw [RingHom.mem_ker, map_sub, sub_eq_zero] at hamem
    rw [hamem, ha₀]
  exact ⟨pb.lift a haP, pb.algHom_ext (by rw [comp_apply, PowerBasis.lift_gen, hθa])⟩

/-- **Uniqueness of lifts of embeddings.** Let `θ : R → Ω` be a `K`-algebra map to a field. If `R`
is a domain, two `K`-algebra maps `f, g : L → R` from a finite separable extension `L` of `K` with
`θ ∘ f = θ ∘ g` are equal. -/
theorem ext_of_comp_eq [IsDomain R] (θ : R →ₐ[K] Ω) {f g : L →ₐ[K] R}
    (h : θ.comp f = θ.comp g) : f = g := by
  let pb := Field.powerBasisOfFiniteOfSeparable K L
  have hsep : (minpoly K pb.gen).Separable := Algebra.IsSeparable.isSeparable K pb.gen
  have hroot : aeval pb.gen (minpoly K pb.gen) = 0 := minpoly.aeval K pb.gen
  refine pb.algHom_ext (eq_of_aeval_eq_zero_of_apply_eq θ (minpoly K pb.gen) ?_ ?_ ?_ ?_)
  · rw [aeval_algHom_apply, hroot, map_zero]
  · rw [aeval_algHom_apply, hroot, map_zero]
  · exact DFunLike.congr_fun h pb.gen
  · rw [← comp_apply, aeval_algHom_apply]
    exact (map_ne_zero (θ.comp g)).mpr (hsep.aeval_derivative_ne_zero hroot)

end AlgHom
