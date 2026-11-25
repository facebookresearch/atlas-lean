/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_Algebra_IsStandardEtale_exists_isStandardEtale_tensorProduct_algEquiv_of_`
`surjective.lean`
and
`P2M/Sol/S_Algebra_IsStandardEtale_exists_isStandardEtale_tensorProduct_algEquiv_of_`
`surjective.lean`
(https://github.com/anthropics/fermats-last-theorem):
Compared with the source files at commit
`6e837e75355538c7f80bab5b956861e86c4eacc2`.
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
The upstream NOTICE also credits:
Mathlib — https://github.com/leanprover-community/mathlib4
Copyright (c) the respective Mathlib authors, as recorded in the headers of the
Mathlib source files.
Released under the Apache License, Version 2.0.
The source is machine-generated proof code built around a proof-extraction
framework; the statements and proofs are reused here with that machinery
removed and the names restated in Mathlib style.
-/

module

public import Mathlib.Algebra.Polynomial.Lifts
public import Mathlib.RingTheory.Etale.StandardEtale

@[expose] public section

open scoped TensorProduct
open Polynomial

universe u v w t

namespace Algebra

private theorem StandardEtalePair.hasMap_iff_of_map_eq
    {C : Type u} {C₀ : Type v} [CommRing C] [CommRing C₀] [Algebra C C₀]
    {P : StandardEtalePair C} {P₀ : StandardEtalePair C₀} {n : ℕ}
    (hPf : P.f.map (algebraMap C C₀) = P₀.f)
    (hPg : P.g.map (algebraMap C C₀) = P₀.g ^ (n + 1))
    {T : Type t} [CommRing T] [Algebra C₀ T] [Algebra C T] [IsScalarTower C C₀ T]
    (t : T) : P.HasMap t ↔ P₀.HasMap t := by
  simp only [StandardEtalePair.HasMap]
  rw [← aeval_map_algebraMap C₀ t P.f, ← aeval_map_algebraMap C₀ t P.g, hPf, hPg,
    map_pow, isUnit_pow_iff (Nat.succ_ne_zero n)]

/-- A standard étale algebra over a quotient base ring `C₀` lifts through any
surjection `C → C₀`: there is a standard étale `C`-algebra `S` whose base
change back to `C₀` is equivalent to the given algebra. The bases and the
given algebra may live in arbitrary universes; the constructed witness `S`
lies in the same universe as `C`, since it is built as a quotient of a
polynomial ring over `C`. -/
theorem IsStandardEtale.exists_isStandardEtale_tensorProduct_algEquiv_of_surjective
    {C : Type u} {C₀ : Type v} [CommRing C] [CommRing C₀] [Algebra C C₀]
    (hC : Function.Surjective (algebraMap C C₀))
    (S₀ : Type w) [CommRing S₀] [Algebra C₀ S₀] [Algebra.IsStandardEtale C₀ S₀] :
    ∃ (S : Type u) (_ : CommRing S) (_ : Algebra C S), Algebra.IsStandardEtale C S ∧
      Nonempty (C₀ ⊗[C] S ≃ₐ[C₀] S₀) := by
  classical
  obtain ⟨P₀⟩ := Algebra.IsStandardEtale.nonempty_standardEtalePresentation (R := C₀) (S := S₀)
  rcases subsingleton_or_nontrivial C₀ with hC₀ | hC₀
  · haveI : Subsingleton S₀ := Module.subsingleton C₀ S₀
    refine ⟨C, inferInstance, inferInstance, inferInstance, ⟨?_⟩⟩
    exact AlgEquiv.ofBijective
      ((Algebra.ofId C₀ S₀).comp (Algebra.TensorProduct.rid C C₀ C₀).toAlgHom)
      ⟨Function.injective_of_subsingleton _, Function.surjective_to_subsingleton _⟩
  set φ : C →+* C₀ := algebraMap C C₀ with hφ
  obtain ⟨f, hf, -, hfm⟩ :=
    Polynomial.lifts_and_degree_eq_and_monic (f := φ)
      ((mem_lifts _).mpr (map_surjective φ hC P₀.f)) P₀.monic_f
  obtain ⟨p₁, p₂, n, hP⟩ := P₀.cond
  obtain ⟨g, hg⟩ := map_surjective φ hC P₀.g
  obtain ⟨q₁, hq₁⟩ := map_surjective φ hC p₁
  obtain ⟨q₂, hq₂⟩ := map_surjective φ hC p₂
  let P : StandardEtalePair C :=
    { f := f, monic_f := hfm, g := g * (derivative f * q₁ + f * q₂),
      cond := ⟨g * q₁, g * q₂, 1, by ring⟩ }
  have hPf : P.f.map φ = P₀.f := hf
  have hPg : P.g.map φ = P₀.g ^ (n + 1) := by
    show (g * (derivative f * q₁ + f * q₂)).map φ = P₀.g ^ (n + 1)
    simp only [Polynomial.map_mul, Polynomial.map_add, ← Polynomial.derivative_map, hf, hg, hq₁,
      hq₂, hP]
    ring
  letI : Algebra C S₀ := ((algebraMap C₀ S₀).comp φ).toAlgebra
  haveI : IsScalarTower C C₀ S₀ := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have hPf' : P.f.map (algebraMap C C₀) = P₀.f := hφ ▸ hPf
  have hPg' : P.g.map (algebraMap C C₀) = P₀.g ^ (n + 1) := hφ ▸ hPg
  have h1 : P.HasMap P₀.x :=
    (StandardEtalePair.hasMap_iff_of_map_eq hPf' hPg' P₀.x).mpr P₀.hasMap
  have h2' : P.HasMap ((1 : C₀) ⊗ₜ[C] P.X) :=
    (StandardEtalePair.hasMap_X (P := P)).map
      (Algebra.TensorProduct.includeRight (R := C) (A := C₀) (B := P.Ring))
  have h2 : P₀.HasMap ((1 : C₀) ⊗ₜ[C] P.X) :=
    (StandardEtalePair.hasMap_iff_of_map_eq hPf' hPg' _).mp h2'
  let F : C₀ ⊗[C] P.Ring →ₐ[C₀] S₀ :=
    Algebra.TensorProduct.lift (Algebra.ofId C₀ S₀) (P.lift P₀.x h1) (fun _ _ => .all _ _)
  let G : S₀ →ₐ[C₀] C₀ ⊗[C] P.Ring :=
    (P₀.lift ((1 : C₀) ⊗ₜ[C] P.X) h2).comp P₀.equivRing.toAlgHom
  have hF : F ((1 : C₀) ⊗ₜ[C] P.X) = P₀.x := by
    simp [F, Algebra.TensorProduct.lift_tmul, StandardEtalePair.lift_X]
  have hG : G P₀.x = (1 : C₀) ⊗ₜ[C] P.X := by
    simp [G, StandardEtalePresentation.equivRing_x, StandardEtalePair.lift_X]
  refine ⟨P.Ring, inferInstance, inferInstance, inferInstance, ⟨AlgEquiv.ofAlgHom F G ?_ ?_⟩⟩
  · apply P₀.hom_ext
    simp only [AlgHom.comp_apply, AlgHom.id_apply, hG, hF]
  · apply Algebra.TensorProduct.ext
    · exact Subsingleton.elim _ _
    · apply StandardEtalePair.hom_ext
      simp only [AlgHom.comp_apply, AlgHom.restrictScalars_apply,
        Algebra.TensorProduct.includeRight_apply, AlgHom.id_apply, hF, hG]

end Algebra
