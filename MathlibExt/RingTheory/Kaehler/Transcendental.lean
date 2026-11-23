/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_KaehlerDifferential_D_ne_zero_of_transcendental.lean`,
`P2M/Sol/S_KaehlerDifferential_D_ne_zero_of_transcendental.lean`,
`Theorems/Thm_KaehlerDifferential_span_D_eq_top_of_transcendental.lean`,
`P2M/Sol/S_KaehlerDifferential_span_D_eq_top_of_transcendental.lean`,
`Theorems/Thm_KaehlerDifferential_exists_unique_smul_D_of_transcendental.lean` and
`P2M/Sol/S_KaehlerDifferential_exists_unique_smul_D_of_transcendental.lean`
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

public import Mathlib.RingTheory.Etale.Kaehler
public import Mathlib.RingTheory.Etale.Field
public import Mathlib.RingTheory.Kaehler.Polynomial
public import Mathlib.FieldTheory.RatFunc.AsPolynomial
public import Mathlib.LinearAlgebra.TensorProduct.Basis

/-!
# Kähler differentials of a transcendental element

For a transcendental element `x` of a field extension `F / K` with `F`
separable over `K(x)`, the differential `D x` is a basis element of the
module of Kähler differentials `Ω[F⁄K]`: it is nonzero, it spans, and every
differential is uniquely a scalar multiple of it.
-/

@[expose] public section

open scoped Polynomial

namespace KaehlerDifferential

/-- The differential of a transcendental separable element is a basis element
of the Kähler differentials: transport the polynomial basis along the
isomorphism `K(x) ≃ RatFunc K` and the formally étale base change to `F`. -/
private theorem exists_basis_D {K F : Type*} [Field K] [Field F]
    [Algebra K F] {x : F} (hx : Transcendental K x)
    [Algebra.IsSeparable (IntermediateField.adjoin K ({x} : Set F)) F] :
    ∃ b : Module.Basis Unit F (KaehlerDifferential K F),
      b () = KaehlerDifferential.D K F x := by
  let e : RatFunc K ≃ₐ[K] IntermediateField.adjoin K ({x} : Set F) :=
    RatFunc.algEquivOfTranscendental x hx
  let algKx : Algebra K[X] (IntermediateField.adjoin K ({x} : Set F)) :=
    (e.toAlgHom.toRingHom.comp (algebraMap K[X] (RatFunc K))).toAlgebra
  let algF : Algebra K[X] F :=
    ((algebraMap (IntermediateField.adjoin K ({x} : Set F)) F).comp
      (algebraMap K[X] (IntermediateField.adjoin K ({x} : Set F)))).toAlgebra
  have : IsScalarTower K[X] (IntermediateField.adjoin K ({x} : Set F)) F :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have : IsScalarTower K K[X] (IntermediateField.adjoin K ({x} : Set F)) :=
    IsScalarTower.of_algebraMap_eq (fun c => by
      change _ = (e.toAlgHom.toRingHom.comp (algebraMap K[X] (RatFunc K))) (Polynomial.C c)
      simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
        AlgEquiv.coe_toAlgHom]
      rw [← Polynomial.algebraMap_eq,
        ← IsScalarTower.algebraMap_apply K K[X] (RatFunc K), AlgEquiv.commutes])
  have : IsScalarTower K K[X] F := IsScalarTower.of_algebraMap_eq (fun c => by
    rw [IsScalarTower.algebraMap_apply K (IntermediateField.adjoin K ({x} : Set F)) F,
      IsScalarTower.algebraMap_apply K[X] (IntermediateField.adjoin K ({x} : Set F)) F,
      ← IsScalarTower.algebraMap_apply K K[X] (IntermediateField.adjoin K ({x} : Set F))])
  have : Algebra.FormallyEtale K[X] (RatFunc K) :=
    Algebra.FormallyEtale.of_isLocalization (nonZeroDivisors K[X])
  have : Algebra.FormallyEtale K[X] (IntermediateField.adjoin K ({x} : Set F)) :=
    Algebra.FormallyEtale.of_equiv (R := K[X]) (A := RatFunc K)
      { e with commutes' := fun _ => rfl }
  have : Algebra.FormallyEtale (IntermediateField.adjoin K ({x} : Set F)) F :=
    Algebra.FormallyEtale.of_isSeparable (IntermediateField.adjoin K ({x} : Set F)) F
  have : Algebra.FormallyEtale K[X] F :=
    Algebra.FormallyEtale.comp K[X] (IntermediateField.adjoin K ({x} : Set F)) F
  let b₀ : Module.Basis Unit K[X] (KaehlerDifferential K K[X]) :=
    (Module.Basis.singleton Unit K[X]).map (KaehlerDifferential.polynomialEquiv K).symm
  have hb₀ : b₀ () = KaehlerDifferential.D K K[X] Polynomial.X := by simp [b₀]
  let ψ := KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale K K[X] F
  refine ⟨(b₀.baseChange F).map ψ, ?_⟩
  have hX : algebraMap K[X] F Polynomial.X = x := by
    change algebraMap (IntermediateField.adjoin K ({x} : Set F)) F
        (e (algebraMap K[X] (RatFunc K) Polynomial.X)) = x
    rw [RatFunc.algebraMap_X]
    exact RatFunc.algEquivOfTranscendental_X x hx
  simp only [Module.Basis.map_apply, Module.Basis.baseChange_apply, hb₀, ψ,
    KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale_apply,
    KaehlerDifferential.mapBaseChange_tmul, one_smul, KaehlerDifferential.map_D, hX]

/-- The differential of a transcendental separable element is nonzero. -/
theorem D_ne_zero_of_transcendental (K : Type*) [Field K] {F : Type*} [Field F]
    [Algebra K F] (x : F) (hx : Transcendental K x)
    [Algebra.IsSeparable (IntermediateField.adjoin K ({x} : Set F)) F] :
    KaehlerDifferential.D K F x ≠ 0 := by
  obtain ⟨b, hb⟩ := exists_basis_D hx
  simpa [hb] using b.ne_zero ()

/-- The differential of a transcendental separable element spans the Kähler
differentials. -/
theorem span_D_eq_top_of_transcendental (K : Type*) [Field K] {F : Type*} [Field F]
    [Algebra K F] (x : F) (hx : Transcendental K x)
    [Algebra.IsSeparable (IntermediateField.adjoin K ({x} : Set F)) F] :
    Submodule.span F ({KaehlerDifferential.D K F x} : Set (KaehlerDifferential K F)) = ⊤ := by
  obtain ⟨b, hb⟩ := exists_basis_D hx
  have h := b.span_eq
  rwa [show Set.range b = {KaehlerDifferential.D K F x} by
    ext ω; simp [Set.range_unique, hb]] at h

/-- Every Kähler differential is uniquely a scalar multiple of the
differential of a transcendental separable element. -/
theorem exists_unique_smul_D_of_transcendental (K : Type*) [Field K] {F : Type*}
    [Field F] [Algebra K F] (x : F) (hx : Transcendental K x)
    [Algebra.IsSeparable (IntermediateField.adjoin K ({x} : Set F)) F]
    (ω : KaehlerDifferential K F) :
    ∃! c : F, ω = c • KaehlerDifferential.D K F x := by
  have hmem : ω ∈ Submodule.span F
      ({KaehlerDifferential.D K F x} : Set (KaehlerDifferential K F)) := by
    rw [span_D_eq_top_of_transcendental K x hx]
    exact Submodule.mem_top
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hmem
  refine ⟨c, rfl, fun c' hc' => ?_⟩
  have h : (c' - c) • KaehlerDifferential.D K F x = 0 := by
    rw [sub_smul, ← hc', sub_self]
  rcases smul_eq_zero.mp h with h | h
  · exact sub_eq_zero.mp h
  · exact absurd h (D_ne_zero_of_transcendental K x hx)

end KaehlerDifferential
