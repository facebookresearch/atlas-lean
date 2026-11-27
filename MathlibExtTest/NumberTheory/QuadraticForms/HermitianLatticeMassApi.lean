/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.QuadraticForms.HermitianLatticeMass

open HermitianLattice NumberField TensorProduct
open scoped NumberField TensorProduct BigOperators nonZeroDivisors

variable {K E V : Type*} [Field K] [NumberField K] [IsTotallyReal K]
  [Field E] [NumberField E] [IsTotallyComplex E] [Algebra K E] [Algebra.IsQuadraticExtension K E]
  [AddCommGroup V] [Module E V] [Module.Finite E V] [Module (𝓞 E) V]
  [IsScalarTower (𝓞 E) E V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) (𝓞 E) V]
  [IsScalarTower (𝓞 K) E V]
  (h : DefiniteForm K E V) (L : FullLattice E V)
  (p : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) (hi : IsIntegralLattice h L)

local notation "𝒜[" p ", " K "]" =>
  AdicCompletion (IsDedekindDomain.HeightOneSpectrum.asIdeal p) (𝓞 K)
local notation "𝒬[" p ", " K ", " n "]" => (𝓞 K) ⧸ IsDedekindDomain.HeightOneSpectrum.asIdeal p ^ n

example (g : V ≃ₗ[E] V) :
    g ∈ unitaryGroup h ↔ ∀ x y, h.pairing (g x) (g y) = h.pairing x y := Iff.rfl

example (x : V) : x ∈ dual h L ↔ ∀ y : L.1, IsIntegral ℤ (h.pairing x y) := Iff.rfl

example (M : FullLattice E V) : M ∈ genus h L ↔
    ∀ p : IsDedekindDomain.HeightOneSpectrum (𝓞 K),
      Nonempty { f : (𝒜[p, K] ⊗[𝓞 K] L.1) ≃ₗ[𝒜[p, K] ⊗[𝓞 K] 𝓞 E]
          (𝒜[p, K] ⊗[𝓞 K] M.1) //
        ∀ x y, localPairing h 𝒜[p, K] M (f x) (f y) = localPairing h 𝒜[p, K] L x y } :=
  Iff.rfl

example : L ∈ genus h L := by
  change ∀ _, _
  intro _
  exact ⟨⟨LinearEquiv.refl _ _, fun _ _ ↦ rfl⟩⟩

example (a b : 𝒜[p, K]) (x y : L.1) :
    localPairing h 𝒜[p, K] L (a ⊗ₜ[𝓞 K] x) (b ⊗ₜ[𝓞 K] y) =
      (a * b) ⊗ₜ[𝓞 K] h.pairing x y := localPairing_tmul h _ L a b x y

example (N : ℕ) (a b : 𝒬[p, K, N]) (x y : L.1) :
    localIntegralPairing h 𝒬[p, K, N] L hi (a ⊗ₜ[𝓞 K] x) (b ⊗ₜ[𝓞 K] y) =
      TensorProduct.tmul (𝓞 K) (N := 𝓞 E) (a * b) ⟨h.pairing x y, hi x.2 y⟩ :=
  localIntegralPairing_tmul h _ L hi a b x y

example : IsUnimodular h L ↔ L.1 = dual h L := Iff.rfl

example (hu : IsUnimodular h L) : IsUnimodularAt h L p := by
  change L.1 = dual h L at hu
  rw [isUnimodularAt_iff, hu]

example (N : ℕ) : Nonempty (PreservingEnd h L hi p N) :=
  ⟨⟨LinearMap.id, fun _ _ ↦ rfl⟩⟩

example (N : ℕ) : normalizedCount h L hi p N =
    letI := Fintype.ofFinite (PreservingEnd h L hi p N)
    (Fintype.card (PreservingEnd h L hi p N) : ℝ) /
      (p.asIdeal.absNorm : ℝ) ^ (N * Module.finrank E V * Module.finrank E V) := rfl

example (hp : Finite (GenusClasses h L)) (hs : ∀ M : genus h L, Finite (stabilizer h M.1)) :
    (massAndLocalFactors h L).mass hp hs =
      letI := hp
      letI := Fintype.ofFinite (GenusClasses h L)
      ∑ c : GenusClasses h L, classWeight h L hs c := massAndLocalFactors_mass h L hp hs

example (hf : Module.length 𝒜[p, K] (CompletedDualQuotient h L hi p) ≠ ⊤)
    (β : LocalDensity h L hi p) (hb : β.1 ≠ 0)
    (hr : p.asIdeal.ramificationIdxIn (𝓞 E) ≠ 2) (hi' : p.asIdeal.inertiaDegIn (𝓞 E) ≠ 2) :
    (massAndLocalFactors h L).localFactor hi p hf β hb =
      let q := p.asIdeal.absNorm
      let m := Module.finrank E V
      let t := (Module.length 𝒜[p, K] (CompletedDualQuotient h L hi p)).toNat
      (q : ℝ) ^ ((t : ℝ) * (m : ℝ) / 2) *
        (∏ j ∈ Finset.range m, (1 - ((q : ℝ) ^ (j + 1))⁻¹)) / β.1 := by
  rw [massAndLocalFactors_localFactor]
  simp [hr, hi']

example (hf : Module.length 𝒜[p, K] (CompletedDualQuotient h L hi p) ≠ ⊤)
    (β : LocalDensity h L hi p) (hb : β.1 ≠ 0)
    (hr : p.asIdeal.ramificationIdxIn (𝓞 E) ≠ 2) (hi' : p.asIdeal.inertiaDegIn (𝓞 E) = 2) :
    (massAndLocalFactors h L).localFactor hi p hf β hb =
      let q := p.asIdeal.absNorm
      let m := Module.finrank E V
      let t := (Module.length 𝒜[p, K] (CompletedDualQuotient h L hi p)).toNat
      (q : ℝ) ^ ((t : ℝ) * (m : ℝ) / 2) *
        (∏ j ∈ Finset.range m, (1 - ((-(q : ℝ)) ^ (j + 1))⁻¹)) / β.1 := by
  rw [massAndLocalFactors_localFactor]
  simp [hr, hi']

example (hf : Module.length 𝒜[p, K] (CompletedDualQuotient h L hi p) ≠ ⊤)
    (β : LocalDensity h L hi p) (hb : β.1 ≠ 0) (hr : p.asIdeal.ramificationIdxIn (𝓞 E) = 2)
    (he : Even (Module.finrank E V)) :
    (massAndLocalFactors h L).localFactor hi p hf β hb =
      let q := p.asIdeal.absNorm
      let m := Module.finrank E V
      let t := (Module.length 𝒜[p, K] (CompletedDualQuotient h L hi p)).toNat
      let d := Ideal.discriminantIdeal (𝓞 K) (𝓞 E)
      let ord := FractionalIdeal.count K p (d : FractionalIdeal (𝓞 K)⁰ K)
      (q : ℝ) ^ ((t : ℝ) * (m : ℝ) / 2 + (ord : ℝ) * (m : ℝ) / 2) *
        (∏ j ∈ Finset.range (m / 2), (1 - ((q : ℝ) ^ (2 * (j + 1)))⁻¹)) / β.1 := by
  rw [massAndLocalFactors_localFactor]
  simp [hr, he]
