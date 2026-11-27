/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from the following files
in https://github.com/anthropics/fermats-last-theorem
at commit 6e837e75355538c7f80bab5b956861e86c4eacc2:
`Definitions/Def_CerednikDrinfeld_FormalUpperHalfPlanePoints.lean`,
the theorem files `Theorems/Thm_<Y>.lean` and solution files `P2M/Sol/S_<Y>.lean`
for `<Y>` in the list below, where `CF_` abbreviates `CerednikDrinfeld_FormalOmega_`:
`CF_DeligneDatum_exists_drinfeldDatum_isQuadrupleOf_of_inEdgeChart`
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
The upstream NOTICE also credits Mathlib as a whole:
https://github.com/leanprover-community/mathlib4
Copyright (c) the respective Mathlib authors, as recorded in the headers of the
Mathlib source files.
Released under the Apache License, Version 2.0.
The source is machine-generated proof code built around a proof-extraction
framework; the statements and proofs are reused here with that machinery
removed and the names restated in Mathlib style.
-/

module

public import MathlibExt.AlgebraicGeometry.FormalOmega.DrinfeldDatum
public import MathlibExt.AlgebraicGeometry.FormalOmega.InvertibleModule

/-!
# Helpers for `QuadrupleLocal`

Auxiliary constructions for the local construction of a Drinfeld datum from a Deligne datum
in an edge chart, split out of `QuadrupleLocal` to keep files short.
-/

@[expose] public section

noncomputable section

open scoped TensorProduct MatrixGroups Matrix
open LT.LatticeTree CerednikDrinfeld CerednikDrinfeld.FormalOmega

namespace CerednikDrinfeld.FormalOmega.QuadrupleLocal

section DiagFst
variable {K : Type} [Field K]

/-- The diagonal matrix `diag(x, 1)` as an element of `GL₂(K)`. -/
def diagFstGL (x : Kˣ) : Matrix.GeneralLinearGroup (Fin 2) K :=
  ⟨Matrix.diagonal ![(x : K), 1], Matrix.diagonal ![((x⁻¹ : Kˣ) : K), 1], by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext i
    fin_cases i <;> simp, by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext i
    fin_cases i <;> simp⟩

/-- The underlying matrix of `diagFstGL x`. -/
theorem diagFstGL_coe (x : Kˣ) :
    ((diagFstGL x : Matrix.GeneralLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
      Matrix.diagonal ![(x : K), 1] := rfl

end DiagFst

variable {𝒪 : Type} [CommRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K]
variable {B : Type} [CommRing B] [Algebra 𝒪 B]

/-- The stalk at `x` of the quotient by `N`, as a map out of the base change of `L` to the local
ring at `x`. -/
noncomputable def stalkQuot (x : PrimeSpectrum B) (L : FullLattice 𝒪 K)
    (N : Submodule B (latticeBaseChange 𝒪 K B L)) :
    latticeBaseChange 𝒪 K (locRing B x) L →ₗ[locRing B x] stalk B x (latticeBaseChange 𝒪 K B L ⧸ N)
        :=
  (IsLocalizedModule.isBaseChange x.asIdeal.primeCompl (locRing B x)
      (LocalizedModule.mkLinearMap x.asIdeal.primeCompl
          (latticeBaseChange 𝒪 K B L ⧸ N))).equiv.toLinearMap
    ∘ₗ quotBaseChange (locRing B x) L N

/-- The kernel of `stalkQuot` is the base change of `N` to the local ring at `x`. -/
theorem ker_stalkQuot (x : PrimeSpectrum B) (L : FullLattice 𝒪 K)
    (N : Submodule B (latticeBaseChange 𝒪 K B L)) :
    LinearMap.ker (stalkQuot x L N) = lineBaseChange (toLocRing B x) L N := by
  rw [stalkQuot, LinearMap.ker_comp, LinearEquiv.ker, Submodule.comap_bot,
    lineBaseChange_eq_ker (toLocRing B x) (fun _ => rfl) L N]

/-- `stalkQuot` is surjective. -/
theorem stalkQuot_surjective (x : PrimeSpectrum B) (L : FullLattice 𝒪 K)
    (N : Submodule B (latticeBaseChange 𝒪 K B L)) :
    Function.Surjective (stalkQuot x L N) := by
  rw [stalkQuot, LinearMap.coe_comp]
  exact (LinearEquiv.surjective _).comp (quotBaseChange_surjective L N)

/-- `stalkQuot` sends `1 ⊗ v` to the class of `1 ⊗ v` in the stalk. -/
theorem stalkQuot_one_tmul (x : PrimeSpectrum B) (L : FullLattice 𝒪 K)
    (N : Submodule B (latticeBaseChange 𝒪 K B L))
    (v : ↥L.1) :
    stalkQuot x L N ((1 : locRing B x) ⊗ₜ[𝒪] v) =
      LocalizedModule.mkLinearMap x.asIdeal.primeCompl _ (N.mkQ ((1 : B) ⊗ₜ[𝒪] v)) := by
  rw [stalkQuot, LinearMap.comp_apply, LinearEquiv.coe_coe, ← rTensor_one_tmul (toLocRing B x) L v,
    quotBaseChange_rTensor (toLocRing B x) (fun _ => rfl), IsBaseChange.equiv_tmul, one_smul]

section NotMem
variable {B : Type} [CommRing B]

/-- An element of a projective module on which every linear form takes values in `I` lies in `I •
⊤`. -/
theorem mem_smul_top_of_forall_form {P : Type} [AddCommGroup P] [Module B P] [Module.Projective B P]
    (I : Ideal B) (t : P) (h : ∀ φ : P →ₗ[B] B, φ t ∈ I) : t ∈ I • (⊤ : Submodule B P) := by
  classical
  obtain ⟨s, hs⟩ := Module.Projective.out (R := B) (P := P)
  have ht : t = Finsupp.linearCombination B (id : P → P) (s t) := (hs t).symm
  rw [ht, Finsupp.linearCombination_apply]
  refine Submodule.sum_mem _ fun p _ => ?_
  refine Submodule.smul_mem_smul (h ((Finsupp.lapply p) ∘ₗ s)) Submodule.mem_top

/-- If `b / 1` lies in `𝔭 • ⊤` in the localization at `𝔭`, then `b ∈ 𝔭`. -/
theorem mem_of_mk_mem_smul_top (x : PrimeSpectrum B) (b : B)
    (hb : (LocalizedModule.mk b 1 : LocalizedModule x.asIdeal.primeCompl B) ∈
      x.asIdeal • (⊤ : Submodule B (LocalizedModule x.asIdeal.primeCompl B))) : b ∈ x.asIdeal := by
  have key : ∀ w : LocalizedModule x.asIdeal.primeCompl B, w ∈ x.asIdeal • (⊤ : Submodule B _) →
      ∃ (b' : B) (s : x.asIdeal.primeCompl), b' ∈ x.asIdeal ∧ w = LocalizedModule.mk b' s := by
    intro w hw
    refine Submodule.smul_induction_on hw ?_ ?_
    · intro r hr n _
      induction n using LocalizedModule.induction_on with
      | h c s => exact ⟨r * c, s, x.asIdeal.mul_mem_right c hr,
          by rw [LocalizedModule.smul'_mk, smul_eq_mul]⟩
    · rintro w₁ w₂ ⟨b₁, s₁, h₁, rfl⟩ ⟨b₂, s₂, h₂, rfl⟩
      refine ⟨(s₂ : B) * b₁ + (s₁ : B) * b₂, s₁ * s₂, x.asIdeal.add_mem
          (x.asIdeal.mul_mem_left _ h₁)
        (x.asIdeal.mul_mem_left _ h₂), ?_⟩
      rw [LocalizedModule.mk_add_mk]
      simp only [Submonoid.smul_def, smul_eq_mul]
  obtain ⟨b', s, hb', he⟩ := key _ hb
  rw [LocalizedModule.mk_eq] at he
  obtain ⟨u, hu⟩ := he
  simp only [Submonoid.smul_def, smul_eq_mul, OneMemClass.coe_one, one_mul] at hu
  have : (u : B) * ((s : B) * b) ∈ x.asIdeal := by rw [hu]; exact x.asIdeal.mul_mem_left _ hb'
  rcases x.isPrime.mem_or_mem this with h | h
  · exact absurd h u.2
  · rcases x.isPrime.mem_or_mem h with h | h
    · exact absurd h s.2
    · exact h

end NotMem

section Chart
variable [IsFractionRing 𝒪 K] {π : 𝒪}
variable {M' M : FullLattice 𝒪 K} (d : DeligneDatum (K := K) π B)

/-- The quotient of the base change of `M'` by the line of `d`. -/
abbrev T0 (M' : FullLattice 𝒪 K) : Type := latticeBaseChange 𝒪 K B M' ⧸ d.line M'

/-- The quotient of the base change of `M` by the line of `d`. -/
abbrev T1 (M : FullLattice 𝒪 K) : Type := latticeBaseChange 𝒪 K B M ⧸ d.line M

/-- The quotient `T0 d M'` is an invertible module. -/
scoped instance instInvertibleT0 (M' : FullLattice 𝒪 K) : Module.Invertible B (T0 d M') :=
    d.invertible M'

/-- The map `T0 d M' → T1 d M` induced by the inclusion `M' ⊆ M`. -/
noncomputable def Pi0 (hle : M'.1 ≤ M.1) : T0 d M' →ₗ[B] T1 d M :=
  Submodule.mapQ _ _ (inclBaseChange B hle) (Submodule.map_le_iff_le_comap.mp (d.mono hle))

/-- The image of an irreducible `π` in `K` is nonzero. -/
theorem hπK_of_irreducible (hπ : Irreducible π) : algebraMap 𝒪 K π ≠ 0 :=
  (map_ne_zero_iff (algebraMap 𝒪 K) (IsFractionRing.injective 𝒪 K)).mpr hπ.ne_zero

/-- The image of an irreducible `π` in `K`, as a unit. -/
noncomputable def piUnit (hπ : Irreducible π) : Kˣ := Units.mk0 _ (hπK_of_irreducible (K := K) hπ)

/-- `π M ⊆ M'` as lattices. -/
theorem act_piUnit_le (hπ : Irreducible π) (hπM : ∀ v ∈ M.1, algebraMap 𝒪 K π • v ∈ M'.1) :
    (FullLattice.act (scalarGL (piUnit (K := K) hπ)) M).1 ≤ M'.1 := by
  intro v hv
  obtain ⟨w, hw, rfl⟩ := mem_latticeMap_scalarGL.mp hv
  exact hπM w hw

/-- The base change of multiplication by `π` factors through the homothety by `π`. -/
theorem smulInto_baseChange_eq (hπ : Irreducible π) (hπM : ∀ v ∈ M.1, algebraMap 𝒪 K π • v ∈ M'.1) :
    ((smulInto π hπM).baseChange B : latticeBaseChange 𝒪 K B M →ₗ[B] latticeBaseChange 𝒪 K B M') =
      (inclBaseChange B (act_piUnit_le hπ hπM)) ∘ₗ (actBaseChange B (scalarGL (piUnit (K := K) hπ))
          M).toLinearMap := by
  refine TensorProduct.AlgebraTensorModule.ext fun b v => ?_
  rw [LinearMap.baseChange_tmul, LinearMap.comp_apply, LinearEquiv.coe_coe]
  change _ = inclBaseChange B (act_piUnit_le hπ hπM)
    (((latticeMapEquiv (scalarGL (piUnit (K := K) hπ)) M.1).baseChange 𝒪 B _ _) (b ⊗ₜ[𝒪] v))
  rw [LinearEquiv.baseChange_tmul, inclBaseChange]
  erw [LinearMap.baseChange_tmul]
  congr 1
  apply Subtype.ext
  rw [coe_smulInto_apply]
  change algebraMap 𝒪 K π • (v : Fin 2 → K) =
    Matrix.mulVec ((scalarGL (piUnit (K := K) hπ) : Matrix.GeneralLinearGroup (Fin 2) K) : Matrix
        (Fin 2) (Fin 2) K)
      (v : Fin 2 → K)
  rw [scalarGL_mulVec]
  rfl

/-- Multiplication by `π` maps the line at `M` into the line at `M'`. -/
theorem map_smulInto_le (hπ : Irreducible π) (hπM : ∀ v ∈ M.1, algebraMap 𝒪 K π • v ∈ M'.1) :
    (d.line M).map ((smulInto π hπM).baseChange B :
      latticeBaseChange 𝒪 K B M →ₗ[B] latticeBaseChange 𝒪 K B M') ≤ d.line M' := by
  rw [smulInto_baseChange_eq hπ hπM, Submodule.map_comp, ← d.homothety (piUnit (K := K) hπ) M]
  exact d.mono (act_piUnit_le hπ hπM)

/-- The map `T1 d M → T0 d M'` induced by multiplication by `π`. -/
noncomputable def Pi1 (hπ : Irreducible π) (hπM : ∀ v ∈ M.1, algebraMap 𝒪 K π • v ∈ M'.1) :
    T1 d M →ₗ[B] T0 d M' :=
  Submodule.mapQ _ _ ((smulInto π hπM).baseChange B) (Submodule.map_le_iff_le_comap.mp
      (map_smulInto_le d hπ hπM))

omit [IsFractionRing 𝒪 K] in
/-- Multiplication by `π` after the inclusion is scalar multiplication by `π`. -/
theorem smul_incl_apply (hle : M'.1 ≤ M.1) (hπM : ∀ v ∈ M.1, algebraMap 𝒪 K π • v ∈ M'.1)
    (y : latticeBaseChange 𝒪 K B M') :
    ((smulInto π hπM).baseChange B) (inclBaseChange B hle y) = algebraMap 𝒪 B π • y := by
  induction y using TensorProduct.inductionOn with
  | add y z hy hz => simp only [map_add, smul_add, hy, hz]
  | tmul c v =>
    rw [inclBaseChange, LinearMap.baseChange_tmul, LinearMap.baseChange_tmul, algebraMap_smul,
      TensorProduct.smul_tmul', TensorProduct.smul_tmul]
    congr 1
    apply Subtype.ext
    rw [coe_smulInto_apply, Submodule.coe_inclusion, Submodule.coe_smul, algebraMap_smul]

omit [IsFractionRing 𝒪 K] in
/-- The inclusion after multiplication by `π` is scalar multiplication by `π`. -/
theorem incl_smul_apply (hle : M'.1 ≤ M.1) (hπM : ∀ v ∈ M.1, algebraMap 𝒪 K π • v ∈ M'.1)
    (y : latticeBaseChange 𝒪 K B M) :
    (inclBaseChange B hle) (((smulInto π hπM).baseChange B) y) = algebraMap 𝒪 B π • y := by
  induction y using TensorProduct.inductionOn with
  | add y z hy hz => simp only [map_add, smul_add, hy, hz]
  | tmul c v =>
    rw [inclBaseChange, LinearMap.baseChange_tmul, LinearMap.baseChange_tmul, algebraMap_smul,
      TensorProduct.smul_tmul', TensorProduct.smul_tmul]
    congr 1
    apply Subtype.ext
    rw [Submodule.coe_inclusion, coe_smulInto_apply, Submodule.coe_smul, algebraMap_smul]

/-- `Pi1 ∘ Pi0` is multiplication by `π`. -/
theorem Pi1_Pi0 (hπ : Irreducible π) (hle : M'.1 ≤ M.1)
    (hπM : ∀ v ∈ M.1, algebraMap 𝒪 K π • v ∈ M'.1)
    (t : T0 d M') : Pi1 d hπ hπM (Pi0 d hle t) = algebraMap 𝒪 B π • t := by
  obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective _ t
  change ((d.line M).mapQ _ _ _) (((d.line M').mapQ _ _ _) (Submodule.Quotient.mk y)) = _
  rw [Submodule.mapQ_apply, Submodule.mapQ_apply, smul_incl_apply hle hπM,
      Submodule.Quotient.mk_smul]
  rfl

/-- `Pi0 ∘ Pi1` is multiplication by `π`. -/
theorem Pi0_Pi1 (hπ : Irreducible π) (hle : M'.1 ≤ M.1)
    (hπM : ∀ v ∈ M.1, algebraMap 𝒪 K π • v ∈ M'.1)
    (t : T1 d M) : Pi0 d hle (Pi1 d hπ hπM t) = algebraMap 𝒪 B π • t := by
  obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective _ t
  change ((d.line M').mapQ _ _ _) (((d.line M).mapQ _ _ _) (Submodule.Quotient.mk y)) = _
  rw [Submodule.mapQ_apply, Submodule.mapQ_apply, incl_smul_apply hle hπM,
      Submodule.Quotient.mk_smul]
  rfl

/-- `Pi1 ∘ₗ Pi0` is multiplication by `π`, as linear maps. -/
theorem Pi1_comp_Pi0 (hπ : Irreducible π) (hle : M'.1 ≤ M.1)
    (hπM : ∀ v ∈ M.1, algebraMap 𝒪 K π • v ∈ M'.1) :
    Pi1 d hπ hπM ∘ₗ Pi0 d hle = algebraMap 𝒪 B π • LinearMap.id :=
  LinearMap.ext fun t => by simpa using Pi1_Pi0 d hπ hle hπM t

/-- The closed set of primes at which `Pi0` vanishes modulo the prime. -/
def S0 (hle : M'.1 ≤ M.1) : Set (PrimeSpectrum B) :=
  {x | LinearMap.range (Pi0 d hle) ≤ x.asIdeal • (⊤ : Submodule B (T1 d M))}

/-- The closed set of primes at which `Pi1` vanishes modulo the prime. -/
def S1 (hπ : Irreducible π) (hπM : ∀ v ∈ M.1, algebraMap 𝒪 K π • v ∈ M'.1) : Set (PrimeSpectrum B)
    :=
  {x | LinearMap.range (Pi1 d hπ hπM) ≤ x.asIdeal • (⊤ : Submodule B (T0 d M'))}

omit [IsFractionRing 𝒪 K] in
/-- `S0` is closed. -/
theorem isClosed_S0 (hle : M'.1 ≤ M.1) : IsClosed (S0 d (M := M) hle) :=
  Module.isClosed_setOf_range_le_smul_top (Pi0 d hle)

/-- `S1` is closed. -/
theorem isClosed_S1 (hπ : Irreducible π) (hπM : ∀ v ∈ M.1, algebraMap 𝒪 K π • v ∈ M'.1) :
    IsClosed (S1 d hπ hπM) :=
  Module.isClosed_setOf_range_le_smul_top (Pi1 d hπ hπM)

/-- Every prime lies in `S0` or `S1` when `π` is nilpotent in `B`. -/
theorem mem_S0_or_mem_S1 (hπ : Irreducible π) (hle : M'.1 ≤ M.1)
    (hπM : ∀ v ∈ M.1, algebraMap 𝒪 K π • v ∈ M'.1)
    (hB : IsNilpotent (algebraMap 𝒪 B π)) (x : PrimeSpectrum B) :
    x ∈ S0 d (M := M) hle ∨ x ∈ S1 d hπ hπM := by
  have hπmem : algebraMap 𝒪 B π ∈ x.asIdeal := by
    obtain ⟨n, hn⟩ := hB
    exact x.isPrime.mem_of_pow_mem n (hn ▸ x.asIdeal.zero_mem)
  exact Module.Invertible.range_le_smul_top_or_of_comp_eq_smul (Pi0 d hle) (Pi1 d hπ hπM) _
    (Pi1_comp_Pi0 d hπ hle hπM) x hπmem

end Chart

section Local
variable [IsFractionRing 𝒪 K] {π : 𝒪}
variable {M' M : FullLattice 𝒪 K} (d : DeligneDatum (K := K) π B)

/-- The inverse of the stalk of `Pi0` at a prime outside `S0`. -/
noncomputable def Pi0inv (hle : M'.1 ≤ M.1) (x : PrimeSpectrum B) (hx : x ∉ S0 d (M := M) hle) :
    stalk B x (T1 d M) ≃ₗ[locRing B x] stalk B x (T0 d M') :=
  (LinearEquiv.ofBijective (LocalizedModule.map x.asIdeal.primeCompl (Pi0 d hle))
    (Module.Invertible.bijective_localizedModule_map_of_not_range_le (Pi0 d hle) x hx)).symm

omit [IsFractionRing 𝒪 K] in
/-- `Pi0inv` is a right inverse of the stalk of `Pi0`. -/
theorem map_Pi0_Pi0inv (hle : M'.1 ≤ M.1) (x : PrimeSpectrum B) (hx : x ∉ S0 d (M := M) hle)
    (t : stalk B x (T1 d M)) :
    LocalizedModule.map x.asIdeal.primeCompl (Pi0 d hle) (Pi0inv d hle x hx t) = t :=
  (LinearEquiv.ofBijective (LocalizedModule.map x.asIdeal.primeCompl (Pi0 d hle))
    (Module.Invertible.bijective_localizedModule_map_of_not_range_le (Pi0 d hle) x
        hx)).apply_symm_apply t

omit [IsFractionRing 𝒪 K] in
/-- `Pi0inv` is a left inverse of the stalk of `Pi0`. -/
theorem Pi0inv_map_Pi0 (hle : M'.1 ≤ M.1) (x : PrimeSpectrum B) (hx : x ∉ S0 d (M := M) hle)
    (t : stalk B x (T0 d M')) :
    Pi0inv d hle x hx (LocalizedModule.map x.asIdeal.primeCompl (Pi0 d hle) t) = t :=
  (LinearEquiv.ofBijective (LocalizedModule.map x.asIdeal.primeCompl (Pi0 d hle))
    (Module.Invertible.bijective_localizedModule_map_of_not_range_le (Pi0 d hle) x
        hx)).symm_apply_apply t

/-- The inverse of the stalk of `Pi1` at a prime outside `S1`. -/
noncomputable def Pi1inv (hπ : Irreducible π) (hπM : ∀ v ∈ M.1, algebraMap 𝒪 K π • v ∈ M'.1)
    (x : PrimeSpectrum B)
    (hx : x ∉ S1 d hπ hπM) : stalk B x (T0 d M') ≃ₗ[locRing B x] stalk B x (T1 d M) :=
  (LinearEquiv.ofBijective (LocalizedModule.map x.asIdeal.primeCompl (Pi1 d hπ hπM))
    (Module.Invertible.bijective_localizedModule_map_of_not_range_le (Pi1 d hπ hπM) x hx)).symm

/-- `Pi1inv` is a right inverse of the stalk of `Pi1`. -/
theorem map_Pi1_Pi1inv (hπ : Irreducible π) (hπM : ∀ v ∈ M.1, algebraMap 𝒪 K π • v ∈ M'.1)
    (x : PrimeSpectrum B)
    (hx : x ∉ S1 d hπ hπM) (t : stalk B x (T0 d M')) :
    LocalizedModule.map x.asIdeal.primeCompl (Pi1 d hπ hπM) (Pi1inv d hπ hπM x hx t) = t :=
  (LinearEquiv.ofBijective (LocalizedModule.map x.asIdeal.primeCompl (Pi1 d hπ hπM))
    (Module.Invertible.bijective_localizedModule_map_of_not_range_le (Pi1 d hπ hπM) x
        hx)).apply_symm_apply t

/-- `Pi1inv` is a left inverse of the stalk of `Pi1`. -/
theorem Pi1inv_map_Pi1 (hπ : Irreducible π) (hπM : ∀ v ∈ M.1, algebraMap 𝒪 K π • v ∈ M'.1)
    (x : PrimeSpectrum B)
    (hx : x ∉ S1 d hπ hπM) (t : stalk B x (T1 d M)) :
    Pi1inv d hπ hπM x hx (LocalizedModule.map x.asIdeal.primeCompl (Pi1 d hπ hπM) t) = t :=
  (LinearEquiv.ofBijective (LocalizedModule.map x.asIdeal.primeCompl (Pi1 d hπ hπM))
    (Module.Invertible.bijective_localizedModule_map_of_not_range_le (Pi1 d hπ hπM) x
        hx)).symm_apply_apply t

/-- The lattice `π⁻¹ M'`. -/
noncomputable abbrev Mpi (hπ : Irreducible π) (M' : FullLattice 𝒪 K) : FullLattice 𝒪 K :=
  FullLattice.act (scalarGL (piUnit (K := K) hπ)⁻¹) M'

/-- Multiplication by `π` maps `π⁻¹ M'` into `M'`. -/
theorem smul_mem_of_mem_Mpi (hπ : Irreducible π) (M' : FullLattice 𝒪 K) :
    ∀ v ∈ (Mpi (K := K) hπ M').1, algebraMap 𝒪 K π • v ∈ M'.1 := by
  intro v hv
  obtain ⟨w, hw, rfl⟩ := mem_latticeMap_scalarGL.mp hv
  have : algebraMap 𝒪 K π • (((piUnit (K := K) hπ)⁻¹ : Kˣ) : K) • w = w := by
    rw [smul_smul, Units.val_inv_eq_inv_val, show algebraMap 𝒪 K π = ((piUnit (K := K) hπ : Kˣ) : K)
        from rfl,
      mul_inv_cancel₀ (piUnit (K := K) hπ).ne_zero, one_smul]
  rw [this]; exact hw

/-- The base change to the local ring at `x` of multiplication by `π` from `π⁻¹ M'` to `M'`. -/
noncomputable def sPi (hπ : Irreducible π) (M' : FullLattice 𝒪 K) (x : PrimeSpectrum B) :
    latticeBaseChange 𝒪 K (locRing B x) (Mpi (K := K) hπ M') →ₗ[locRing B x] latticeBaseChange 𝒪 K
        (locRing B x) M' :=
  (smulInto π (smul_mem_of_mem_Mpi (K := K) hπ M')).baseChange (locRing B x)

/-- `sPi` is surjective. -/
theorem sPi_surjective (hπ : Irreducible π) (M' : FullLattice 𝒪 K) (x : PrimeSpectrum B) :
    Function.Surjective (sPi (B := B) hπ M' x) := by
  rw [sPi, LinearMap.baseChange_eq_lTensor]
  refine LinearMap.lTensor_surjective _ fun w => ?_
  refine ⟨⟨(((piUnit (K := K) hπ)⁻¹ : Kˣ) : K) • (w : Fin 2 → K), ?_⟩, ?_⟩
  · exact mem_latticeMap_scalarGL.mpr ⟨w, w.2, rfl⟩
  · apply Subtype.ext
    rw [coe_smulInto_apply, smul_smul, Units.val_inv_eq_inv_val,
      show algebraMap 𝒪 K π = ((piUnit (K := K) hπ : Kˣ) : K) from rfl,
          mul_inv_cancel₀ (piUnit (K := K) hπ).ne_zero,
      one_smul]

open Classical in
/-- The lattice and stalk map for `T0` at the prime `x`. -/
noncomputable def loc₀ (hle : M'.1 ≤ M.1) (x : PrimeSpectrum B) :
    Σ L : FullLattice 𝒪 K, (latticeBaseChange 𝒪 K (locRing B x) L →ₗ[locRing B x] stalk B x
        (T0 d M')) :=
  if hx : x ∈ S0 d (M := M) hle then ⟨M', stalkQuot x M' (d.line M')⟩
  else ⟨M, (Pi0inv d hle x hx).toLinearMap ∘ₗ stalkQuot x M (d.line M)⟩

open Classical in
/-- The lattice and stalk map for `T1` at the prime `x`. -/
noncomputable def loc₁ (hπ : Irreducible π) (hπM : ∀ v ∈ M.1, algebraMap 𝒪 K π • v ∈ M'.1)
    (x : PrimeSpectrum B) :
    Σ L : FullLattice 𝒪 K, (latticeBaseChange 𝒪 K (locRing B x) L →ₗ[locRing B x] stalk B x
        (T1 d M)) :=
  if hx : x ∈ S1 d hπ hπM then ⟨M, stalkQuot x M (d.line M)⟩
  else ⟨Mpi (K := K) hπ M', (Pi1inv d hπ hπM x hx).toLinearMap ∘ₗ stalkQuot x M' (d.line M') ∘ₗ sPi
      hπ M' x⟩

omit [IsFractionRing 𝒪 K] in
/-- `loc₀` on `S0`. -/
theorem loc₀_eq_of_mem (hle : M'.1 ≤ M.1) {x : PrimeSpectrum B} (hx : x ∈ S0 d (M := M) hle) :
    loc₀ d hle x = ⟨M', stalkQuot x M' (d.line M')⟩ := by
  simp only [loc₀, hx, ↓reduceDIte]

omit [IsFractionRing 𝒪 K] in
/-- `loc₀` off `S0`. -/
theorem loc₀_eq_of_not_mem (hle : M'.1 ≤ M.1) {x : PrimeSpectrum B} (hx : x ∉ S0 d (M := M) hle) :
    loc₀ d hle x = ⟨M, (Pi0inv d hle x hx).toLinearMap ∘ₗ stalkQuot x M (d.line M)⟩ := by
  simp only [loc₀, hx, ↓reduceDIte]

/-- `loc₁` on `S1`. -/
theorem loc₁_eq_of_mem (hπ : Irreducible π) (hπM : ∀ v ∈ M.1, algebraMap 𝒪 K π • v ∈ M'.1)
    {x : PrimeSpectrum B}
    (hx : x ∈ S1 d hπ hπM) : loc₁ d hπ hπM x = ⟨M, stalkQuot x M (d.line M)⟩ := by
  simp only [loc₁, hx, ↓reduceDIte]

/-- `loc₁` off `S1`. -/
theorem loc₁_eq_of_not_mem (hπ : Irreducible π) (hπM : ∀ v ∈ M.1, algebraMap 𝒪 K π • v ∈ M'.1)
    {x : PrimeSpectrum B}
    (hx : x ∉ S1 d hπ hπM) :
    loc₁ d hπ hπM x = ⟨Mpi (K := K) hπ M',
      (Pi1inv d hπ hπM x hx).toLinearMap ∘ₗ stalkQuot x M' (d.line M') ∘ₗ sPi hπ M' x⟩ := by
  simp only [loc₁, hx, ↓reduceDIte]

omit [IsFractionRing 𝒪 K] in
/-- The lattice of `loc₀` on `S0` is `M'`. -/
theorem loc₀_fst_of_mem (hle : M'.1 ≤ M.1) {x : PrimeSpectrum B} (hx : x ∈ S0 d (M := M) hle) :
    (loc₀ d hle x).1 = M' := by rw [loc₀_eq_of_mem d hle hx]

omit [IsFractionRing 𝒪 K] in
/-- The lattice of `loc₀` off `S0` is `M`. -/
theorem loc₀_fst_of_not_mem (hle : M'.1 ≤ M.1) {x : PrimeSpectrum B} (hx : x ∉ S0 d (M := M) hle) :
    (loc₀ d hle x).1 = M := by rw [loc₀_eq_of_not_mem d hle hx]

/-- The lattice of `loc₁` on `S1` is `M`. -/
theorem loc₁_fst_of_mem (hπ : Irreducible π) (hπM : ∀ v ∈ M.1, algebraMap 𝒪 K π • v ∈ M'.1)
    {x : PrimeSpectrum B}
    (hx : x ∈ S1 d hπ hπM) : (loc₁ d hπ hπM x).1 = M := by rw [loc₁_eq_of_mem d hπ hπM hx]

/-- The lattice of `loc₁` off `S1` is `π⁻¹ M'`. -/
theorem loc₁_fst_of_not_mem (hπ : Irreducible π) (hπM : ∀ v ∈ M.1, algebraMap 𝒪 K π • v ∈ M'.1)
    {x : PrimeSpectrum B}
    (hx : x ∉ S1 d hπ hπM) : (loc₁ d hπ hπM x).1 = FullLattice.act (scalarGL (piUnit (K := K) hπ)⁻¹)
        M' := by
  rw [loc₁_eq_of_not_mem d hπ hπM hx]

omit [IsFractionRing 𝒪 K] in
/-- The stalk map of `loc₀` is surjective. -/
theorem loc₀_surjective (hle : M'.1 ≤ M.1) (x : PrimeSpectrum B) : Function.Surjective
    (loc₀ d hle x).2 := by
  by_cases hx : x ∈ S0 d (M := M) hle
  · rw [loc₀_eq_of_mem d hle hx]; exact stalkQuot_surjective x M' (d.line M')
  · rw [loc₀_eq_of_not_mem d hle hx]
    exact (Pi0inv d hle x hx).surjective.comp (stalkQuot_surjective x M (d.line M))

/-- The stalk map of `loc₁` is surjective. -/
theorem loc₁_surjective (hπ : Irreducible π) (hπM : ∀ v ∈ M.1, algebraMap 𝒪 K π • v ∈ M'.1)
    (x : PrimeSpectrum B) :
    Function.Surjective (loc₁ d hπ hπM x).2 := by
  by_cases hx : x ∈ S1 d hπ hπM
  · rw [loc₁_eq_of_mem d hπ hπM hx]; exact stalkQuot_surjective x M (d.line M)
  · rw [loc₁_eq_of_not_mem d hπ hπM hx]
    exact (Pi1inv d hπ hπM x hx).surjective.comp
      ((stalkQuot_surjective x M' (d.line M')).comp (sPi_surjective hπ M' x))

omit [IsFractionRing 𝒪 K] in
/-- Naturality of `stalkQuot` in compatible maps of lattices. -/
theorem stalkQuot_naturality (x : PrimeSpectrum B) {L L' : FullLattice 𝒪 K}
    (N : Submodule B (latticeBaseChange 𝒪 K B L)) (N' : Submodule B (latticeBaseChange 𝒪 K B L'))
    (φ : ↥L.1 → ↥L'.1)
    (g : latticeBaseChange 𝒪 K B L →ₗ[B] latticeBaseChange 𝒪 K B L')
        (hg : ∀ v, g ((1 : B) ⊗ₜ[𝒪] v) = (1 : B) ⊗ₜ[𝒪] φ v)
    (hN : N ≤ N'.comap g)
    (gx : latticeBaseChange 𝒪 K (locRing B x) L →ₗ[locRing B x] latticeBaseChange 𝒪 K (locRing B x)
        L')
    (hgx : ∀ v, gx ((1 : locRing B x) ⊗ₜ[𝒪] v) = (1 : locRing B x) ⊗ₜ[𝒪] φ v)
    (w : latticeBaseChange 𝒪 K (locRing B x) L) :
    stalkQuot x L' N' (gx w) = LocalizedModule.map x.asIdeal.primeCompl (Submodule.mapQ N N' g hN)
        (stalkQuot x L N w) := by
  induction w using TensorProduct.inductionOn with
  | add w₁ w₂ h₁ h₂ => simp only [map_add, h₁, h₂]
  | tmul b v =>
    have hb : b ⊗ₜ[𝒪] v = b • ((1 : locRing B x) ⊗ₜ[𝒪] v) := by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [hb, map_smul, map_smul, map_smul, hgx, stalkQuot_one_tmul, stalkQuot_one_tmul,
      LocalizedModule.mkLinearMap_apply, LocalizedModule.mkLinearMap_apply, LinearMap.map_smul,
      LocalizedModule.map_mk, Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.mapQ_apply, hg]

omit [IsFractionRing 𝒪 K] in
/-- `stalkQuot` intertwines the inclusion `M' ⊆ M` with the stalk of `Pi0`. -/
theorem stalkQuot_incl (hle : M'.1 ≤ M.1) (x : PrimeSpectrum B)
    (w : latticeBaseChange 𝒪 K (locRing B x) M') :
    stalkQuot x M (d.line M) (inclBaseChange (locRing B x) hle w) =
      LocalizedModule.map x.asIdeal.primeCompl (Pi0 d hle) (stalkQuot x M' (d.line M') w) := by
  refine stalkQuot_naturality x (d.line M') (d.line M) (Submodule.inclusion hle)
      (inclBaseChange B hle)
    (fun v => ?_) _ (inclBaseChange (locRing B x) hle) (fun v => ?_) w
  · rw [inclBaseChange, LinearMap.baseChange_tmul]
  · rw [inclBaseChange, LinearMap.baseChange_tmul]

/-- `stalkQuot` intertwines multiplication by `π` with the stalk of `Pi1`. -/
theorem stalkQuot_smulInto (hπ : Irreducible π) (hπM : ∀ v ∈ M.1, algebraMap 𝒪 K π • v ∈ M'.1)
    (x : PrimeSpectrum B)
    (w : latticeBaseChange 𝒪 K (locRing B x) M) :
    stalkQuot x M' (d.line M') ((smulInto π hπM).baseChange (locRing B x) w) =
      LocalizedModule.map x.asIdeal.primeCompl (Pi1 d hπ hπM) (stalkQuot x M (d.line M) w) := by
  refine stalkQuot_naturality x (d.line M) (d.line M') (smulInto π hπM)
      ((smulInto π hπM).baseChange B)
    (fun v => ?_) _ ((smulInto π hπM).baseChange (locRing B x)) (fun v => ?_) w
  · rw [LinearMap.baseChange_tmul]
  · rw [LinearMap.baseChange_tmul]

omit [IsFractionRing 𝒪 K] in
/-- The kernel of the stalk map of `loc₀` is the base-changed line. -/
theorem ker_loc₀ (hle : M'.1 ≤ M.1) (x : PrimeSpectrum B) :
    LinearMap.ker (loc₀ d hle x).2 = (d.map π (toLocRing B x)).line (loc₀ d hle x).1 := by
  by_cases hx : x ∈ S0 d (M := M) hle
  · rw [loc₀_eq_of_mem d hle hx]; exact ker_stalkQuot x M' (d.line M')
  · rw [loc₀_eq_of_not_mem d hle hx]
    change LinearMap.ker ((Pi0inv d hle x hx).toLinearMap ∘ₗ stalkQuot x M (d.line M)) = _
    rw [LinearMap.ker_comp, LinearEquiv.ker, Submodule.comap_bot]
    exact ker_stalkQuot x M (d.line M)

/-- Multiplication by `π` as an isomorphism `π⁻¹ M' ≃ M'`. -/
noncomputable def smulEquiv (hπ : Irreducible π) (M' : FullLattice 𝒪 K) : ↥(Mpi (K := K) hπ M').1
    ≃ₗ[𝒪] ↥M'.1 :=
  LinearEquiv.ofBijective (smulInto π (smul_mem_of_mem_Mpi (K := K) hπ M'))
    ⟨by
      intro v w h
      apply Subtype.ext
      have := congrArg Subtype.val h
      rw [coe_smulInto_apply, coe_smulInto_apply] at this
      exact smul_right_injective _ (hπK_of_irreducible (K := K) hπ) this,
     by
      intro w
      refine ⟨⟨(((piUnit (K := K) hπ)⁻¹ : Kˣ) : K) • (w : Fin 2 → K),
          mem_latticeMap_scalarGL.mpr ⟨w, w.2, rfl⟩⟩, ?_⟩
      apply Subtype.ext
      rw [coe_smulInto_apply, smul_smul, Units.val_inv_eq_inv_val,
        show algebraMap 𝒪 K π = ((piUnit (K := K) hπ : Kˣ) : K) from rfl,
            mul_inv_cancel₀ (piUnit (K := K) hπ).ne_zero,
        one_smul]⟩

/-- `sPi` is the base change of `smulEquiv`. -/
theorem sPi_eq (hπ : Irreducible π) (M' : FullLattice 𝒪 K) (x : PrimeSpectrum B) :
    sPi (B := B) hπ M' x = ((smulEquiv (K := K) hπ M').baseChange 𝒪 (locRing B x) _ _).toLinearMap
        := by
  refine TensorProduct.AlgebraTensorModule.ext fun b v => ?_
  rw [sPi, LinearMap.baseChange_tmul, LinearEquiv.coe_coe, LinearEquiv.baseChange_tmul]
  rfl

/-- `sPi` is injective. -/
theorem ker_sPi (hπ : Irreducible π) (M' : FullLattice 𝒪 K) (x : PrimeSpectrum B) :
    LinearMap.ker (sPi (B := B) hπ M' x) = ⊥ := by
  rw [sPi_eq, LinearEquiv.ker]

/-- Multiplication by `π` maps the line at `π⁻¹ M'` onto the line at `M'`. -/
theorem map_smulInto_line_Mpi (hπ : Irreducible π) (M' : FullLattice 𝒪 K) :
    (d.line (Mpi (K := K) hπ M')).map ((smulInto π (smul_mem_of_mem_Mpi (K := K) hπ M')).baseChange
        B) = d.line M' := by
  have hfac := smulInto_baseChange_eq (M := Mpi (K := K) hπ M') (M' := M') (B := B) hπ
      (smul_mem_of_mem_Mpi (K := K) hπ M')
  have hle1 : (FullLattice.act (scalarGL (piUnit (K := K) hπ)) (Mpi (K := K) hπ M')).1 ≤ M'.1 :=
    act_piUnit_le hπ (smul_mem_of_mem_Mpi (K := K) hπ M')
  have hle2 : M'.1 ≤ (FullLattice.act (scalarGL (piUnit (K := K) hπ)) (Mpi (K := K) hπ M')).1 := by
    intro v hv
    refine mem_latticeMap_scalarGL.mpr ⟨(((piUnit (K := K) hπ)⁻¹ : Kˣ) : K) • v,
      mem_latticeMap_scalarGL.mpr ⟨v, hv, rfl⟩, ?_⟩
    rw [smul_smul, Units.val_inv_eq_inv_val, mul_inv_cancel₀ (piUnit (K := K) hπ).ne_zero, one_smul]
  apply le_antisymm
  · rw [hfac, Submodule.map_comp, ← d.homothety (piUnit (K := K) hπ) (Mpi (K := K) hπ M')]
    exact d.mono hle1
  · have hround : (inclBaseChange B hle1) ∘ₗ (inclBaseChange B hle2) = LinearMap.id := by
      refine TensorProduct.AlgebraTensorModule.ext fun b v => ?_
      rw [LinearMap.comp_apply, inclBaseChange, inclBaseChange, LinearMap.baseChange_tmul,
          LinearMap.baseChange_tmul,
        LinearMap.id_apply]
      rfl
    calc d.line M' = ((d.line M').map (inclBaseChange B hle2)).map (inclBaseChange B hle1) := by
          rw [← Submodule.map_comp, hround, Submodule.map_id]
      _ ≤ (d.line (FullLattice.act (scalarGL (piUnit (K := K) hπ)) (Mpi (K := K) hπ M'))).map
          (inclBaseChange B hle1) :=
          Submodule.map_mono (d.mono hle2)
      _ = _ := by rw [d.homothety (piUnit (K := K) hπ) (Mpi (K := K) hπ M'), ← Submodule.map_comp,
          ← hfac]

omit [IsFractionRing 𝒪 K] in
/-- Base change of lines commutes with mapping along a base-changed lattice map. -/
theorem lineBaseChange_map_baseChange {B' : Type} [CommRing B'] [Algebra 𝒪 B'] (f : B →ₐ[𝒪] B')
    {L L' : FullLattice 𝒪 K} (ψ : ↥L.1 →ₗ[𝒪] ↥L'.1) (N : Submodule B (latticeBaseChange 𝒪 K B L)) :
    lineBaseChange f L' (N.map (ψ.baseChange B)) = (lineBaseChange f L N).map (ψ.baseChange B') :=
        by
  rw [lineBaseChange, lineBaseChange, Submodule.map_span, Submodule.map_coe, ← Set.image_comp,
      ← Set.image_comp]
  have key : ∀ n : latticeBaseChange 𝒪 K B L,
      (LinearMap.rTensor (↥L'.1) f.toLinearMap) ((ψ.baseChange B) n) =
        (ψ.baseChange B') ((LinearMap.rTensor (↥L.1) f.toLinearMap) n) := by
    intro n
    induction n using TensorProduct.inductionOn with
    | add n₁ n₂ h₁ h₂ => simp only [map_add, h₁, h₂]
    | tmul b v => rw [LinearMap.baseChange_tmul, LinearMap.rTensor_tmul, LinearMap.rTensor_tmul,
        LinearMap.baseChange_tmul]
  congr 1
  exact Set.image_congr fun n _ => by simp only [Function.comp_apply, key]

/-- The kernel of the stalk map of `loc₁` is the base-changed line. -/
theorem ker_loc₁ (hπ : Irreducible π) (hπM : ∀ v ∈ M.1, algebraMap 𝒪 K π • v ∈ M'.1)
    (x : PrimeSpectrum B) :
    LinearMap.ker (loc₁ d hπ hπM x).2 = (d.map π (toLocRing B x)).line (loc₁ d hπ hπM x).1 := by
  by_cases hx : x ∈ S1 d hπ hπM
  · rw [loc₁_eq_of_mem d hπ hπM hx]; exact ker_stalkQuot x M (d.line M)
  · rw [loc₁_eq_of_not_mem d hπ hπM hx]
    change LinearMap.ker ((Pi1inv d hπ hπM x hx).toLinearMap ∘ₗ stalkQuot x M' (d.line M') ∘ₗ sPi hπ
        M' x) =
      lineBaseChange (toLocRing B x) (Mpi (K := K) hπ M') (d.line (Mpi (K := K) hπ M'))
    rw [LinearMap.ker_comp, LinearEquiv.ker, Submodule.comap_bot, LinearMap.ker_comp, ker_stalkQuot,
      ← map_smulInto_line_Mpi d hπ M', lineBaseChange_map_baseChange, ← sPi, Submodule.comap_map_eq,
          ker_sPi, sup_bot_eq]

/-- `M ⊆ π⁻¹ M'`. -/
theorem le_Mpi (hπ : Irreducible π) (hπM : ∀ v ∈ M.1, algebraMap 𝒪 K π • v ∈ M'.1) :
    M.1 ≤ (Mpi (K := K) hπ M').1 := by
  intro v hv
  refine mem_latticeMap_scalarGL.mpr ⟨algebraMap 𝒪 K π • v, hπM v hv, ?_⟩
  rw [smul_smul, Units.val_inv_eq_inv_val, show algebraMap 𝒪 K π = ((piUnit (K := K) hπ : Kˣ) : K)
      from rfl,
    inv_mul_cancel₀ (piUnit (K := K) hπ).ne_zero, one_smul]

/-- The lattice of `loc₀` is contained in that of `loc₁`. -/
theorem loc_le (hπ : Irreducible π) (hle : M'.1 ≤ M.1) (hπM : ∀ v ∈ M.1,
    algebraMap 𝒪 K π • v ∈ M'.1)
    (x : PrimeSpectrum B) : (loc₀ d hle x).1.1 ≤ (loc₁ d hπ hπM x).1.1 := by
  by_cases h0 : x ∈ S0 d (M := M) hle <;> by_cases h1 : x ∈ S1 d hπ hπM
  · rw [loc₀_fst_of_mem d hle h0, loc₁_fst_of_mem d hπ hπM h1]; exact hle
  · rw [loc₀_fst_of_mem d hle h0, loc₁_fst_of_not_mem d hπ hπM h1]; exact hle.trans (le_Mpi hπ hπM)
  · rw [loc₀_fst_of_not_mem d hle h0, loc₁_fst_of_mem d hπ hπM h1]
  · rw [loc₀_fst_of_not_mem d hle h0, loc₁_fst_of_not_mem d hπ hπM h1]; exact le_Mpi hπ hπM

/-- `π` times the lattice of `loc₁` is contained in that of `loc₀`. -/
theorem loc_smul_le (hπ : Irreducible π) (hle : M'.1 ≤ M.1)
    (hπM : ∀ v ∈ M.1, algebraMap 𝒪 K π • v ∈ M'.1)
    (x : PrimeSpectrum B) : ∀ v ∈ (loc₁ d hπ hπM x).1.1,
        algebraMap 𝒪 K π • v ∈ (loc₀ d hle x).1.1 := by
  by_cases h0 : x ∈ S0 d (M := M) hle <;> by_cases h1 : x ∈ S1 d hπ hπM
  · rw [loc₀_fst_of_mem d hle h0, loc₁_fst_of_mem d hπ hπM h1]; exact hπM
  · rw [loc₀_fst_of_mem d hle h0, loc₁_fst_of_not_mem d hπ hπM h1]; exact smul_mem_of_mem_Mpi hπ M'
  · rw [loc₀_fst_of_not_mem d hle h0, loc₁_fst_of_mem d hπ hπM h1]; exact fun v hv => hle (hπM v hv)
  · rw [loc₀_fst_of_not_mem d hle h0, loc₁_fst_of_not_mem d hπ hπM h1]
    exact fun v hv => hle (smul_mem_of_mem_Mpi hπ M' v hv)

/-- `sPi` after the inclusion `M' ⊆ π⁻¹ M'` is multiplication by `π`. -/
theorem sPi_incl (hπ : Irreducible π) (x : PrimeSpectrum B) (h : M'.1 ≤ (Mpi (K := K) hπ M').1)
    (w : latticeBaseChange 𝒪 K (locRing B x) M') :
    sPi hπ M' x (inclBaseChange (locRing B x) h w) = algebraMap 𝒪 B π • w := by
  induction w using TensorProduct.inductionOn with
  | add y z hy hz => simp only [map_add, smul_add, hy, hz]
  | tmul c v =>
    rw [inclBaseChange, LinearMap.baseChange_tmul, sPi, LinearMap.baseChange_tmul, algebraMap_smul,
      TensorProduct.smul_tmul', TensorProduct.smul_tmul]
    congr 1
    apply Subtype.ext
    rw [coe_smulInto_apply, Submodule.coe_inclusion, Submodule.coe_smul, algebraMap_smul]

omit [IsFractionRing 𝒪 K] in
/-- Multiplication by `π` from a lattice to itself, after base change, is the scalar `π`. -/
theorem smulInto_self (x : PrimeSpectrum B) (h : ∀ v ∈ M.1, algebraMap 𝒪 K π • v ∈ M.1)
    (w : latticeBaseChange 𝒪 K (locRing B x) M) :
    (smulInto π h).baseChange (locRing B x) w = algebraMap 𝒪 B π • w := by
  induction w using TensorProduct.inductionOn with
  | add y z hy hz => simp only [map_add, smul_add, hy, hz]
  | tmul c v =>
    rw [LinearMap.baseChange_tmul, algebraMap_smul, TensorProduct.smul_tmul',
        TensorProduct.smul_tmul]
    congr 1
    apply Subtype.ext
    rw [coe_smulInto_apply, Submodule.coe_smul, algebraMap_smul]

/-- `sPi` after the inclusion `M ⊆ π⁻¹ M'` is multiplication by `π`. -/
theorem sPi_incl' (hπ : Irreducible π) (hπM : ∀ v ∈ M.1, algebraMap 𝒪 K π • v ∈ M'.1)
    (x : PrimeSpectrum B)
    (h : M.1 ≤ (Mpi (K := K) hπ M').1) (w : latticeBaseChange 𝒪 K (locRing B x) M) :
    sPi hπ M' x (inclBaseChange (locRing B x) h w) = (smulInto π hπM).baseChange (locRing B x) w :=
        by
  induction w using TensorProduct.inductionOn with
  | add y z hy hz => simp only [map_add, hy, hz]
  | tmul c v =>
    rw [inclBaseChange, LinearMap.baseChange_tmul, sPi, LinearMap.baseChange_tmul,
        LinearMap.baseChange_tmul]
    congr 1

/-- Multiplication by `π` from `π⁻¹ M'` to `M` factors through `sPi`. -/
theorem incl_sPi (hπ : Irreducible π) (hle : M'.1 ≤ M.1) (x : PrimeSpectrum B)
    (h : ∀ v ∈ (Mpi (K := K) hπ M').1, algebraMap 𝒪 K π • v ∈ M.1)
        (w : latticeBaseChange 𝒪 K (locRing B x) (Mpi (K := K) hπ M')) :
    (smulInto π h).baseChange (locRing B x) w = inclBaseChange (locRing B x) hle (sPi hπ M' x w) :=
        by
  induction w using TensorProduct.inductionOn with
  | add y z hy hz => simp only [map_add, hy, hz]
  | tmul c v =>
    rw [inclBaseChange, sPi, LinearMap.baseChange_tmul, LinearMap.baseChange_tmul,
        LinearMap.baseChange_tmul]
    congr 1

omit [IsFractionRing 𝒪 K] in
/-- The base change of the identity inclusion is the identity. -/
theorem incl_self (x : PrimeSpectrum B) (h : M.1 ≤ M.1) (w : latticeBaseChange 𝒪 K (locRing B x) M)
    :
    inclBaseChange (locRing B x) h w = w := by
  induction w using TensorProduct.inductionOn with
  | add y z hy hz => simp only [map_add, hy, hz]
  | tmul c v => rw [inclBaseChange, LinearMap.baseChange_tmul]; rfl

/-- The stalks of `Pi1 ∘ Pi0` are multiplication by `π`. -/
theorem map_Pi1_map_Pi0 (hπ : Irreducible π) (hle : M'.1 ≤ M.1)
    (hπM : ∀ v ∈ M.1, algebraMap 𝒪 K π • v ∈ M'.1)
    (x : PrimeSpectrum B) (t : stalk B x (T0 d M')) :
    LocalizedModule.map x.asIdeal.primeCompl (Pi1 d hπ hπM)
        (LocalizedModule.map x.asIdeal.primeCompl (Pi0 d hle) t) =
      algebraMap 𝒪 B π • t := by
  induction t using LocalizedModule.induction_on with
  | h m s => rw [LocalizedModule.map_mk, LocalizedModule.map_mk, Pi1_Pi0 d hπ hle hπM,
      LocalizedModule.smul'_mk]

/-- The stalks of `Pi0 ∘ Pi1` are multiplication by `π`. -/
theorem map_Pi0_map_Pi1 (hπ : Irreducible π) (hle : M'.1 ≤ M.1)
    (hπM : ∀ v ∈ M.1, algebraMap 𝒪 K π • v ∈ M'.1)
    (x : PrimeSpectrum B) (t : stalk B x (T1 d M)) :
    LocalizedModule.map x.asIdeal.primeCompl (Pi0 d hle)
        (LocalizedModule.map x.asIdeal.primeCompl (Pi1 d hπ hπM) t) =
      algebraMap 𝒪 B π • t := by
  induction t using LocalizedModule.induction_on with
  | h m s => rw [LocalizedModule.map_mk, LocalizedModule.map_mk, Pi0_Pi1 d hπ hle hπM,
      LocalizedModule.smul'_mk]

/-- Compatibility of the stalk maps of `loc₀` and `loc₁` with the inclusion and `Pi0`. -/
theorem u₁_incl_loc (hπ : Irreducible π) (hle : M'.1 ≤ M.1)
    (hπM : ∀ v ∈ M.1, algebraMap 𝒪 K π • v ∈ M'.1)
    (x : PrimeSpectrum B) (hl : (loc₀ d hle x).1.1 ≤ (loc₁ d hπ hπM x).1.1)
    (w : latticeBaseChange 𝒪 K (locRing B x) (loc₀ d hle x).1) :
    (loc₁ d hπ hπM x).2 (inclBaseChange (locRing B x) (M' := (loc₀ d hle x).1)
        (M := (loc₁ d hπ hπM x).1) hl w) =
      LocalizedModule.map x.asIdeal.primeCompl (Pi0 d hle) ((loc₀ d hle x).2 w) := by
  revert w
  by_cases h0 : x ∈ S0 d (M := M) hle <;> by_cases h1 : x ∈ S1 d hπ hπM
  · have e0 := loc₀_eq_of_mem d hle h0; have e1 := loc₁_eq_of_mem d hπ hπM h1
    generalize loc₀ d hle x = p₀ at e0 hl ⊢; generalize loc₁ d hπ hπM x = p₁ at e1 hl ⊢
    subst e0 e1
    dsimp only at hl
    intro w; exact stalkQuot_incl d hle x w
  · have e0 := loc₀_eq_of_mem d hle h0; have e1 := loc₁_eq_of_not_mem d hπ hπM h1
    generalize loc₀ d hle x = p₀ at e0 hl ⊢; generalize loc₁ d hπ hπM x = p₁ at e1 hl ⊢
    subst e0 e1
    dsimp only at hl
    intro w
    change (Pi1inv d hπ hπM x h1) (stalkQuot x M' (d.line M')
        (sPi hπ M' x (inclBaseChange (locRing B x) hl w))) = _
    rw [sPi_incl, ← algebraMap_smul (locRing B x), map_smul, algebraMap_smul,
        ← map_Pi1_map_Pi0 d hπ hle hπM x,
      Pi1inv_map_Pi1]
  · have e0 := loc₀_eq_of_not_mem d hle h0; have e1 := loc₁_eq_of_mem d hπ hπM h1
    generalize loc₀ d hle x = p₀ at e0 hl ⊢; generalize loc₁ d hπ hπM x = p₁ at e1 hl ⊢
    subst e0 e1
    dsimp only at hl
    intro w
    change stalkQuot x M (d.line M) (inclBaseChange (locRing B x) hl w) =
      LocalizedModule.map x.asIdeal.primeCompl (Pi0 d hle)
          ((Pi0inv d hle x h0) (stalkQuot x M (d.line M) w))
    rw [incl_self, map_Pi0_Pi0inv]
  · have e0 := loc₀_eq_of_not_mem d hle h0; have e1 := loc₁_eq_of_not_mem d hπ hπM h1
    generalize loc₀ d hle x = p₀ at e0 hl ⊢; generalize loc₁ d hπ hπM x = p₁ at e1 hl ⊢
    subst e0 e1
    dsimp only at hl
    intro w
    change (Pi1inv d hπ hπM x h1) (stalkQuot x M' (d.line M')
        (sPi hπ M' x (inclBaseChange (locRing B x) hl w))) =
      LocalizedModule.map x.asIdeal.primeCompl (Pi0 d hle)
          ((Pi0inv d hle x h0) (stalkQuot x M (d.line M) w))
    rw [sPi_incl' hπ hπM, stalkQuot_smulInto d hπ hπM, Pi1inv_map_Pi1, map_Pi0_Pi0inv]

/-- Compatibility of the stalk maps of `loc₀` and `loc₁` with multiplication by `π` and `Pi1`. -/
theorem u₀_smul_loc (hπ : Irreducible π) (hle : M'.1 ≤ M.1)
    (hπM : ∀ v ∈ M.1, algebraMap 𝒪 K π • v ∈ M'.1)
    (x : PrimeSpectrum B) (hl : ∀ v ∈ (loc₁ d hπ hπM x).1.1,
        algebraMap 𝒪 K π • v ∈ (loc₀ d hle x).1.1)
    (w : latticeBaseChange 𝒪 K (locRing B x) (loc₁ d hπ hπM x).1) :
    (loc₀ d hle x).2 (((smulInto π hl).baseChange (locRing B x) :
        latticeBaseChange 𝒪 K (locRing B x) (loc₁ d hπ hπM x).1 →ₗ[locRing B x]
          latticeBaseChange 𝒪 K (locRing B x) (loc₀ d hle x).1) w) =
      LocalizedModule.map x.asIdeal.primeCompl (Pi1 d hπ hπM) ((loc₁ d hπ hπM x).2 w) := by
  revert w
  by_cases h0 : x ∈ S0 d (M := M) hle <;> by_cases h1 : x ∈ S1 d hπ hπM
  · have e0 := loc₀_eq_of_mem d hle h0; have e1 := loc₁_eq_of_mem d hπ hπM h1
    generalize loc₀ d hle x = p₀ at e0 hl ⊢; generalize loc₁ d hπ hπM x = p₁ at e1 hl ⊢
    subst e0 e1
    dsimp only at hl
    intro w; exact stalkQuot_smulInto d hπ hπM x w
  · have e0 := loc₀_eq_of_mem d hle h0; have e1 := loc₁_eq_of_not_mem d hπ hπM h1
    generalize loc₀ d hle x = p₀ at e0 hl ⊢; generalize loc₁ d hπ hπM x = p₁ at e1 hl ⊢
    subst e0 e1
    dsimp only at hl
    intro w
    change stalkQuot x M' (d.line M') ((smulInto π hl).baseChange (locRing B x) w) =
      LocalizedModule.map x.asIdeal.primeCompl (Pi1 d hπ hπM)
        ((Pi1inv d hπ hπM x h1) (stalkQuot x M' (d.line M') (sPi hπ M' x w)))
    rw [map_Pi1_Pi1inv]; rfl
  · have e0 := loc₀_eq_of_not_mem d hle h0; have e1 := loc₁_eq_of_mem d hπ hπM h1
    generalize loc₀ d hle x = p₀ at e0 hl ⊢; generalize loc₁ d hπ hπM x = p₁ at e1 hl ⊢
    subst e0 e1
    dsimp only at hl
    intro w
    change (Pi0inv d hle x h0) (stalkQuot x M (d.line M)
        ((smulInto π hl).baseChange (locRing B x) w)) =
      LocalizedModule.map x.asIdeal.primeCompl (Pi1 d hπ hπM) (stalkQuot x M (d.line M) w)
    rw [smulInto_self, ← algebraMap_smul (locRing B x), map_smul, algebraMap_smul,
        ← map_Pi0_map_Pi1 d hπ hle hπM x,
      Pi0inv_map_Pi0]
  · have e0 := loc₀_eq_of_not_mem d hle h0; have e1 := loc₁_eq_of_not_mem d hπ hπM h1
    generalize loc₀ d hle x = p₀ at e0 hl ⊢; generalize loc₁ d hπ hπM x = p₁ at e1 hl ⊢
    subst e0 e1
    dsimp only at hl
    intro w
    change (Pi0inv d hle x h0) (stalkQuot x M (d.line M)
        ((smulInto π hl).baseChange (locRing B x) w)) =
      LocalizedModule.map x.asIdeal.primeCompl (Pi1 d hπ hπM)
        ((Pi1inv d hπ hπM x h1) (stalkQuot x M' (d.line M') (sPi hπ M' x w)))
    have key := incl_sPi (B := B) hπ hle x hl w
    rw [key, stalkQuot_incl d hle, Pi0inv_map_Pi0, map_Pi1_Pi1inv]

end Local

end CerednikDrinfeld.FormalOmega.QuadrupleLocal

end
