/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua, Avocado
-/

module

public import MathlibExt.Algebra.Homology.KoszulComplexResidueReduction
public import MathlibExt.LinearAlgebra.ExteriorPower.DeletionBasis
public import MathlibExt.RingTheory.Ideal.AssociatedGraded.ModuleFirstOrder
public import MathlibExt.RingTheory.LocalRing.CotangentBasisFamily

/-!
# First-order Koszul differentials for cotangent-basis lifts

For a noetherian local ring R with residue field κ and cotangent space V=m/m², choose the
finite family lifting a κ-basis of V. The Koszul differential has image in m times the next
term. Its first-order linearization maps the residue of Λ^{n+1}(R^e) to the residue of
Λ^n(R^e) tensored over κ with V.

Under the residue exterior-power identifications, this map is exterior deletion followed by
the cotangent-basis equivalence on the second factor. It is injective in every degree, with
the ordered deletion signs retained.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open IsLocalRing
open scoped TensorProduct

universe u

namespace KoszulComplex

private theorem fintype_sum_congr
    {N : Type*} [AddCommMonoid N]
    {ι : Type*} [Fintype ι] (f g : ι → N)
    (h : ∀ i, f i = g i) :
    ∑ i, f i = ∑ i, g i := by
  classical
  exact Finset.sum_congr rfl fun i _ => h i

section

variable (R : Type u) [CommRing R] [IsLocalRing R]
  [IsNoetherianRing R]

local notation "k" => ResidueField R
local notation "m" => maximalIdeal R
local notation "V" => CotangentSpace R
local notation "e" => Module.finrank k V
local notation "M₀" => Fin e → R
local notation "Mₖ" => Fin e → k
local notation:max "K[" n "]" => (⋀[R]^n M₀)
local notation:max "Kₖ[" n "]" => (⋀[k]^n Mₖ)

-- Reconcile the residue-field spelling with the raw quotient spelling only
-- inside this module. These instances must not be exported.
/-- The residue scalar structure on the quotient presentation.

Regard R/m as a module over the residue field κ through its quotient-ring presentation. -/
local instance e1ResidueQuotientModule : Module k (R ⧸ m) :=
  inferInstanceAs (Module (R ⧸ m) (R ⧸ m))

/-- The scalar tower on the residue quotient presentation.

The R- and κ-actions on R/m form the canonical scalar tower. -/
local instance e1ResidueQuotientTower : IsScalarTower R k (R ⧸ m) :=
  inferInstanceAs (IsScalarTower R (R ⧸ m) (R ⧸ m))

/-- The commuting scalar actions on the residue quotient.

The R-action and residue-field action on R/m commute. -/
local instance e1ResidueQuotientSmulComm : SMulCommClass R k (R ⧸ m) :=
  inferInstanceAs (SMulCommClass R (R ⧸ m) (R ⧸ m))

/-- The residue-field module of a Koszul term quotient.

The quotient of K_n by mK_n carries its canonical κ-module structure. -/
local instance e1TermQuotientModule (n : ℕ) :
    Module k (K[n] ⧸ (m • (⊤ : Submodule R K[n]))) :=
  inferInstanceAs
    (Module (R ⧸ m) (K[n] ⧸ (m • (⊤ : Submodule R K[n]))))

/-- The scalar tower on a reduced Koszul term.

The R- and κ-actions on K_n/mK_n form the canonical scalar tower. -/
local instance e1TermQuotientTower (n : ℕ) :
    IsScalarTower R k
      (K[n] ⧸ (m • (⊤ : Submodule R K[n]))) :=
  inferInstanceAs
    (IsScalarTower R (R ⧸ m)
      (K[n] ⧸ (m • (⊤ : Submodule R K[n]))))

private theorem cotangentFamilyDifferential_range (n : ℕ) :
    LinearMap.range
        (differential R M₀ (familyFunctional R (cotangentFamily R)) n) ≤
      m • (⊤ : Submodule R K[n]) :=
  differential_range_le_ideal_smul R M₀ m
    (familyFunctional R (cotangentFamily R))
    (familyIdeal_eq_maximalIdeal R (cotangentFamily R)
      (cotangentFamily_span R)).le n

/-- The tensor-valued first-order cotangent-family differential.

Linearize d : K_{n+1} → K_n at m to obtain K_{n+1}/mK_{n+1} → (K_n/mK_n) ⊗_κ V. -/
@[no_expose]
noncomputable def cotangentFamilyLinearizedDifferential (n : ℕ) :
    (K[n + 1] ⧸ (m • (⊤ : Submodule R K[n + 1]))) →ₗ[k]
      ((K[n] ⧸ (m • (⊤ : Submodule R K[n]))) ⊗[k] V) :=
  (differential R M₀
    (familyFunctional R (cotangentFamily R)) n).linearizationAtIdeal
      m (cotangentFamilyDifferential_range R n)

/-- Agreement with linearization using the differential image containment.

The cotangent-family map equals the ideal linearization of the differential using any stated
containment of its range in mK_n. -/
theorem cotangentFamilyLinearizedDifferential_eq_linearizationAtIdeal
    (n : ℕ)
    (h : LinearMap.range
        (differential R M₀
          (familyFunctional R (cotangentFamily R)) n) ≤
      m • (⊤ : Submodule R K[n])) :
    cotangentFamilyLinearizedDifferential R n =
      (differential R M₀
        (familyFunctional R (cotangentFamily R)) n).linearizationAtIdeal
          m h := by
  rw [cotangentFamilyLinearizedDifferential]

private def cotangentFamilyCoefficient (b : M₀) : m :=
  ⟨familyFunctional R (cotangentFamily R) b,
    (familyIdeal_eq_maximalIdeal R (cotangentFamily R)
      (cotangentFamily_span R)).le (LinearMap.mem_range_self _ b)⟩

private theorem cotangentFamilyEquiv_residue_apply (b : M₀) :
    cotangentFamilyEquiv R (fun i => residue R (b i)) =
      (m).toCotangent (cotangentFamilyCoefficient R b) := by
  rw [← Finset.univ_sum_single (fun i => residue R (b i)), map_sum]
  calc
    (∑ i, cotangentFamilyEquiv R (Pi.single i (residue R (b i)))) =
        ∑ i, residue R (b i) •
          cotangentFamilyEquiv R (Pi.single i 1) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [show Pi.single i (residue R (b i)) =
          residue R (b i) • Pi.single i 1 by
        ext j
        simp [Pi.single_apply], map_smul]
    _ = ∑ i, residue R (b i) •
          (m).toCotangent (cotangentGenerator R i) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [cotangentFamilyEquiv_single]
    _ = ∑ i, (m).toCotangent (b i • cotangentGenerator R i) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [(m).toCotangent.map_smul]
      change residue R (b i) •
          (m).toCotangent (cotangentGenerator R i) =
        algebraMap R k (b i) •
          (m).toCotangent (cotangentGenerator R i)
      rw [ResidueField.algebraMap_eq]
    _ = (m).toCotangent (∑ i, b i • cotangentGenerator R i) := by
      rw [map_sum]
    _ = (m).toCotangent (cotangentFamilyCoefficient R b) := by
      congr 1
      apply Subtype.ext
      simp [cotangentFamilyCoefficient, familyFunctional,
        Fintype.linearCombination_apply, cotangentFamily]

omit [IsNoetherianRing R] in
private theorem rawTensor_eq_residueTensor
    (n : ℕ) (x : K[n] ⧸ (m • (⊤ : Submodule R K[n]))) (v : V) :
    (x ⊗ₜ[R ⧸ m] v) = (x ⊗ₜ[k] v) :=
  rfl

omit [IsNoetherianRing R] in
private theorem rawSmul_eq_residueSmul
    (r : R) (n : ℕ)
    (x : (K[n] ⧸ (m • (⊤ : Submodule R K[n]))) ⊗[k] V) :
    r • x = residue R r • x := by
  change algebraMap R k r • x = residue R r • x
  rw [ResidueField.algebraMap_eq]

private theorem cotangentFamilyLinearizedDifferentialRaw_mk_ιMulti
    (n : ℕ) (b : Fin (n + 1) → M₀) :
    (differential R M₀
      (familyFunctional R (cotangentFamily R)) n).linearizationAtIdeal
        m (cotangentFamilyDifferential_range R n)
        (Submodule.Quotient.mk
          (exteriorPower.ιMulti R (n + 1) b)) =
      ∑ i : Fin (n + 1), (-1 : R) ^ (i : ℕ) •
        (Submodule.Quotient.mk
            (exteriorPower.ιMulti R n (b ∘ i.succAbove)) ⊗ₜ[R ⧸ m]
          (m).toCotangent (cotangentFamilyCoefficient R (b i))) := by
  apply (Ideal.firstOrderMul_bijective_of_flat m K[n]).injective
  have hleft := LinearMap.firstOrderMul_linearizationAtIdeal_mk
    m (differential R M₀
      (familyFunctional R (cotangentFamily R)) n)
      (cotangentFamilyDifferential_range R n)
      (exteriorPower.ιMulti R (n + 1) b)
  let IM : Submodule R K[n] := m • ⊤
  let q : IM →ₗ[R] Ideal.FirstOrderModuleLayer m K[n] :=
    Submodule.mkQ _
  calc
    Ideal.firstOrderMul m K[n]
        ((differential R M₀
          (familyFunctional R (cotangentFamily R)) n).linearizationAtIdeal
            m (cotangentFamilyDifferential_range R n)
              (Submodule.Quotient.mk
                (exteriorPower.ιMulti R (n + 1) b))) =
      Submodule.Quotient.mk
        (⟨differential R M₀
            (familyFunctional R (cotangentFamily R)) n
              (exteriorPower.ιMulti R (n + 1) b),
          cotangentFamilyDifferential_range R n
            (LinearMap.mem_range_self _
              (exteriorPower.ιMulti R (n + 1) b))⟩ :
            ↥IM) := hleft
    _ = Ideal.firstOrderMul m K[n]
        (∑ i : Fin (n + 1), (-1 : R) ^ (i : ℕ) •
          (Submodule.Quotient.mk
              (exteriorPower.ιMulti R n (b ∘ i.succAbove)) ⊗ₜ[R ⧸ m]
            (m).toCotangent (cotangentFamilyCoefficient R (b i)))) := by
      rw [map_sum]
      simp only [LinearMap.map_smul_of_tower,
        Ideal.firstOrderMul_mk_tmul_toCotangent]
      let y : Fin (n + 1) → ↥IM :=
        fun i =>
          ⟨(cotangentFamilyCoefficient R (b i) : R) •
              exteriorPower.ιMulti R n (b ∘ i.succAbove),
            Submodule.smul_mem_smul
              (cotangentFamilyCoefficient R (b i)).property
              Submodule.mem_top⟩
      let rep : IM :=
        ⟨differential R M₀
            (familyFunctional R (cotangentFamily R)) n
              (exteriorPower.ιMulti R (n + 1) b),
          cotangentFamilyDifferential_range R n
            (LinearMap.mem_range_self _
              (exteriorPower.ιMulti R (n + 1) b))⟩
      calc
        Submodule.Quotient.mk rep = q rep := rfl
        _ = q (∑ i : Fin (n + 1),
            ((-1 : R) ^ (i : ℕ)) • y i) := by
          apply congrArg q
          apply Subtype.ext
          simpa [y, cotangentFamilyCoefficient] using
            (differential_apply_ιMulti R M₀
              (familyFunctional R (cotangentFamily R)) n b)
        _ = ∑ i : Fin (n + 1), q
            (((-1 : R) ^ (i : ℕ)) • y i) := by
          exact map_sum q
            (fun i : Fin (n + 1) => ((-1 : R) ^ (i : ℕ)) • y i)
            Finset.univ
        _ = ∑ i : Fin (n + 1), (-1 : R) ^ (i : ℕ) •
            q (y i) := by
          exact fintype_sum_congr _ _ fun i => q.map_smul _ _

private theorem cotangentFamilyLinearizedDifferential_mk_ιMulti
    (n : ℕ) (b : Fin (n + 1) → M₀) :
    cotangentFamilyLinearizedDifferential R n
        (Submodule.Quotient.mk
          (exteriorPower.ιMulti R (n + 1) b)) =
      ∑ i : Fin (n + 1), (-1 : k) ^ (i : ℕ) •
        (Submodule.Quotient.mk
            (exteriorPower.ιMulti R n (b ∘ i.succAbove)) ⊗ₜ[k]
          (m).toCotangent (cotangentFamilyCoefficient R (b i))) := by
  rw [cotangentFamilyLinearizedDifferential]
  calc
    _ = ∑ i : Fin (n + 1), (-1 : R) ^ (i : ℕ) •
        (Submodule.Quotient.mk
            (exteriorPower.ιMulti R n (b ∘ i.succAbove)) ⊗ₜ[R ⧸ m]
          (m).toCotangent (cotangentFamilyCoefficient R (b i))) :=
      cotangentFamilyLinearizedDifferentialRaw_mk_ιMulti R n b
    _ = _ := by
      have hterm (i : Fin (n + 1)) :
          (-1 : R) ^ (i : ℕ) •
              ((Submodule.Quotient.mk
                  (exteriorPower.ιMulti R n (b ∘ i.succAbove)) :
                    K[n] ⧸ (m • (⊤ : Submodule R K[n]))) ⊗ₜ[R ⧸ m]
                (m).toCotangent
                  (cotangentFamilyCoefficient R (b i))) =
            (-1 : k) ^ (i : ℕ) •
              ((Submodule.Quotient.mk
                  (exteriorPower.ιMulti R n (b ∘ i.succAbove)) :
                    K[n] ⧸ (m • (⊤ : Submodule R K[n]))) ⊗ₜ[k]
                (m).toCotangent
                  (cotangentFamilyCoefficient R (b i))) := by
        rw [rawTensor_eq_residueTensor]
        rw [rawSmul_eq_residueSmul]
        congr 1
      exact fintype_sum_congr _ _ hterm

/-- The exterior-deletion coordinate formula for the linearized differential.

After the residue exterior identifications, the first-order map is deletion Λ^{n+1}(κ^e) →
Λ^n(κ^e) ⊗ κ^e followed by the cotangent-basis equivalence on its second factor. -/
theorem cotangentFamily_linearization (n : ℕ) :
    (TensorProduct.map
      (familyResidueComponentEquiv R n).toLinearMap
      (LinearMap.id (R := k) (M := V))).comp
        ((cotangentFamilyLinearizedDifferential R n).comp
          (familyResidueComponentEquiv R (n + 1)).symm.toLinearMap) =
      (TensorProduct.map
        (LinearMap.id (R := k) (M := Kₖ[n]))
        (cotangentFamilyEquiv R).toLinearMap).comp
          (exteriorPower.deletion k Mₖ n) := by
  let E := familyResidueComponentEquiv R (J := Fin e)
  let L : Kₖ[n + 1] →ₗ[k] Kₖ[n] ⊗[k] V :=
    (TensorProduct.map (E n).toLinearMap
      (LinearMap.id (R := k) (M := V))).comp
        ((cotangentFamilyLinearizedDifferential R n).comp
          (E (n + 1)).symm.toLinearMap)
  let D : Kₖ[n + 1] →ₗ[k] Kₖ[n] ⊗[k] V :=
    (TensorProduct.map
      (LinearMap.id (R := k) (M := Kₖ[n]))
      (cotangentFamilyEquiv R).toLinearMap).comp
        (exteriorPower.deletion k Mₖ n)
  change L = D
  apply LinearMap.ext
  intro y
  obtain ⟨q, rfl⟩ := (E (n + 1)).surjective y
  obtain ⟨z, rfl⟩ := Submodule.mkQ_surjective _ q
  let red : K[n + 1] →ₗ[R] Kₖ[n + 1] :=
    ((E (n + 1)).toLinearMap.restrictScalars R).comp
      (m • (⊤ : Submodule R K[n + 1])).mkQ
  let LR : K[n + 1] →ₗ[R] Kₖ[n] ⊗[k] V :=
    (L.restrictScalars R).comp red
  let DR : K[n + 1] →ₗ[R] Kₖ[n] ⊗[k] V :=
    (D.restrictScalars R).comp red
  have hLD : LR = DR := by
    apply exteriorPower.linearMap_ext
      (R := R) (n := n + 1) (M := M₀) (N := Kₖ[n] ⊗[k] V)
    apply AlternatingMap.ext
    intro b
    dsimp only [LR, DR, red, L, D]
    simp only [LinearMap.compAlternatingMap_apply, LinearMap.comp_apply,
      LinearMap.coe_restrictScalars]
    have hlin := congrArg (cotangentFamilyLinearizedDifferential R n)
      ((E (n + 1)).symm_apply_apply
        ((m • (⊤ : Submodule R K[n + 1])).mkQ
          (exteriorPower.ιMulti R (n + 1) b)))
    have houter := congrArg
      (TensorProduct.map (E n).toLinearMap
        (LinearMap.id (R := k) (M := V))) hlin
    calc
      _ = TensorProduct.map (E n).toLinearMap
          (LinearMap.id (R := k) (M := V))
            (cotangentFamilyLinearizedDifferential R n
              ((m • (⊤ : Submodule R K[n + 1])).mkQ
                (exteriorPower.ιMulti R (n + 1) b))) := houter
      _ = _ := by
        dsimp only [E]
        let A := TensorProduct.map
          (familyResidueComponentEquiv R (J := Fin e) n).toLinearMap
          (LinearMap.id (R := k) (M := V))
        let B := TensorProduct.map
          (LinearMap.id (R := k) (M := Kₖ[n]))
          (cotangentFamilyEquiv R).toLinearMap
        have hpublic :=
          cotangentFamilyLinearizedDifferential_mk_ιMulti R n b
        have hpublicOuter := congrArg A hpublic
        let w (i : Fin (n + 1)) : Kₖ[n] :=
          exteriorPower.ιMulti k n
            (fun q j => residue R ((b ∘ i.succAbove) q j))
        let c (i : Fin (n + 1)) : V :=
          (m).toCotangent (cotangentFamilyCoefficient R (b i))
        let t (i : Fin (n + 1)) : Kₖ[n] ⊗[k] V :=
          w i ⊗ₜ[k] c i
        let tβ (i : Fin (n + 1)) : Kₖ[n] ⊗[k] V :=
          w i ⊗ₜ[k] cotangentFamilyEquiv R
            (fun j => residue R (b i j))
        let S : Kₖ[n] ⊗[k] V :=
          ∑ i : Fin (n + 1), ((-1 : k) ^ (i : ℕ)) • t i
        let Sβ : Kₖ[n] ⊗[k] V :=
          ∑ i : Fin (n + 1), ((-1 : k) ^ (i : ℕ)) • tβ i
        calc
          _ = A
                (∑ i : Fin (n + 1),
                  (-1 : k) ^ (i : ℕ) •
                    (Submodule.Quotient.mk
                        (exteriorPower.ιMulti R n
                          (b ∘ i.succAbove)) ⊗ₜ[k]
                      (m).toCotangent
                        (cotangentFamilyCoefficient R (b i)))) :=
            hpublicOuter
          _ = _ := by
            have hA : A
                (∑ i : Fin (n + 1),
                  (-1 : k) ^ (i : ℕ) •
                    (Submodule.Quotient.mk
                        (exteriorPower.ιMulti R n
                          (b ∘ i.succAbove)) ⊗ₜ[k]
                      (m).toCotangent
                        (cotangentFamilyCoefficient R (b i)))) = S := by
              dsimp only [S]
              rw [map_sum]
              apply Finset.sum_congr rfl
              intro i _
              rw [map_smul]
              have hterm : A
                  (Submodule.Quotient.mk
                      (exteriorPower.ιMulti R n
                        (b ∘ i.succAbove)) ⊗ₜ[k]
                    (m).toCotangent
                      (cotangentFamilyCoefficient R (b i))) = t i := by
                have hE := familyResidueComponentEquiv_mk_ιMulti R n
                  (b ∘ i.succAbove)
                calc
                  _ = (familyResidueComponentEquiv R n).toLinearMap
                        (Submodule.Quotient.mk
                          (exteriorPower.ιMulti R n
                            (b ∘ i.succAbove))) ⊗ₜ[k]
                      (m).toCotangent
                        (cotangentFamilyCoefficient R (b i)) := by
                    dsimp only [A]
                    rw [TensorProduct.map_tmul, LinearMap.id_apply]
                  _ = t i := by
                    exact congrArg (fun z => z ⊗ₜ[k]
                      (m).toCotangent
                        (cotangentFamilyCoefficient R (b i))) hE
              rw [hterm]
            have hCoefficient : S = Sβ := by
              dsimp only [S, Sβ]
              apply Finset.sum_congr rfl
              intro i _
              dsimp only [t, tβ, w, c]
              rw [cotangentFamilyEquiv_residue_apply]
            have hDeletion : Sβ = B
                (exteriorPower.deletion k Mₖ n
                  (exteriorPower.ιMulti k (n + 1)
                    (fun q j => residue R (b q j)))) := by
              rw [exteriorPower.deletion_apply_ιMulti, map_sum]
              dsimp only [Sβ, B, tβ, w]
              simp only [map_smul, TensorProduct.map_tmul,
                LinearMap.id_apply]
              apply Finset.sum_congr rfl
              intro i _
              congr 3
            have hSource : B
                (exteriorPower.deletion k Mₖ n
                  (exteriorPower.ιMulti k (n + 1)
                    (fun q j => residue R (b q j)))) =
              B (exteriorPower.deletion k Mₖ n
                (familyResidueComponentEquiv R (n + 1)
                  ((m • (⊤ : Submodule R K[n + 1])).mkQ
                    (exteriorPower.ιMulti R (n + 1) b)))) := by
              have hE := familyResidueComponentEquiv_mk_ιMulti R
                (n + 1) b
              exact congrArg (fun z => B
                (exteriorPower.deletion k Mₖ n z)) hE.symm
            exact hA.trans (hCoefficient.trans (hDeletion.trans hSource))
  exact LinearMap.congr_fun hLD z

/-- Injectivity of the first-order cotangent-family differential.

The linearized Koszul differential is injective for every n ≥ 0. -/
theorem cotangentFamilyLinearizedDifferential_injective (n : ℕ) :
    Function.Injective (cotangentFamilyLinearizedDifferential R n) := by
  let E := familyResidueComponentEquiv R (J := Fin e)
  let T := TensorProduct.map
    (LinearMap.id (R := k) (M := Kₖ[n]))
    (cotangentFamilyEquiv R).toLinearMap
  let D := exteriorPower.deletion k Mₖ n
  have hT : Function.Bijective T :=
    TensorProduct.map_bijective Function.bijective_id
      (cotangentFamilyEquiv R).bijective
  have hright : Function.Injective (T.comp D) :=
    hT.injective.comp (exteriorPower.deletion_injective k Mₖ n)
  intro x y hxy
  apply (E (n + 1)).injective
  apply hright
  have hx := LinearMap.congr_fun
    (cotangentFamily_linearization R n) ((E (n + 1)) x)
  have hy := LinearMap.congr_fun
    (cotangentFamily_linearization R n) ((E (n + 1)) y)
  simp only [LinearMap.comp_apply] at hx hy
  dsimp only [E] at hx hy
  have hlinx := congrArg (cotangentFamilyLinearizedDifferential R n)
    ((familyResidueComponentEquiv R
      (J := Fin e) (n + 1)).symm_apply_apply x)
  have hliny := congrArg (cotangentFamilyLinearizedDifferential R n)
    ((familyResidueComponentEquiv R
      (J := Fin e) (n + 1)).symm_apply_apply y)
  have houterx := congrArg
    (TensorProduct.map
      (familyResidueComponentEquiv R n).toLinearMap
      (LinearMap.id (R := k) (M := V))) hlinx
  have houtery := congrArg
    (TensorProduct.map
      (familyResidueComponentEquiv R n).toLinearMap
      (LinearMap.id (R := k) (M := V))) hliny
  have hx' :
      TensorProduct.map (E n).toLinearMap
          (LinearMap.id (R := k) (M := V))
          (cotangentFamilyLinearizedDifferential R n x) =
        TensorProduct.map
          (LinearMap.id (R := k) (M := Kₖ[n]))
          (cotangentFamilyEquiv R).toLinearMap
            (exteriorPower.deletion k Mₖ n
              (familyResidueComponentEquiv R (n + 1) x)) :=
    houterx.symm.trans hx
  have hy' :
      TensorProduct.map (E n).toLinearMap
          (LinearMap.id (R := k) (M := V))
          (cotangentFamilyLinearizedDifferential R n y) =
        TensorProduct.map
          (LinearMap.id (R := k) (M := Kₖ[n]))
          (cotangentFamilyEquiv R).toLinearMap
            (exteriorPower.deletion k Mₖ n
              (familyResidueComponentEquiv R (n + 1) y)) :=
    houtery.symm.trans hy
  change
    TensorProduct.map
        (LinearMap.id (R := k) (M := Kₖ[n]))
        (cotangentFamilyEquiv R).toLinearMap
          (exteriorPower.deletion k Mₖ n
            (familyResidueComponentEquiv R (n + 1) x)) =
      TensorProduct.map
        (LinearMap.id (R := k) (M := Kₖ[n]))
        (cotangentFamilyEquiv R).toLinearMap
          (exteriorPower.deletion k Mₖ n
            (familyResidueComponentEquiv R (n + 1) y))
  exact hx'.symm.trans ((congrArg
    (TensorProduct.map (E n).toLinearMap
      (LinearMap.id (R := k) (M := V))) hxy).trans hy')

end

end KoszulComplex
