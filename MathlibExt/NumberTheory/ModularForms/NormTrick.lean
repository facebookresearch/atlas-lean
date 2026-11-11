/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_ModularForm_exists_mul_eq_mul_norm_of_forall_slash_mul_eq.lean`
and
`P2M/Sol/S_ModularForm_exists_mul_eq_mul_norm_of_forall_slash_mul_eq.lean`
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

public import Mathlib.NumberTheory.ModularForms.NormTrace
public import Mathlib.NumberTheory.ModularForms.SlashActions
public import Mathlib.NumberTheory.ModularForms.Cusps
public import Mathlib.NumberTheory.ModularForms.BoundedAtCusp

/-!
# The norm trick for modular forms

Given two modular forms `F G` of the same level satisfying a commutation
relation under the slash action of a larger group `ℋ`, the product over the
cosets of a glued function is a modular form `Φ` of level `ℋ` with
`Φ * G = F * norm ℋ G`.
-/

@[expose] public section

open scoped ModularForm Manifold

variable {𝒢 ℋ : Subgroup (GL (Fin 2) ℝ)} {k : ℤ}

local notation "𝒬" => ℋ ⧸ (𝒢.subgroupOf ℋ)

namespace NormTrickAux

open UpperHalfPlane SlashInvariantForm

variable (𝒢 ℋ) in
/-- The identity coset. -/
private def one𝒬 : 𝒬 := ((1 : ℋ) : 𝒬)

private theorem smul_mk (h r : ℋ) : h • ((r : ℋ) : 𝒬) = ((h * r : ℋ) : 𝒬) := rfl

private theorem mk_eq_one𝒬_iff (r : ℋ) :
    ((r : ℋ) : 𝒬) = one𝒬 𝒢 ℋ ↔ (r : GL (Fin 2) ℝ) ∈ 𝒢 := by
  rw [one𝒬, QuotientGroup.eq, mul_one, Subgroup.mem_subgroupOf]
  simp

private theorem smul_one𝒬 (h : ℋ) : h • one𝒬 𝒢 ℋ = ((h : ℋ) : 𝒬) := by
  rw [one𝒬, smul_mk, mul_one]

private theorem smul_eq_one𝒬_iff_of_mem {h : ℋ} (hmem : (h : GL (Fin 2) ℝ) ∈ 𝒢) (d : 𝒬) :
    h • d = one𝒬 𝒢 ℋ ↔ d = one𝒬 𝒢 ℋ := by
  induction d using QuotientGroup.induction_on with
  | H r =>
    rw [smul_mk, mk_eq_one𝒬_iff, mk_eq_one𝒬_iff]
    change (h : GL (Fin 2) ℝ) * (r : GL (Fin 2) ℝ) ∈ 𝒢 ↔ (r : GL (Fin 2) ℝ) ∈ 𝒢
    exact ⟨fun hr => by simpa using 𝒢.mul_mem (𝒢.inv_mem hmem) hr, fun hr => 𝒢.mul_mem hmem hr⟩

/-- The glued function: `F` on the identity coset, `G` elsewhere. -/
private noncomputable def X (F G : ModularForm 𝒢 k) (c : 𝒬) : ModularForm 𝒢 k :=
  haveI := Classical.dec (c = one𝒬 𝒢 ℋ)
  if c = one𝒬 𝒢 ℋ then F else G

private theorem X_one (F G : ModularForm 𝒢 k) : X F G (one𝒬 𝒢 ℋ) = F := by
  simp [X]

private theorem X_of_ne (F G : ModularForm 𝒢 k) {c : 𝒬} (hc : c ≠ one𝒬 𝒢 ℋ) :
    X F G c = G := by
  simp [X, hc]

/-- The translate of the glued function by a coset. -/
private noncomputable def Θ (F G : ModularForm 𝒢 k) (c : 𝒬) : ℍ → ℂ := quotientFunc (X F G c) c

private theorem quotientFunc_one𝒬 (G : ModularForm 𝒢 k) :
    quotientFunc G (one𝒬 𝒢 ℋ) = ⇑G := by
  change (⇑G : ℍ → ℂ) ∣[k] (((1 : ℋ) : GL (Fin 2) ℝ))⁻¹ = ⇑G
  simp

private theorem Θ_one (F G : ModularForm 𝒢 k) : Θ F G (one𝒬 𝒢 ℋ) = ⇑F := by
  rw [Θ, X_one, quotientFunc_one𝒬]

private theorem Θ_of_ne (F G : ModularForm 𝒢 k) {c : 𝒬} (hc : c ≠ one𝒬 𝒢 ℋ) :
    Θ F G c = quotientFunc G c := by
  rw [Θ, X_of_ne F G hc]

private theorem quotientFunc_mk' (G : ModularForm 𝒢 k) (r : ℋ) :
    quotientFunc G ((r : ℋ) : 𝒬) = (⇑G : ℍ → ℂ) ∣[k] ((r : GL (Fin 2) ℝ))⁻¹ := rfl

private theorem prod_smul_eq [Fintype 𝒬] (F G : ModularForm 𝒢 k)
    (hFG : ∀ h ∈ ℋ, ((⇑F : ℍ → ℂ) ∣[k] h) * (⇑G : ℍ → ℂ) =
      (⇑F : ℍ → ℂ) * ((⇑G : ℍ → ℂ) ∣[k] h))
    (h' : ℋ) :
    ∏ d : 𝒬, quotientFunc (X F G (h' • d)) d = ∏ d : 𝒬, Θ F G d := by
  classical
  by_cases hmem : (h' : GL (Fin 2) ℝ) ∈ 𝒢
  · refine Finset.prod_congr rfl fun d _ => ?_
    by_cases hd : d = one𝒬 𝒢 ℋ
    · have e : h' • d = one𝒬 𝒢 ℋ := (smul_eq_one𝒬_iff_of_mem hmem d).mpr hd
      rw [Θ, e, hd, X_one]
    · have e : h' • d ≠ one𝒬 𝒢 ℋ := fun e => hd ((smul_eq_one𝒬_iff_of_mem hmem d).mp e)
      rw [Θ, X_of_ne F G hd, X_of_ne F G e]
  · have hb1 : h'⁻¹ • one𝒬 𝒢 ℋ ≠ one𝒬 𝒢 ℋ := by
      rw [Ne, smul_one𝒬, mk_eq_one𝒬_iff]
      intro hi
      exact hmem (by simpa using 𝒢.inv_mem hi)
    have hb2 : h' • (h'⁻¹ • one𝒬 𝒢 ℋ) = one𝒬 𝒢 ℋ := smul_inv_smul _ _
    have hne : h' • one𝒬 𝒢 ℋ ≠ one𝒬 𝒢 ℋ := by
      rw [Ne, smul_one𝒬, mk_eq_one𝒬_iff]; exact hmem
    have v1 : quotientFunc (X F G (h' • one𝒬 𝒢 ℋ)) (one𝒬 𝒢 ℋ) = ⇑G := by
      rw [X_of_ne F G hne, quotientFunc_one𝒬]
    have v2 : quotientFunc (X F G (h' • (h'⁻¹ • one𝒬 𝒢 ℋ))) (h'⁻¹ • one𝒬 𝒢 ℋ) =
        (⇑F : ℍ → ℂ) ∣[k] (h' : GL (Fin 2) ℝ) := by
      rw [hb2, X_one, smul_one𝒬, quotientFunc_mk']
      simp
    have w1 : Θ F G (one𝒬 𝒢 ℋ) = ⇑F := Θ_one F G
    have w2 : Θ F G (h'⁻¹ • one𝒬 𝒢 ℋ) = (⇑G : ℍ → ℂ) ∣[k] (h' : GL (Fin 2) ℝ) := by
      rw [Θ_of_ne F G hb1, smul_one𝒬, quotientFunc_mk']
      simp
    have hoff : ∀ d : 𝒬, d ≠ one𝒬 𝒢 ℋ → d ≠ h'⁻¹ • one𝒬 𝒢 ℋ →
        quotientFunc (X F G (h' • d)) d = Θ F G d := by
      intro d hd1 hdb
      have : h' • d ≠ one𝒬 𝒢 ℋ := by
        intro e
        apply hdb
        rw [← e, inv_smul_smul]
      rw [X_of_ne F G this, Θ_of_ne F G hd1]
    have hmemb : h'⁻¹ • one𝒬 𝒢 ℋ ∈ (Finset.univ : Finset 𝒬).erase (one𝒬 𝒢 ℋ) :=
      Finset.mem_erase.mpr ⟨hb1, Finset.mem_univ _⟩
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ (one𝒬 𝒢 ℋ)), ← Finset.mul_prod_erase _ _ hmemb,
      ← Finset.mul_prod_erase _ (Θ F G) (Finset.mem_univ (one𝒬 𝒢 ℋ)),
      ← Finset.mul_prod_erase _ (Θ F G) hmemb, v1, v2, w1, w2]
    have hrest : ∏ d ∈ ((Finset.univ : Finset 𝒬).erase (one𝒬 𝒢 ℋ)).erase (h'⁻¹ • one𝒬 𝒢 ℋ),
          quotientFunc (X F G (h' • d)) d =
        ∏ d ∈ ((Finset.univ : Finset 𝒬).erase (one𝒬 𝒢 ℋ)).erase (h'⁻¹ • one𝒬 𝒢 ℋ), Θ F G d := by
      refine Finset.prod_congr rfl fun d hd => ?_
      rw [Finset.mem_erase, Finset.mem_erase] at hd
      exact hoff d hd.2.1 hd.1
    rw [hrest, ← mul_assoc, ← mul_assoc,
      mul_comm (⇑G : ℍ → ℂ) ((⇑F : ℍ → ℂ) ∣[k] (h' : GL (Fin 2) ℝ)), hFG _ h'.2]

variable [𝒢.IsFiniteRelIndex ℋ] [ℋ.HasDetPlusMinusOne]

/-- The glued product as a slash-invariant form of level `ℋ`. -/
private noncomputable def ΦSIF (F G : ModularForm 𝒢 k)
    (hFG : ∀ h ∈ ℋ, ((⇑F : ℍ → ℂ) ∣[k] h) * (⇑G : ℍ → ℂ) =
      (⇑F : ℍ → ℂ) * ((⇑G : ℍ → ℂ) ∣[k] h)) :
    SlashInvariantForm ℋ (k * Nat.card 𝒬) where
  toFun := let := Fintype.ofFinite 𝒬; ∏ c : 𝒬, Θ F G c
  slash_action_eq' h hh := by
    let := Fintype.ofFinite 𝒬
    rw [Nat.card_eq_fintype_card, ← Finset.card_univ, ModularForm.prod_slash,
      Subgroup.HasDetPlusMinusOne.abs_det hh, one_zpow, one_smul]
    have hfac : ∀ c : 𝒬, (Θ F G c) ∣[k] h =
        quotientFunc (X F G c) ((⟨h, hh⟩ : ℋ)⁻¹ • c) := fun c =>
      quotientFunc_smul (X F G c) hh c
    simp_rw [hfac]
    have hperm : ∏ c : 𝒬, quotientFunc (X F G c) ((⟨h, hh⟩ : ℋ)⁻¹ • c) =
        ∏ d : 𝒬, quotientFunc (X F G ((⟨h, hh⟩ : ℋ) • d)) d := by
      rw [← Equiv.prod_comp (MulAction.toPerm ((⟨h, hh⟩ : ℋ)))
        (fun c : 𝒬 => quotientFunc (X F G c) ((⟨h, hh⟩ : ℋ)⁻¹ • c))]
      refine Finset.prod_congr rfl fun d _ => ?_
      simp only [MulAction.toPerm_apply, inv_smul_smul]
    rw [hperm]
    exact prod_smul_eq F G hFG ⟨h, hh⟩

private theorem ΦSIF_coe (F G : ModularForm 𝒢 k)
    (hFG : ∀ h ∈ ℋ, ((⇑F : ℍ → ℂ) ∣[k] h) * (⇑G : ℍ → ℂ) =
      (⇑F : ℍ → ℂ) * ((⇑G : ℍ → ℂ) ∣[k] h)) :
    (⇑(ΦSIF F G hFG) : ℍ → ℂ) = let := Fintype.ofFinite 𝒬; ∏ c : 𝒬, Θ F G c := rfl

/-- The glued product as a modular form of level `ℋ`. -/
private noncomputable def ΦMF (F G : ModularForm 𝒢 k)
    (hFG : ∀ h ∈ ℋ, ((⇑F : ℍ → ℂ) ∣[k] h) * (⇑G : ℍ → ℂ) =
      (⇑F : ℍ → ℂ) * ((⇑G : ℍ → ℂ) ∣[k] h)) :
    ModularForm ℋ (k * Nat.card 𝒬) where
  __ := ΦSIF F G hFG
  holo' := by
    let := Fintype.ofFinite 𝒬
    change MDiff (⇑(ΦSIF F G hFG) : ℍ → ℂ)
    rw [ΦSIF_coe]
    refine MDifferentiable.prod (fun c _ => ?_)
    induction c using Quotient.inductionOn with
    | h r => exact (ModularForm.translate (X F G ⟦r⟧) (r : GL (Fin 2) ℝ)⁻¹).holo'
  bdd_at_cusps' hc γ := by
    rintro rfl
    let := Fintype.ofFinite 𝒬
    change IsBoundedAtImInfty ((⇑(ΦSIF F G hFG) : ℍ → ℂ) ∣[k * Nat.card 𝒬] γ)
    rw [ΦSIF_coe]
    simp_rw [IsBoundedAtImInfty, Filter.BoundedAtFilter]
    rw [Nat.card_eq_fintype_card, ← Finset.card_univ, ModularForm.prod_slash]
    apply Asymptotics.IsBigO.const_smul_left
    rw [show (1 : ℍ → ℝ) = (fun x ↦ ∏ (i : 𝒬), 1) by ext; simp, Finset.prod_fn]
    refine .finsetProd (fun c _ => ?_)
    induction c using Quotient.inductionOn with
    | h r =>
      refine (ModularForm.translate (X F G ⟦r⟧) (r : GL (Fin 2) ℝ)⁻¹).bdd_at_cusps' ?_ γ rfl
      simpa using hc.of_isFiniteRelIndex_conj r.2

private theorem ΦMF_coe (F G : ModularForm 𝒢 k)
    (hFG : ∀ h ∈ ℋ, ((⇑F : ℍ → ℂ) ∣[k] h) * (⇑G : ℍ → ℂ) =
      (⇑F : ℍ → ℂ) * ((⇑G : ℍ → ℂ) ∣[k] h)) :
    (⇑(ΦMF F G hFG) : ℍ → ℂ) = let := Fintype.ofFinite 𝒬; ∏ c : 𝒬, Θ F G c := rfl

private theorem ΦMF_mul (F G : ModularForm 𝒢 k)
    (hFG : ∀ h ∈ ℋ, ((⇑F : ℍ → ℂ) ∣[k] h) * (⇑G : ℍ → ℂ) =
      (⇑F : ℍ → ℂ) * ((⇑G : ℍ → ℂ) ∣[k] h)) :
    (⇑(ΦMF F G hFG) : ℍ → ℂ) * (⇑G : ℍ → ℂ) =
      (⇑F : ℍ → ℂ) * (⇑(ModularForm.norm ℋ G) : ℍ → ℂ) := by
  let := Fintype.ofFinite 𝒬
  classical
  rw [ΦMF_coe, ModularForm.coe_norm]
  have e1 : (∏ c : 𝒬, Θ F G c) =
      Θ F G (one𝒬 𝒢 ℋ) * ∏ c ∈ (Finset.univ : Finset 𝒬).erase (one𝒬 𝒢 ℋ), Θ F G c :=
    (Finset.mul_prod_erase _ (Θ F G) (Finset.mem_univ (one𝒬 𝒢 ℋ))).symm
  have e2 : (∏ c : 𝒬, quotientFunc G c) =
      quotientFunc G (one𝒬 𝒢 ℋ) * ∏ c ∈ (Finset.univ : Finset 𝒬).erase (one𝒬 𝒢 ℋ),
        quotientFunc G c := by
    rw [Finset.mul_prod_erase _ (fun c : 𝒬 => quotientFunc G c) (Finset.mem_univ (one𝒬 𝒢 ℋ))]
  have e3 : ∏ d ∈ (Finset.univ : Finset 𝒬).erase (one𝒬 𝒢 ℋ), Θ F G d =
      ∏ d ∈ (Finset.univ : Finset 𝒬).erase (one𝒬 𝒢 ℋ), quotientFunc G d :=
    Finset.prod_congr rfl fun d hd => Θ_of_ne F G (Finset.mem_erase.mp hd).1
  rw [e1, e2, e3, Θ_one, quotientFunc_one𝒬]
  ring

end NormTrickAux

namespace ModularForm

/-- The norm trick: two modular forms satisfying a commutation relation under
the slash action of `ℋ` give rise to a modular form `Φ` of level `ℋ` with
`Φ * G = F * norm ℋ G`. -/
theorem exists_mul_eq_mul_norm_of_forall_slash_mul_eq
    (𝒢 ℋ : Subgroup (GL (Fin 2) ℝ)) [𝒢.IsFiniteRelIndex ℋ] [ℋ.HasDetPlusMinusOne] {k : ℤ}
    (F G : ModularForm 𝒢 k)
    (hFG : ∀ h ∈ ℋ, ((⇑F : UpperHalfPlane → ℂ) ∣[k] h) * (⇑G : UpperHalfPlane → ℂ) =
      (⇑F : UpperHalfPlane → ℂ) * ((⇑G : UpperHalfPlane → ℂ) ∣[k] h)) :
    ∃ Φ : ModularForm ℋ (k * Nat.card (ℋ ⧸ 𝒢.subgroupOf ℋ)),
      (⇑Φ : UpperHalfPlane → ℂ) * (⇑G : UpperHalfPlane → ℂ) =
        (⇑F : UpperHalfPlane → ℂ) * (⇑(ModularForm.norm ℋ G) : UpperHalfPlane → ℂ) :=
  ⟨NormTrickAux.ΦMF F G hFG, NormTrickAux.ΦMF_mul F G hFG⟩

end ModularForm
