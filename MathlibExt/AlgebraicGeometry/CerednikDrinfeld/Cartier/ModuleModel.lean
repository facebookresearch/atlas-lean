/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
The upstream NOTICE also credits Mathlib as a whole:
https://github.com/leanprover-community/mathlib4
Copyright (c) the respective Mathlib authors, as recorded in the headers of the
Mathlib source files.
Released under the Apache License, Version 2.0.
-/

/-
Adapted from https://github.com/anthropics/fermats-last-theorem, compared with the
source file at commit `6e837e75355538c7f80bab5b956861e86c4eacc2`:
`Definitions/Def_CerednikDrinfeld_CartierModuleModel.lean`
The source is machine-generated proof code built around a proof-extraction
framework; the statements and proofs are reused here with that machinery
removed and the names restated in Mathlib style.
Adaptations copyright (c) Meta Platforms, Inc. and affiliates, under the
license in the root LICENSE file.
-/

module

public import MathlibExt.AlgebraicGeometry.CerednikDrinfeld.Cartier.GradedPiece
public import MathlibExt.RingTheory.MvFormalGroup.Cartier.IntVerschiebung
public import MathlibExt.RingTheory.WittVector.GradedCartierModuleData

/-!
# Cartier module models of formal `O_D`-modules

For a formal `O_D`-module `X` over `B`, `FormalODModule.varpiLinear` is the action of the
uniformizer on the Cartier module as a `WittVector p B`-linear map and
`FormalODModule.gradedSubmodule` is the graded piece as a submodule. When the graded pieces
`0` and `1` are complementary, `FormalODModule.toGradedCartierModuleData` is the resulting
`GradedCartierModuleData`, with its fields computed by the `toGradedCartierModuleData_*`
lemmas.

## References

* J.-F. Boutot and H. Carayol, *Uniformisation p-adique des courbes de Shimura : les théorèmes
  de Čerednik et de Drinfeld*, in *Courbes modulaires et courbes de Shimura*, Astérisque
  196–197 (1991), 45–158, for special formal `O_D`-modules and their Cartier modules.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u

namespace MvFormalGroup

open MvPowerSeries

namespace WittLaw

variable {p : ℕ} [hp : Fact p.Prime] {R : Type u} [CommRing R]

omit hp in
theorem hasSubst_subst_comp {σ τ υ : Type*} {a : σ → MvPowerSeries τ R}
    {b : τ → MvPowerSeries υ R} (ha : HasSubst a) (hb : HasSubst b) :
    HasSubst (fun s => subst b (a s)) := by
  simpa only [coe_substAlgHom] using ha.comp hb

theorem verschiebung_cVec {τ : Type} (w : WittVector p R) :
    WittVector.verschiebung (cVec p (τ := τ) w) = cVec p (WittVector.verschiebung w) :=
  (WittVector.map_verschiebung _ w).symm

theorem mulPoly_verschiebung_zero (w : WittVector p R) :
    mulPoly p (WittVector.verschiebung w) 0 = 0 := by
  change (cVec p (WittVector.verschiebung w) * xTaut p R).coeff 0 = 0
  rw [← verschiebung_cVec, ← WittVector.verschiebung_mul_frobenius]
  exact WittVector.verschiebung_coeff_zero _

theorem mulPoly_verschiebung_succ (w : WittVector p R) (n : ℕ) :
    mulPoly p (WittVector.verschiebung w) (n + 1) =
      (cVec p w * WittVector.frobenius (xTaut p R)).coeff n := by
  change (cVec p (WittVector.verschiebung w) * xTaut p R).coeff (n + 1) = _
  rw [← verschiebung_cVec, ← WittVector.verschiebung_mul_frobenius]
  exact WittVector.verschiebung_coeff_succ _ n

theorem subst_frobPolyFam_mulFam (w : WittVector p R) (n : ℕ) :
    subst (frobPolyFam p R) (mulFam p w n) =
      (((cVec p w * WittVector.frobenius (xTaut p R)).coeff n : MvPolynomial ℕ R) :
        MvPowerSeries ℕ R) := by
  have hf : frobPolyFam p R = fun m => (frobPoly p R m : MvPowerSeries ℕ R) := rfl
  rw [hf, mulFam_apply, ← coe_aeval, aeval_mulPoly, mk_frobPoly]

theorem hasSubst_mulFam_frobPolyFam (w : WittVector p R) :
    HasSubst (fun k => subst (frobPolyFam p R) (mulFam p w k)) :=
  hasSubst_subst_comp (hasSubst_mulFam w) hasSubst_frobPolyFam

theorem subst_verFam_mulFam_frobPolyFam (w : WittVector p R) (n : ℕ) :
    subst (fun k => subst (frobPolyFam p R) (mulFam p w k)) (verFam R n) =
      mulFam p (WittVector.verschiebung w) n := by
  have hc := hasSubst_mulFam_frobPolyFam (p := p) (R := R) w
  cases n with
  | zero =>
    rw [verFam_zero, ← coe_substAlgHom hc, map_zero, mulFam_apply, mulPoly_verschiebung_zero,
      MvPolynomial.coe_zero]
  | succ k =>
    rw [verFam_succ, subst_X hc, subst_frobPolyFam_mulFam, mulFam_apply, mulPoly_verschiebung_succ]

end WittLaw

namespace CartierModule

variable {p : ℕ} [hp : Fact p.Prime] {d : ℕ} {R : Type u} [CommRing R] {Φ : MvFormalGroup d R}

theorem verschiebungInt_smul_frobenius [Φ.IsComm] (w : WittVector p R) (f : CartierModule p Φ) :
    verschiebungInt (w • frobenius f) = WittVector.verschiebung w • f := by
  apply CartierModule.ext
  funext j
  change subst (WittLaw.frobPolyFam p R) (subst (WittLaw.mulFam p w)
      (subst (WittLaw.verFam R) (f.toPowerSeries j))) =
    subst (WittLaw.mulFam p (WittVector.verschiebung w)) (f.toPowerSeries j)
  rw [subst_comp_subst_apply (WittLaw.hasSubst_mulFam w) WittLaw.hasSubst_frobPolyFam,
    subst_comp_subst_apply WittLaw.hasSubst_verFam (WittLaw.hasSubst_mulFam_frobPolyFam w)]
  congr 1
  funext n
  exact WittLaw.subst_verFam_mulFam_frobPolyFam w n

end CartierModule

end MvFormalGroup

namespace CerednikDrinfeld

namespace FormalODModule

open MvFormalGroup MvFormalGroup.CartierModule

variable {p : ℕ} [hp : Fact p.Prime] {B : Type u} [CommRing B]

theorem endAct_varpiEnd_endAct_varpiEnd (X : FormalODModule p B) (f : CartierModule p X.F) :
    endAct X.varpiEnd (endAct X.varpiEnd f) = (p : ℕ) • f := by
  have h : endAct (p := p) X.varpiEnd * endAct (p := p) X.varpiEnd =
      endAct (p := p) ((p : ℕ) : MvFormalGroup.End X.F) := by
    rw [← map_mul, varpiEnd_mul_varpiEnd, map_natCast]
  rw [← endAct_natCast p f, ← h]
  rfl

def varpiLinear (X : FormalODModule p B) :
    CartierModule p X.F →ₗ[WittVector p B] CartierModule p X.F where
  toFun := endAct X.varpiEnd
  map_add' := map_add (endAct X.varpiEnd)
  map_smul' := endAct_smul_witt X.varpiEnd

@[simp] theorem varpiLinear_apply (X : FormalODModule p B) (f : CartierModule p X.F) :
    X.varpiLinear f = endAct X.varpiEnd f := rfl

theorem smul_mem_gradedPiece (X : FormalODModule p B) (j : Zp2 p →+* B) (n : ℕ)
    (w : WittVector p B) (f : CartierModule p X.F) (hf : f ∈ X.gradedPiece j n) :
    w • f ∈ X.gradedPiece j n := by
  refine (mem_gradedPiece_iff X j n _).2 fun c => ?_
  rw [endAct_smul_witt, homothety_smul_witt, (mem_gradedPiece_iff X j n f).1 hf c]

def gradedSubmodule (X : FormalODModule p B) (j : Zp2 p →+* B) (n : ℕ) :
    Submodule (WittVector p B) (CartierModule p X.F) where
  carrier := X.gradedPiece j n
  add_mem' hf hg := (X.gradedPiece j n).add_mem hf hg
  zero_mem' := (X.gradedPiece j n).zero_mem
  smul_mem' w {f} hf := smul_mem_gradedPiece X j n w f hf

@[simp] theorem mem_gradedSubmodule_iff (X : FormalODModule p B) (j : Zp2 p →+* B) (n : ℕ)
    (f : CartierModule p X.F) : f ∈ X.gradedSubmodule j n ↔ f ∈ X.gradedPiece j n :=
  Iff.rfl

@[simp] theorem gradedSubmodule_toAddSubgroup (X : FormalODModule p B) (j : Zp2 p →+* B) (n : ℕ) :
    (X.gradedSubmodule j n).toAddSubgroup = X.gradedPiece j n :=
  rfl

theorem gradedSubmodule_add_two (X : FormalODModule p B) (j : Zp2 p →+* B) (n : ℕ) :
    X.gradedSubmodule j (n + 2) = X.gradedSubmodule j n :=
  Submodule.toAddSubgroup_injective (by
    rw [gradedSubmodule_toAddSubgroup, gradedSubmodule_toAddSubgroup, gradedPiece_add_two])

theorem isCompl_gradedSubmodule_iff (X : FormalODModule p B) (j : Zp2 p →+* B) (m n : ℕ) :
    IsCompl (X.gradedSubmodule j m) (X.gradedSubmodule j n) ↔
      IsCompl (X.gradedPiece j m) (X.gradedPiece j n) := by
  simp only [isCompl_iff, disjoint_iff_inf_le, codisjoint_iff_le_sup, IsConcreteLE.le_iff,
    Submodule.mem_inf, AddSubgroup.mem_inf, Submodule.mem_bot, AddSubgroup.mem_bot,
    Submodule.mem_top, AddSubgroup.mem_top, Submodule.mem_sup, AddSubgroup.mem_sup,
    mem_gradedSubmodule_iff]

theorem gradedPiece_fin_add_one (X : FormalODModule p B) (j : Zp2 p →+* B) (i : Fin 2) :
    X.gradedPiece j ((i + 1 : Fin 2) : ℕ) = X.gradedPiece j ((i : ℕ) + 1) := by
  fin_cases i
  · rfl
  · exact (gradedPiece_add_two X j 0).symm

theorem verschiebungInt_mem_gradedPiece_succ (X : FormalODModule p B) (j : Zp2 p →+* B) (n : ℕ)
    (f : CartierModule p X.F) (hf : f ∈ X.gradedPiece j n) :
    verschiebungInt f ∈ X.gradedPiece j (n + 1) := by
  refine (mem_gradedPiece_iff X j (n + 1) _).2 fun c => ?_
  have h2 : j (WittVector.teichmuller p c) ^ p ^ (n + 1 + 1) =
      j (WittVector.teichmuller p c) ^ p ^ n :=
    apply_teichmuller_pow_pow_add_two j c n
  rw [endAct_verschiebungInt, (mem_gradedPiece_iff X j n f).1 hf c, homothety_verschiebungInt,
    ← pow_mul, ← pow_succ, h2]

theorem frobenius_mem_gradedPiece_succ (X : FormalODModule p B) (j : Zp2 p →+* B) (n : ℕ)
    (f : CartierModule p X.F) (hf : f ∈ X.gradedPiece j n) :
    frobenius f ∈ X.gradedPiece j (n + 1) := by
  refine (mem_gradedPiece_iff X j (n + 1) _).2 fun c => ?_
  rw [endAct_frobenius, (mem_gradedPiece_iff X j n f).1 hf c, frobenius_homothety, ← pow_mul,
    ← pow_succ]

theorem endAct_varpiEnd_mem_gradedPiece_succ (X : FormalODModule p B) (j : Zp2 p →+* B) (n : ℕ)
    (f : CartierModule p X.F) (hf : f ∈ X.gradedPiece j n) :
    endAct X.varpiEnd f ∈ X.gradedPiece j (n + 1) := by
  refine (mem_gradedPiece_iff X j (n + 1) _).2 fun c => ?_
  have hc : WittVector.teichmuller p c =
      WittVector.frobenius (WittVector.teichmuller p (c ^ p)) := by
    rw [WittVector.frobenius_teichmuller_eq, ← pow_mul, ← pow_two, pow_card_galoisField]
  have key : endAct (X.actEnd (WittVector.teichmuller p c)) (endAct X.varpiEnd f) =
      endAct X.varpiEnd (endAct (X.actEnd (WittVector.teichmuller p (c ^ p))) f) := by
    change
        (endAct (p := p) (X.actEnd (WittVector.teichmuller p c)) * endAct (p := p) X.varpiEnd) f =
      (endAct (p := p) X.varpiEnd *
        endAct (p := p) (X.actEnd (WittVector.teichmuller p (c ^ p)))) f
    rw [← map_mul, ← map_mul, hc, ← varpiEnd_mul_actEnd]
  rw [key, (mem_gradedPiece_iff X j n f).1 hf (c ^ p), endAct_homothety,
    map_pow (WittVector.teichmuller p) c p, map_pow j _ p, ← pow_mul, ← pow_succ']

/-- **Graded Cartier module data of a formal `O_D`-module.** For a formal `O_D`-module `X` over a
commutative ring `B` and a ring homomorphism `j : Zp2 p →+* B` such that the graded pieces `0`
and `1` of the Cartier module are complementary, the Cartier module with its `WittVector p B`
action, the Frobenius, the Verschiebung `verschiebungInt`, the action of `ϖ`, and the graded
pieces `0` and `1`. -/
def toGradedCartierModuleData {B : Type u} [CommRing B] (X : FormalODModule p B) (j : Zp2 p →+* B)
    (hc : IsCompl (X.gradedPiece j 0) (X.gradedPiece j 1)) : GradedCartierModuleData p j where
  M := CartierModule p X.F
  frobenius := MvFormalGroup.CartierModule.frobenius
  verschiebung := MvFormalGroup.CartierModule.verschiebungInt
  varpi := X.varpiLinear
  piece i := X.gradedSubmodule j (i : ℕ)
  frobenius_smul := frobenius_smul
  smul_verschiebung := smul_verschiebungInt
  verschiebung_smul_frobenius := verschiebungInt_smul_frobenius
  frobenius_verschiebung := frobenius_verschiebungInt
  varpi_verschiebung := endAct_verschiebungInt X.varpiEnd
  varpi_frobenius := endAct_frobenius X.varpiEnd
  varpi_varpi := endAct_varpiEnd_endAct_varpiEnd X
  isCompl_piece := (isCompl_gradedSubmodule_iff X j 0 1).2 hc
  verschiebung_mem i f hf := by
    change verschiebungInt f ∈ X.gradedPiece j ((i + 1 : Fin 2) : ℕ)
    rw [gradedPiece_fin_add_one]
    exact verschiebungInt_mem_gradedPiece_succ X j i f hf
  frobenius_mem i f hf := by
    change MvFormalGroup.CartierModule.frobenius f ∈ X.gradedPiece j ((i + 1 : Fin 2) : ℕ)
    rw [gradedPiece_fin_add_one]
    exact frobenius_mem_gradedPiece_succ X j i f hf
  varpi_mem i f hf := by
    change endAct X.varpiEnd f ∈ X.gradedPiece j ((i + 1 : Fin 2) : ℕ)
    rw [gradedPiece_fin_add_one]
    exact endAct_varpiEnd_mem_gradedPiece_succ X j i f hf

section model

variable {B : Type u} [CommRing B] (X : FormalODModule p B) (j : Zp2 p →+* B)
  (hc : IsCompl (X.gradedPiece j 0) (X.gradedPiece j 1))

theorem toGradedCartierModuleData_M :
    (X.toGradedCartierModuleData j hc).M = CartierModule p X.F := rfl

theorem toGradedCartierModuleData_frobenius :
    (X.toGradedCartierModuleData j hc).frobenius = MvFormalGroup.CartierModule.frobenius := rfl

@[simp] theorem toGradedCartierModuleData_frobenius_apply (f : CartierModule p X.F) :
    (X.toGradedCartierModuleData j hc).frobenius f = MvFormalGroup.CartierModule.frobenius f := rfl

theorem toGradedCartierModuleData_verschiebung :
    (X.toGradedCartierModuleData j hc).verschiebung = MvFormalGroup.CartierModule.verschiebungInt :=
  rfl

@[simp] theorem toGradedCartierModuleData_verschiebung_apply (f : CartierModule p X.F) :
    (X.toGradedCartierModuleData j hc).verschiebung f = verschiebungInt f := rfl

theorem toGradedCartierModuleData_varpi :
    (X.toGradedCartierModuleData j hc).varpi = X.varpiLinear := rfl

@[simp] theorem toGradedCartierModuleData_varpi_apply (f : CartierModule p X.F) :
    (X.toGradedCartierModuleData j hc).varpi f = endAct X.varpiEnd f := rfl

theorem toGradedCartierModuleData_piece (i : Fin 2) :
    (X.toGradedCartierModuleData j hc).piece i = X.gradedSubmodule j (i : ℕ) := rfl

@[simp] theorem mem_toGradedCartierModuleData_piece_iff (i : Fin 2) (f : CartierModule p X.F) :
    f ∈ (X.toGradedCartierModuleData j hc).piece i ↔ f ∈ X.gradedPiece j (i : ℕ) := Iff.rfl

theorem toGradedCartierModuleData_smul (w : WittVector p B) (f : CartierModule p X.F) :
    (HSMul.hSMul (γ := (X.toGradedCartierModuleData j hc).M) w f) = w • f := rfl

@[simp high] theorem toGradedCartierModuleData_homothety_apply (b : B) (f : CartierModule p X.F) :
    (X.toGradedCartierModuleData j hc).homothety b f = homothety b f :=
  teichmuller_smul b f

end model

end FormalODModule

end CerednikDrinfeld

end
