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
`Definitions/Def_MvFormalGroup_CartierModuleBaseChange.lean`
The source is machine-generated proof code built around a proof-extraction
framework; the statements and proofs are reused here with that machinery
removed and the names restated in Mathlib style.
Adaptations copyright (c) Meta Platforms, Inc. and affiliates, under the
license in the root LICENSE file.
-/

module

public import MathlibExt.RingTheory.MvFormalGroup.Cartier.WittAction

/-!
# Base change of Cartier modules

Along a ring homomorphism `f : R →+* S`, a Cartier module of `Φ` maps to one of `Φ.map f`
(`CartierModule.baseChange`), and more generally to one of any `Ψ` with `Φ.map f = Ψ`
(`CartierModule.baseChangeEq`). Base change is functorial, injective along injective ring
homomorphisms (`baseChangeEq_injective`) and compatible with Frobenius, Verschiebung,
homotheties, the Witt-vector action and the tangent map.

## References

* Th. Zink, *Cartiertheorie kommutativer formaler Gruppen*, Teubner-Texte zur Mathematik 68,
  Teubner, Leipzig, 1984.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v w

open MvPowerSeries

namespace MvFormalGroup

variable {p : ℕ} [hp : Fact p.Prime] {d d' : ℕ}
variable {R : Type u} [CommRing R] {S : Type v} [CommRing S] {T : Type w} [CommRing T]

omit hp in
@[simp] theorem toPowerSeries_map_ringHom (F : MvFormalGroup d R) (f : R →+* S) (i : Fin d) :
    (F.map f).toPowerSeries i = MvPowerSeries.map f (F.toPowerSeries i) := rfl

namespace WittLaw

omit hp in
theorem constantCoeff_map_family {σ τ : Type*} {a : σ → MvPowerSeries τ R}
    (ha : ∀ s, (a s).constantCoeff = 0) (f : R →+* S) (s : σ) :
    (MvPowerSeries.map f (a s)).constantCoeff = 0 := by
  rw [constantCoeff_map, ha s, map_zero]

omit hp in
theorem coe_mvPolynomial_map {σ : Type*} (f : R →+* S) (P : MvPolynomial σ R) :
    ((MvPolynomial.map f P : MvPolynomial σ S) : MvPowerSeries σ S) =
      MvPowerSeries.map f (P : MvPowerSeries σ R) := by
  ext n
  rw [MvPolynomial.coeff_coe, MvPolynomial.coeff_map, coeff_map, MvPolynomial.coeff_coe]

theorem map_addFam (f : R →+* S) (n : ℕ) :
    MvPowerSeries.map f (addFam p R n) = addFam p S n := by
  rw [addFam, addFam, ← coe_mvPolynomial_map, MvPolynomial.map_map]
  congr 2
  ext x <;> simp

omit hp in
theorem map_verFam (f : R →+* S) (n : ℕ) :
    MvPowerSeries.map f (verFam R n) = verFam S n := by
  cases n with
  | zero => exact map_zero _
  | succ n => exact map_X f n

omit hp in
theorem map_frobFam (f : R →+* S) (n : ℕ) :
    MvPowerSeries.map f (frobFam p R n) = frobFam p S n := by
  change MvPowerSeries.map f (X n ^ p) = X n ^ p
  rw [map_pow, map_X]

omit hp in
theorem map_teichFam (f : R →+* S) (a : R) (n : ℕ) :
    MvPowerSeries.map f (teichFam p a n) = teichFam p (f a) n := by
  rw [teichFam_apply, teichFam_apply, smul_eq_C_mul, smul_eq_C_mul, map_mul, map_C, map_X, map_pow]

theorem map_mulPoly (f : R →+* S) (w : WittVector p R) (n : ℕ) :
    MvPolynomial.map f (mulPoly p w n) = mulPoly p (WittVector.map f w) n := by
  rw [mulPoly_eq_peval, mulPoly_eq_peval,
    WittVector.map_peval (MvPolynomial.map f) (WittVector.wittMul p n)]
  congr 1
  funext i m
  fin_cases i
  · change MvPolynomial.map f (MvPolynomial.C (w.coeff m)) = MvPolynomial.C
      ((WittVector.map f w).coeff m)
    rw [MvPolynomial.map_C, WittVector.map_coeff]
  · change MvPolynomial.map f (MvPolynomial.X m) = MvPolynomial.X m
    rw [MvPolynomial.map_X]

theorem map_mulFam (f : R →+* S) (w : WittVector p R) (n : ℕ) :
    MvPowerSeries.map f (mulFam p w n) = mulFam p (WittVector.map f w) n := by
  rw [mulFam_apply, mulFam_apply, ← coe_mvPolynomial_map, map_mulPoly]

end WittLaw

namespace CartierModule

open WittLaw

variable {Φ : MvFormalGroup d R} {Φ' : MvFormalGroup d' R}
variable {Ψ : MvFormalGroup d S} {Ψ' : MvFormalGroup d' S}

omit hp in
theorem map_curveFam (f : R →+* S) (n : ℕ) :
    MvPowerSeries.map f (curveFam R n) = curveFam S n := by
  cases n with
  | zero => exact map_X f ()
  | succ n => exact map_zero _

omit hp in
theorem map_blkX (f : R →+* S) (i : Fin 2) :
    (fun m => MvPowerSeries.map f ((fun m => (X (i, m) : MvPowerSeries (Fin 2 × ℕ) R)) m)) =
      fun m => (X (i, m) : MvPowerSeries (Fin 2 × ℕ) S) := by
  funext m
  exact map_X f (i, m)

def baseChangeEqFun (f : R →+* S) (h : Φ.map f = Ψ) (m : CartierModule p Φ) :
    CartierModule p Ψ where
  toPowerSeries := fun j => MvPowerSeries.map f (m.toPowerSeries j)
  constantCoeff_eq_zero := fun j => constantCoeff_map_family m.constantCoeff_eq_zero f j
  subst_eq := by
    intro j
    subst h
    have hm := m.constantCoeff_eq_zero
    have hm' : ∀ l, (MvPowerSeries.map f (m.toPowerSeries l)).constantCoeff = 0 :=
      constantCoeff_map_family hm f
    have key := congrArg (MvPowerSeries.map f) (m.subst_addFam j)
    have hE : HasSubst (Sum.elim (inBlk 0 m.toPowerSeries) (inBlk 1 m.toPowerSeries)) := by
      apply hasSubst_of_constantCoeff_zero
      rintro (l | l)
      · exact constantCoeff_inBlk 0 hm l
      · exact constantCoeff_inBlk 1 hm l
    rw [map_subst (hasSubst_addFam p R), map_subst hE] at key
    have hA : (fun n => MvPowerSeries.map f (addFam p R n)) = addFam p S := funext (map_addFam f)
    rw [hA] at key
    have hblk : ∀ (i : Fin 2) (l : Fin d), MvPowerSeries.map f (inBlk i m.toPowerSeries l) =
        inBlk i (fun l => MvPowerSeries.map f (m.toPowerSeries l)) l := by
      intro i l
      rw [inBlk_apply, inBlk_apply, map_subst (hasSubst_blk i)]
      congr 1
      funext n
      exact map_X f (i, n)
    have hfam : (fun s => MvPowerSeries.map f
        (Sum.elim (inBlk 0 m.toPowerSeries) (inBlk 1 m.toPowerSeries) s)) =
        Sum.elim (inBlk 0 fun l => MvPowerSeries.map f (m.toPowerSeries l))
          (inBlk 1 fun l => MvPowerSeries.map f (m.toPowerSeries l)) := by
      funext s
      rcases s with l | l
      · exact hblk 0 l
      · exact hblk 1 l
    rw [hfam] at key
    exact key

@[simp] theorem toPowerSeries_baseChangeEqFun (f : R →+* S) (h : Φ.map f = Ψ)
    (m : CartierModule p Φ)
    (j : Fin d) : (baseChangeEqFun f h m).toPowerSeries j = MvPowerSeries.map f
        (m.toPowerSeries j) :=
  rfl

theorem map_sumElim (f : R →+* S) {σ : Type*} (a b : Fin d → MvPowerSeries σ R) :
    (fun s => MvPowerSeries.map f (Sum.elim a b s)) =
      Sum.elim (fun l => MvPowerSeries.map f (a l)) fun l => MvPowerSeries.map f (b l) := by
  funext s
  rcases s with l | l <;> rfl

def baseChangeEq [Φ.IsComm] [Ψ.IsComm] (f : R →+* S) (h : Φ.map f = Ψ) :
    CartierModule p Φ →+ CartierModule p Ψ where
  toFun := baseChangeEqFun f h
  map_zero' := CartierModule.ext (funext fun j => by
    change MvPowerSeries.map f 0 = 0
    exact map_zero _)
  map_add' m m' := CartierModule.ext (funext fun j => by
    change MvPowerSeries.map f
        (subst (Sum.elim m.toPowerSeries m'.toPowerSeries) (Φ.toPowerSeries j)) =
      subst (Sum.elim (fun l => MvPowerSeries.map f (m.toPowerSeries l))
        fun l => MvPowerSeries.map f (m'.toPowerSeries l)) (Ψ.toPowerSeries j)
    have hS : HasSubst (Sum.elim m.toPowerSeries m'.toPowerSeries) := by
      apply hasSubst_of_constantCoeff_zero
      rintro (l | l)
      · exact m.constantCoeff_eq_zero l
      · exact m'.constantCoeff_eq_zero l
    rw [map_subst hS, map_sumElim, ← h]
    rfl)

@[simp] theorem toPowerSeries_baseChangeEq [Φ.IsComm] [Ψ.IsComm] (f : R →+* S) (h : Φ.map f = Ψ)
    (m : CartierModule p Φ) (j : Fin d) :
    (baseChangeEq f h m).toPowerSeries j = MvPowerSeries.map f (m.toPowerSeries j) :=
  rfl

theorem baseChangeEq_apply [Φ.IsComm] [Ψ.IsComm] (f : R →+* S) (h : Φ.map f = Ψ)
    (m : CartierModule p Φ) : baseChangeEq f h m = baseChangeEqFun f h m := rfl

abbrev baseChange [Φ.IsComm] (f : R →+* S) : CartierModule p Φ →+ CartierModule p (Φ.map f) :=
  baseChangeEq f rfl

theorem baseChangeEq_id [Φ.IsComm] (h : Φ.map (RingHom.id R) = Φ) (m : CartierModule p Φ) :
    baseChangeEq (RingHom.id R) h m = m :=
  CartierModule.ext (funext fun j => by
    change MvPowerSeries.map (RingHom.id R) (m.toPowerSeries j) = _
    rw [MvPowerSeries.map_id]
    rfl)

theorem baseChangeEq_baseChangeEq [Φ.IsComm] [Ψ.IsComm] {Χ : MvFormalGroup d T} [Χ.IsComm]
    (f : R →+* S) (g : S →+* T) (h : Φ.map f = Ψ) (h' : Ψ.map g = Χ) (h'' : Φ.map (g.comp f) = Χ)
    (m : CartierModule p Φ) :
    baseChangeEq g h' (baseChangeEq f h m) = baseChangeEq (g.comp f) h'' m :=
  CartierModule.ext (funext fun j => by
    change MvPowerSeries.map g (MvPowerSeries.map f (m.toPowerSeries j)) =
      MvPowerSeries.map (g.comp f) (m.toPowerSeries j)
    rw [MvPowerSeries.map_comp]
    rfl)

theorem toPowerSeries_baseChangeEq_eq [Φ.IsComm] [Ψ.IsComm] {Ψ₁ : MvFormalGroup d S} [Ψ₁.IsComm]
    (f : R →+* S) (h : Φ.map f = Ψ) (h₁ : Φ.map f = Ψ₁) (m : CartierModule p Φ) :
    (baseChangeEq f h m).toPowerSeries = (baseChangeEq f h₁ m).toPowerSeries := rfl

theorem baseChangeEq_injective [Φ.IsComm] [Ψ.IsComm] (f : R →+* S) (h : Φ.map f = Ψ)
    (hf : Function.Injective f) : Function.Injective (baseChangeEq (p := p) f h) := by
  intro m m' hmm
  refine CartierModule.ext (funext fun j => ?_)
  have hj := congrArg (fun x : CartierModule p Ψ => x.toPowerSeries j) hmm
  simp only [toPowerSeries_baseChangeEq] at hj
  ext e
  apply hf
  rw [← coeff_map, ← coeff_map, hj]

theorem baseChangeEq_precomp [Φ.IsComm] [Ψ.IsComm] (f : R →+* S) (h : Φ.map f = Ψ)
    {u : ℕ → MvPowerSeries ℕ R} {u' : ℕ → MvPowerSeries ℕ S} (hu : IsEndo p u) (hu' : IsEndo p u')
    (huu' : ∀ n, MvPowerSeries.map f (u n) = u' n) (m : CartierModule p Φ) :
    baseChangeEq f h (precomp hu m) = precomp hu' (baseChangeEq f h m) :=
  CartierModule.ext (funext fun j => by
    change MvPowerSeries.map f (subst u (m.toPowerSeries j)) =
      subst u' (MvPowerSeries.map f (m.toPowerSeries j))
    rw [map_subst hu.hasSubst]
    congr 1
    exact funext huu')

theorem baseChangeEq_frobenius [Φ.IsComm] [Ψ.IsComm] (f : R →+* S) (h : Φ.map f = Ψ)
    (m : CartierModule p Φ) :
    baseChangeEq f h (frobenius m) = frobenius (baseChangeEq f h m) :=
  baseChangeEq_precomp f h isEndo_verFam isEndo_verFam (map_verFam f) m

theorem baseChangeEq_verschiebung [Φ.IsComm] [Ψ.IsComm] [CharP R p] [CharP S p] (f : R →+* S)
    (h : Φ.map f = Ψ) (m : CartierModule p Φ) :
    baseChangeEq f h (verschiebung m) = verschiebung (baseChangeEq f h m) :=
  baseChangeEq_precomp f h isEndo_frobFam isEndo_frobFam (map_frobFam f) m

theorem baseChangeEq_verschiebung_iterate [Φ.IsComm] [Ψ.IsComm] [CharP R p] [CharP S p]
    (f : R →+* S) (h : Φ.map f = Ψ) (n : ℕ) (m : CartierModule p Φ) :
    baseChangeEq f h ((⇑(verschiebung (p := p) (Φ := Φ)))^[n] m) =
      (⇑(verschiebung (p := p) (Φ := Ψ)))^[n] (baseChangeEq f h m) := by
  induction n generalizing m with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply, ← baseChangeEq_verschiebung, ih]

theorem baseChangeEq_frobenius_iterate [Φ.IsComm] [Ψ.IsComm]
    (f : R →+* S) (h : Φ.map f = Ψ) (n : ℕ) (m : CartierModule p Φ) :
    baseChangeEq f h ((⇑(frobenius (p := p) (Φ := Φ)))^[n] m) =
      (⇑(frobenius (p := p) (Φ := Ψ)))^[n] (baseChangeEq f h m) := by
  induction n generalizing m with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply, ← baseChangeEq_frobenius, ih]

theorem baseChangeEq_homothety [Φ.IsComm] [Ψ.IsComm] (f : R →+* S) (h : Φ.map f = Ψ) (a : R)
    (m : CartierModule p Φ) :
    baseChangeEq f h (homothety a m) = homothety (f a) (baseChangeEq f h m) :=
  baseChangeEq_precomp f h (isEndo_teichFam a) (isEndo_teichFam (f a)) (map_teichFam f a) m

theorem baseChangeEq_smul_witt [Φ.IsComm] [Ψ.IsComm] (f : R →+* S) (h : Φ.map f = Ψ)
    (w : WittVector p R) (m : CartierModule p Φ) :
    baseChangeEq f h (w • m) = (WittVector.map f w) • (baseChangeEq f h m) := by
  rw [smul_eq_precomp, smul_eq_precomp]
  exact baseChangeEq_precomp f h (isEndo_mulFam w) (isEndo_mulFam _) (map_mulFam f w) m

theorem baseChangeEq_nsmul [Φ.IsComm] [Ψ.IsComm] (f : R →+* S) (h : Φ.map f = Ψ) (n : ℕ)
    (m : CartierModule p Φ) : baseChangeEq f h (n • m) = n • baseChangeEq f h m :=
  map_nsmul _ _ _

theorem baseChangeEq_map [Φ.IsComm] [Ψ.IsComm] [Φ'.IsComm] [Ψ'.IsComm] (f : R →+* S)
    (h : Φ.map f = Ψ) (h' : Φ'.map f = Ψ') {φ : Φ.Hom Φ'} {ψ : Ψ.Hom Ψ'}
    (hφψ : ∀ i, ψ.toPowerSeries i = MvPowerSeries.map f (φ.toPowerSeries i))
        (m : CartierModule p Φ) :
    baseChangeEq f h' (map φ m) = map ψ (baseChangeEq f h m) :=
  CartierModule.ext (funext fun i => by
    change MvPowerSeries.map f (subst m.toPowerSeries (φ.toPowerSeries i)) =
      subst (fun l => MvPowerSeries.map f (m.toPowerSeries l)) (ψ.toPowerSeries i)
    rw [map_subst m.hasSubst_toPowerSeries, hφψ i])

theorem baseChangeEq_endAct [Φ.IsComm] [Ψ.IsComm] (f : R →+* S) (h : Φ.map f = Ψ)
    {φ : MvFormalGroup.End Φ} {ψ : MvFormalGroup.End Ψ}
    (hφψ : ∀ i, ψ.toPowerSeries i = MvPowerSeries.map f (φ.toPowerSeries i))
        (m : CartierModule p Φ) :
    baseChangeEq f h (endAct φ m) = endAct ψ (baseChangeEq f h m) :=
  baseChangeEq_map f h h hφψ m

theorem tangent_baseChangeEq [Φ.IsComm] [Ψ.IsComm] (f : R →+* S) (h : Φ.map f = Ψ)
    (m : CartierModule p Φ) : tangent (baseChangeEq f h m) = fun j => f (tangent m j) := by
  funext j
  change coeff (Finsupp.single 0 1) (MvPowerSeries.map f (m.toPowerSeries j)) =
    f (coeff (Finsupp.single 0 1) (m.toPowerSeries j))
  rw [coeff_map]

theorem curve_baseChangeEq [Φ.IsComm] [Ψ.IsComm] (f : R →+* S) (h : Φ.map f = Ψ)
    (m : CartierModule p Φ) (j : Fin d) :
    curve (baseChangeEq f h m) j = PowerSeries.map f (curve m j) := by
  rw [curve_apply, curve_apply]
  change subst (curveFam S) (MvPowerSeries.map f (m.toPowerSeries j)) =
    MvPowerSeries.map f (subst (curveFam R) (m.toPowerSeries j))
  rw [map_subst hasSubst_curveFam]
  congr 1
  funext n
  exact (map_curveFam f n).symm

namespace Examples

theorem baseChange_addLinear (f : R →+* S) (v : Fin d → R)
    (h : (addMv d R).map f = addMv d S) :
    baseChangeEq f h (addLinear p v) = addLinear p (fun j => f (v j)) := by
  refine CartierModule.ext (funext fun j => ?_)
  change MvPowerSeries.map f (v j • (X 0 : MvPowerSeries ℕ R)) = f (v j) • (X 0 : MvPowerSeries ℕ S)
  rw [smul_eq_C_mul, smul_eq_C_mul, map_mul, map_C, map_X]

end Examples

end CartierModule

end MvFormalGroup

end
