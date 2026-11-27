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
`Definitions/Def_MvFormalGroup_CartierModule.lean`
The source is machine-generated proof code built around a proof-extraction
framework; the statements and proofs are reused here with that machinery
removed and the names restated in Mathlib style.
Adaptations copyright (c) Meta Platforms, Inc. and affiliates, under the
license in the root LICENSE file.
-/

module

public import Mathlib.RingTheory.PowerSeries.Expand
public import MathlibExt.RingTheory.MvFormalGroup.Cartier.Basic

/-!
# Operators on Cartier modules

Precomposition with an endomorphism of the Witt law (`CartierModule.precomp`) gives the Frobenius
`CartierModule.frobenius` and, over a ring of characteristic `p`, the Verschiebung
`CartierModule.verschiebung`, with `frobenius_verschiebung_eq_nsmul`. Homomorphisms of formal
groups act by `CartierModule.map`, and `CartierModule.endAct` is the ring homomorphism from
`MvFormalGroup.End Φ` to the additive endomorphisms. The tangent map `CartierModule.tangent`
and the associated curve `CartierModule.curve` connect Cartier modules with the Lie algebra.

## References

* Th. Zink, *Cartiertheorie kommutativer formaler Gruppen*, Teubner-Texte zur Mathematik 68,
  Teubner, Leipzig, 1984.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u

namespace MvFormalGroup

open MvPowerSeries WittLaw

variable {p : ℕ} [hp : Fact p.Prime] {d d' d'' : ℕ} {R : Type u} [CommRing R]

namespace CartierModule

variable {Φ : MvFormalGroup d R} {Φ' : MvFormalGroup d' R} {Φ'' : MvFormalGroup d'' R}

def precompFun {u : ℕ → MvPowerSeries ℕ R} (hu : WittLaw.IsEndo p u) (f : CartierModule p Φ) :
    CartierModule p Φ where
  toPowerSeries := fun j => subst u (f.toPowerSeries j)
  constantCoeff_eq_zero := fun j =>
    constantCoeff_subst_eq_zero hu.hasSubst hu.constantCoeff (f.constantCoeff_eq_zero j)
  subst_eq := by
    intro j
    have hf := f.constantCoeff_eq_zero
    have hA := hasSubst_addFam p R
    have hP := hasSubst_pairFam hu.hasSubst hu.constantCoeff
    change subst (WittLaw.addFam p R) (subst u (f.toPowerSeries j)) =
      subst (Sum.elim (inBlk 0 fun l => subst u (f.toPowerSeries l))
        (inBlk 1 fun l => subst u (f.toPowerSeries l))) (Φ.toPowerSeries j)
    rw [subst_comp_subst_apply hu.hasSubst hA]
    have hfam : (fun n => subst (WittLaw.addFam p R) (u n)) =
        fun n => subst (WittLaw.pairFam u) (WittLaw.addFam p R n) := funext hu.subst_addFam
    rw [hfam, ← subst_comp_subst_apply hA hP, f.subst_addFam, subst_subst_elim Φ
      (constantCoeff_inBlk 0 hf) (constantCoeff_inBlk 1 hf) hP]
    congr 1
    funext s
    rcases s with l | l
    · exact WittLaw.subst_pairFam_subst_blk hu.hasSubst hu.constantCoeff 0 (f.toPowerSeries l)
    · exact WittLaw.subst_pairFam_subst_blk hu.hasSubst hu.constantCoeff 1 (f.toPowerSeries l)

@[simp] theorem toPowerSeries_precompFun {u : ℕ → MvPowerSeries ℕ R} (hu : WittLaw.IsEndo p u)
    (f : CartierModule p Φ) :
    (precompFun hu f).toPowerSeries = fun j => subst u (f.toPowerSeries j) := rfl

def precomp [Φ.IsComm] {u : ℕ → MvPowerSeries ℕ R} (hu : WittLaw.IsEndo p u) :
    CartierModule p Φ →+ CartierModule p Φ where
  toFun := precompFun hu
  map_zero' := CartierModule.ext (funext fun j => by
    change subst u (0 : MvPowerSeries ℕ R) = 0
    rw [← coe_substAlgHom hu.hasSubst, map_zero])
  map_add' f g := CartierModule.ext (funext fun j =>
    subst_subst_elim Φ f.constantCoeff_eq_zero g.constantCoeff_eq_zero hu.hasSubst j)

@[simp] theorem toPowerSeries_precomp [Φ.IsComm] {u : ℕ → MvPowerSeries ℕ R}
    (hu : WittLaw.IsEndo p u) (f : CartierModule p Φ) :
    (precomp hu f).toPowerSeries = fun j => subst u (f.toPowerSeries j) := rfl

theorem precomp_precomp [Φ.IsComm] {u v : ℕ → MvPowerSeries ℕ R} (hu : WittLaw.IsEndo p u)
    (hv : WittLaw.IsEndo p v) (f : CartierModule p Φ) (j : Fin d) :
    (precomp hv (precomp hu f)).toPowerSeries j = subst (fun n => subst v (u n))
        (f.toPowerSeries j) := by
  change subst v (subst u (f.toPowerSeries j)) = _
  rw [subst_comp_subst_apply hu.hasSubst hv.hasSubst]

/-- **Frobenius of a Cartier module.** For a commutative formal group law `Φ` over a commutative
ring, the Frobenius `F` precomposes each point of the Cartier module with the Witt vector
Verschiebung, the substitution `X 0 ↦ 0`, `X (n + 1) ↦ X n`. -/
def frobenius [Φ.IsComm] : CartierModule p Φ →+ CartierModule p Φ :=
  precomp WittLaw.isEndo_verFam

@[simp] theorem toPowerSeries_frobenius [Φ.IsComm] (f : CartierModule p Φ) :
    (frobenius f).toPowerSeries = fun j => subst (WittLaw.verFam R) (f.toPowerSeries j) := rfl

/-- **Verschiebung of a Cartier module.** For a commutative formal group law `Φ` over a
commutative ring of characteristic `p`, the Verschiebung `V` precomposes each point of the
Cartier module with the Witt vector Frobenius, the substitution `X n ↦ X n ^ p`. It satisfies
`F (V x) = p • x`. -/
def verschiebung [Φ.IsComm] [CharP R p] : CartierModule p Φ →+ CartierModule p Φ :=
  precomp WittLaw.isEndo_frobFam

@[simp] theorem toPowerSeries_verschiebung [Φ.IsComm] [CharP R p] (f : CartierModule p Φ) :
    (verschiebung f).toPowerSeries = fun j => subst (WittLaw.frobFam p R) (f.toPowerSeries j) := rfl

theorem toPowerSeries_verschiebung_eq_expand [Φ.IsComm] [CharP R p] (f : CartierModule p Φ)
    (j : Fin d) :
    (verschiebung f).toPowerSeries j = MvPowerSeries.expand p hp.out.ne_zero (f.toPowerSeries j) :=
  WittLaw.subst_frobFam _

theorem frobenius_verschiebung [Φ.IsComm] [CharP R p] (f : CartierModule p Φ) :
    frobenius (verschiebung f) = verschiebung (frobenius f) := by
  apply CartierModule.ext
  funext j
  rw [frobenius, verschiebung, precomp_precomp, precomp_precomp]
  congr 1
  funext n
  cases n with
  | zero =>
    change subst (WittLaw.verFam R) (X 0 ^ p : MvPowerSeries ℕ R) =
      subst (WittLaw.frobFam p R) (0 : MvPowerSeries ℕ R)
    rw [subst_pow WittLaw.hasSubst_verFam, subst_X WittLaw.hasSubst_verFam,
      ← coe_substAlgHom WittLaw.hasSubst_frobFam, map_zero, WittLaw.verFam_zero,
      zero_pow hp.out.ne_zero]
  | succ m =>
    change subst (WittLaw.verFam R) (X (m + 1) ^ p : MvPowerSeries ℕ R) =
      subst (WittLaw.frobFam p R) (X m : MvPowerSeries ℕ R)
    rw [subst_pow WittLaw.hasSubst_verFam, subst_X WittLaw.hasSubst_verFam,
      subst_X WittLaw.hasSubst_frobFam, WittLaw.verFam_succ, WittLaw.frobFam_apply]

theorem verschiebung_injective [Φ.IsComm] [CharP R p] :
    Function.Injective (verschiebung : CartierModule p Φ → CartierModule p Φ) := by
  intro f g h
  apply CartierModule.ext
  funext j
  ext m
  have hj := congrArg (fun k : CartierModule p Φ => coeff (p • m) (k.toPowerSeries j)) h
  simpa only [toPowerSeries_verschiebung_eq_expand, MvPowerSeries.coeff_expand_smul] using hj

theorem _root_.MvFormalGroup.Hom.subst_subst_elim {τ : Type*} {F : MvFormalGroup d R}
    {G : MvFormalGroup d' R} (φ : F.Hom G) {a b : Fin d → MvPowerSeries τ R}
    (ha : ∀ j, (a j).constantCoeff = 0) (hb : ∀ j, (b j).constantCoeff = 0) (i : Fin d') :
    subst (fun j => subst (Sum.elim a b) (F.toPowerSeries j)) (φ.toPowerSeries i) =
      subst (Sum.elim (fun j => subst a (φ.toPowerSeries j)) fun j => subst b (φ.toPowerSeries j))
        (G.toPowerSeries i) := by
  have hab : HasSubst (Sum.elim a b) := hasSubst_elim ha hb
  have hXl : HasSubst (fun l : Fin d => (X (Sum.inl l) : MvPowerSeries (Fin d ⊕ Fin d) R)) :=
    hasSubst_of_constantCoeff_zero fun l => constantCoeff_X _
  have hXr : HasSubst (fun l : Fin d => (X (Sum.inr l) : MvPowerSeries (Fin d ⊕ Fin d) R)) :=
    hasSubst_of_constantCoeff_zero fun l => constantCoeff_X _
  have hLR : HasSubst (Sum.elim
      (fun j => subst (fun l => (X (Sum.inl l) : MvPowerSeries (Fin d ⊕ Fin d) R))
        (φ.toPowerSeries j))
      fun j => subst (fun l => (X (Sum.inr l) : MvPowerSeries (Fin d ⊕ Fin d) R))
        (φ.toPowerSeries j)) :=
    hasSubst_elim
      (fun j => constantCoeff_subst_eq_zero hXl (fun l => constantCoeff_X _)
        (φ.constantCoeff_eq_zero j))
      fun j => constantCoeff_subst_eq_zero hXr (fun l => constantCoeff_X _)
        (φ.constantCoeff_eq_zero j)
  have key := congrArg (subst (Sum.elim a b)) (φ.subst_eq i)
  rw [subst_comp_subst_apply F.hasSubst_toPowerSeries hab, subst_comp_subst_apply hLR hab] at key
  rw [key]
  congr 1
  funext s
  rcases s with j | j
  · change subst (Sum.elim a b) (subst (fun l => (X (Sum.inl l) : MvPowerSeries (Fin d ⊕ Fin d) R))
        (φ.toPowerSeries j)) = subst a (φ.toPowerSeries j)
    rw [subst_comp_subst_apply hXl hab]
    congr 1
    funext l
    exact subst_X hab (Sum.inl l)
  · change subst (Sum.elim a b) (subst (fun l => (X (Sum.inr l) : MvPowerSeries (Fin d ⊕ Fin d) R))
        (φ.toPowerSeries j)) = subst b (φ.toPowerSeries j)
    rw [subst_comp_subst_apply hXr hab]
    congr 1
    funext l
    exact subst_X hab (Sum.inr l)

def mapFun (φ : Φ.Hom Φ') (f : CartierModule p Φ) : CartierModule p Φ' where
  toPowerSeries := fun i => subst f.toPowerSeries (φ.toPowerSeries i)
  constantCoeff_eq_zero := fun i =>
    constantCoeff_subst_eq_zero f.hasSubst_toPowerSeries f.constantCoeff_eq_zero
      (φ.constantCoeff_eq_zero i)
  subst_eq := by
    intro i
    have hf := f.constantCoeff_eq_zero
    change subst (WittLaw.addFam p R) (subst f.toPowerSeries (φ.toPowerSeries i)) =
      subst (Sum.elim (inBlk 0 fun l => subst f.toPowerSeries (φ.toPowerSeries l))
        (inBlk 1 fun l => subst f.toPowerSeries (φ.toPowerSeries l))) (Φ'.toPowerSeries i)
    rw [subst_comp_subst_apply f.hasSubst_toPowerSeries (hasSubst_addFam p R)]
    have hfam : (fun l => subst (WittLaw.addFam p R) (f.toPowerSeries l)) =
        fun l => subst (Sum.elim (inBlk 0 f.toPowerSeries) (inBlk 1 f.toPowerSeries))
          (Φ.toPowerSeries l) := funext f.subst_addFam
    rw [hfam, φ.subst_subst_elim (constantCoeff_inBlk 0 hf) (constantCoeff_inBlk 1 hf) i]
    congr 1
    funext s
    rcases s with l | l
    · change subst (inBlk 0 f.toPowerSeries) (φ.toPowerSeries l) =
        subst (blk 0) (subst f.toPowerSeries (φ.toPowerSeries l))
      rw [subst_comp_subst_apply f.hasSubst_toPowerSeries (hasSubst_blk 0)]
      rfl
    · change subst (inBlk 1 f.toPowerSeries) (φ.toPowerSeries l) =
        subst (blk 1) (subst f.toPowerSeries (φ.toPowerSeries l))
      rw [subst_comp_subst_apply f.hasSubst_toPowerSeries (hasSubst_blk 1)]
      rfl

@[simp] theorem toPowerSeries_mapFun (φ : Φ.Hom Φ') (f : CartierModule p Φ) :
    (mapFun φ f).toPowerSeries = fun i => subst f.toPowerSeries (φ.toPowerSeries i) := rfl

def map [Φ.IsComm] [Φ'.IsComm] (φ : Φ.Hom Φ') : CartierModule p Φ →+ CartierModule p Φ' where
  toFun := mapFun φ
  map_zero' := CartierModule.ext (funext fun i =>
    subst_zero_of_constantCoeff_eq_zero (φ.constantCoeff_eq_zero i))
  map_add' f g := CartierModule.ext (funext fun i =>
    φ.subst_subst_elim f.constantCoeff_eq_zero g.constantCoeff_eq_zero i)

@[simp] theorem toPowerSeries_map [Φ.IsComm] [Φ'.IsComm] (φ : Φ.Hom Φ') (f : CartierModule p Φ) :
    (map φ f).toPowerSeries = fun i => subst f.toPowerSeries (φ.toPowerSeries i) := rfl

theorem map_id [Φ.IsComm] (f : CartierModule p Φ) : map (MvFormalGroup.Hom.id Φ) f = f :=
  CartierModule.ext (funext fun i => subst_X f.hasSubst_toPowerSeries i)

theorem map_comp [Φ.IsComm] [Φ'.IsComm] [Φ''.IsComm] (ψ : Φ'.Hom Φ'') (φ : Φ.Hom Φ')
    (f : CartierModule p Φ) : map (ψ.comp φ) f = map ψ (map φ f) :=
  CartierModule.ext (funext fun i =>
    subst_comp_subst_apply φ.hasSubst_toPowerSeries f.hasSubst_toPowerSeries (ψ.toPowerSeries i))

theorem map_add_hom [Φ.IsComm] [Φ'.IsComm] (φ ψ : Φ.Hom Φ') (f : CartierModule p Φ) :
    map (φ + ψ) f = map φ f + map ψ f :=
  CartierModule.ext (funext fun i =>
    subst_subst_elim Φ' φ.constantCoeff_eq_zero ψ.constantCoeff_eq_zero f.hasSubst_toPowerSeries i)

theorem map_zero_hom [Φ.IsComm] [Φ'.IsComm] (f : CartierModule p Φ) :
    map (0 : Φ.Hom Φ') f = 0 :=
  CartierModule.ext (funext fun i => by
    change subst f.toPowerSeries (0 : MvPowerSeries (Fin d) R) = 0
    rw [← coe_substAlgHom f.hasSubst_toPowerSeries, map_zero])

theorem map_precomp [Φ.IsComm] [Φ'.IsComm] (φ : Φ.Hom Φ') {u : ℕ → MvPowerSeries ℕ R}
    (hu : WittLaw.IsEndo p u) (f : CartierModule p Φ) :
    map φ (precomp hu f) = precomp hu (map φ f) :=
  CartierModule.ext (funext fun i =>
    (subst_comp_subst_apply f.hasSubst_toPowerSeries hu.hasSubst (φ.toPowerSeries i)).symm)

theorem map_frobenius [Φ.IsComm] [Φ'.IsComm] (φ : Φ.Hom Φ') (f : CartierModule p Φ) :
    map φ (frobenius f) = frobenius (map φ f) :=
  map_precomp φ _ f

theorem map_verschiebung [Φ.IsComm] [Φ'.IsComm] [CharP R p] (φ : Φ.Hom Φ')
    (f : CartierModule p Φ) : map φ (verschiebung f) = verschiebung (map φ f) :=
  map_precomp φ _ f

def endAct [Φ.IsComm] : MvFormalGroup.End Φ →+* AddMonoid.End (CartierModule p Φ) where
  toFun φ := map φ
  map_one' := AddMonoidHom.ext map_id
  map_mul' φ ψ := AddMonoidHom.ext (map_comp φ ψ)
  map_zero' := AddMonoidHom.ext map_zero_hom
  map_add' φ ψ := AddMonoidHom.ext (map_add_hom φ ψ)

@[simp] theorem endAct_apply [Φ.IsComm] (φ : MvFormalGroup.End Φ) (f : CartierModule p Φ) :
    endAct φ f = map φ f := rfl

theorem endAct_frobenius [Φ.IsComm] (φ : MvFormalGroup.End Φ) (f : CartierModule p Φ) :
    endAct φ (frobenius f) = frobenius (endAct φ f) :=
  map_frobenius φ f

theorem endAct_verschiebung [Φ.IsComm] [CharP R p] (φ : MvFormalGroup.End Φ)
    (f : CartierModule p Φ) : endAct φ (verschiebung f) = verschiebung (endAct φ f) :=
  map_verschiebung φ f

theorem endAct_natCast [Φ.IsComm] (n : ℕ) (f : CartierModule p Φ) :
    endAct (n : MvFormalGroup.End Φ) f = n • f := by
  rw [map_natCast]; rfl

end CartierModule

namespace WittLaw

def nsmulFam (p : ℕ) [Fact p.Prime] (R : Type u) [CommRing R] (n : ℕ) : ℕ → MvPowerSeries ℕ R :=
  fun k => ((MvPolynomial.map (Int.castRingHom R)
    (MvPolynomial.rename Prod.snd (WittVector.wittNSMul p n k)) : MvPolynomial ℕ R) :
      MvPowerSeries ℕ R)

theorem isWeightedHomogeneous_wittNSMul (n k : ℕ) :
    MvPolynomial.IsWeightedHomogeneous (weight p fun _ : Fin 1 => 1) (WittVector.wittNSMul p n k)
      (p ^ k) := by
  have h := isWeightedHomogeneous_wittStructureInt p (fun _ : Fin 1 => 1)
    (n • MvPolynomial.X (0 : Fin 1) : MvPolynomial (Fin 1) ℤ) 1
    (fun m => by
      rw
          [map_nsmul, MvPolynomial.bind₁_X_right, one_mul, nsmul_eq_mul, ← map_natCast
              MvPolynomial.C]
      have h0 := isWeightedHomogeneous_rename_wittPolynomial p (fun _ : Fin 1 => 1) 0 m
      rw [one_mul] at h0
      exact h0.C_mul _) k
  rwa [one_mul] at h

theorem constantCoeff_nsmulFam (n k : ℕ) : (nsmulFam p R n k).constantCoeff = 0 := by
  rw [nsmulFam, ← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, MvPolynomial.coeff_coe,
    MvPolynomial.coeff_map, ← MvPolynomial.constantCoeff_eq, MvPolynomial.constantCoeff_rename,
    WittVector.constantCoeff_wittNSMul, map_zero]

theorem weight_eq_of_coeff_nsmulFam_ne_zero {n k : ℕ} {e : ℕ →₀ ℕ}
    (h : coeff e (nsmulFam p R n k) ≠ 0) : Finsupp.weight (fun m => p ^ m) e = p ^ k := by
  classical
  rw [nsmulFam, MvPolynomial.coeff_coe, MvPolynomial.coeff_map] at h
  have h' : (MvPolynomial.rename Prod.snd (WittVector.wittNSMul p n k)).coeff e ≠ 0 :=
    fun h0 => h (by rw [h0, map_zero])
  obtain ⟨x, hx, hne⟩ := MvPolynomial.coeff_rename_ne_zero _ _ _ h'
  have hw := isWeightedHomogeneous_wittNSMul (p := p) n k hne
  rw [← hx, ← hw, Finsupp.weight_apply, Finsupp.weight_apply,
    Finsupp.sum_mapDomain_index (h := fun i c => c • p ^ i) (fun _ => zero_smul ℕ _)
      (fun _ _ _ => add_smul _ _ _)]
  refine Finsupp.sum_congr fun im _ => ?_
  simp [weight]

theorem hasSubst_nsmulFam (n : ℕ) : HasSubst (nsmulFam p R n) := by
  refine ⟨fun k => by rw [constantCoeff_nsmulFam]; exact IsNilpotent.zero, fun e => ?_⟩
  refine (Set.finite_lt_nat (Finsupp.weight (fun m => p ^ m) e)).subset fun k hk => ?_
  have hw := weight_eq_of_coeff_nsmulFam_ne_zero (p := p) (R := R) hk
  change k < Finsupp.weight (fun m => p ^ m) e
  rw [hw]
  exact Nat.lt_pow_self hp.out.one_lt

omit hp in
private theorem peval_tautological (φ : MvPolynomial (Fin 1 × ℕ) ℤ) :
    WittVector.peval φ ![(WittVector.mk p fun m => (MvPolynomial.X (0, m) :
      MvPolynomial (Fin 1 × ℕ) ℤ)).coeff] = φ := by
  have hid : Function.uncurry ![(WittVector.mk p fun m => (MvPolynomial.X (0, m) :
      MvPolynomial (Fin 1 × ℕ) ℤ)).coeff] = (MvPolynomial.X : Fin 1 × ℕ → _) := by
    funext ⟨i, m⟩
    fin_cases i; rfl
  change MvPolynomial.aeval _ φ = φ
  rw [hid, MvPolynomial.aeval_X_left_apply]

theorem wittNSMul_zero (k : ℕ) : WittVector.wittNSMul p 0 k = 0 := by
  let x : WittVector p (MvPolynomial (Fin 1 × ℕ) ℤ) := WittVector.mk p fun m => MvPolynomial.X
      (0, m)
  have h := WittVector.nsmul_coeff 0 x k
  rw [zero_nsmul, WittVector.zero_coeff, peval_tautological] at h
  exact h.symm

theorem aeval_wittNSMul_wittAdd (n k : ℕ) :
    MvPolynomial.aeval (fun im : Fin 2 × ℕ =>
        (Fin.cases (WittVector.wittNSMul p n im.2) (fun _ => MvPolynomial.X (0, im.2)) im.1 :
          MvPolynomial (Fin 1 × ℕ) ℤ)) (WittVector.wittAdd p k) =
      WittVector.wittNSMul p (n + 1) k := by
  let x : WittVector p (MvPolynomial (Fin 1 × ℕ) ℤ) := WittVector.mk p fun m => MvPolynomial.X
      (0, m)
  have h := WittVector.nsmul_coeff (n + 1) x k
  rw [peval_tautological, succ_nsmul, WittVector.add_coeff] at h
  have hval : (fun im : Fin 2 × ℕ =>
      (Fin.cases (WittVector.wittNSMul p n im.2) (fun _ => MvPolynomial.X (0, im.2)) im.1 :
        MvPolynomial (Fin 1 × ℕ) ℤ)) = Function.uncurry ![(n • x).coeff, x.coeff] := by
    funext ⟨i, m⟩
    refine Fin.cases ?_ (fun l => ?_) i
    · change WittVector.wittNSMul p n m = (n • x).coeff m
      rw [WittVector.nsmul_coeff, peval_tautological]
    · fin_cases l; rfl
  rw [hval]
  exact h

private theorem aeval_X_eq_map {σ : Type*} (S : Type*) [CommRing S] (φ : MvPolynomial σ ℤ) :
    MvPolynomial.aeval (MvPolynomial.X : σ → MvPolynomial σ S) φ =
      MvPolynomial.map (Int.castRingHom S) φ := by
  refine RingHom.congr_fun (?_ :
    (MvPolynomial.aeval (MvPolynomial.X : σ → MvPolynomial σ S)).toRingHom =
      MvPolynomial.map (Int.castRingHom S)) φ
  refine MvPolynomial.ringHom_ext (fun r => ?_) (fun i => ?_)
  · exact RingHom.congr_fun (RingHom.ext_int
      ((MvPolynomial.aeval (MvPolynomial.X : σ → MvPolynomial σ S)).toRingHom.comp
        (MvPolynomial.C : ℤ →+* MvPolynomial σ ℤ))
      ((MvPolynomial.map (Int.castRingHom S)).comp (MvPolynomial.C : ℤ →+* MvPolynomial σ ℤ))) r
  · simp

theorem map_wittNSMul_self (k : ℕ) :
    MvPolynomial.map (Int.castRingHom (ZMod p)) (WittVector.wittNSMul p p k) =
      Nat.casesOn k 0 fun m => MvPolynomial.X (0, m) ^ p := by
  let A := MvPolynomial (Fin 1 × ℕ) (ZMod p)
  let x : WittVector p A := WittVector.mk p fun m => MvPolynomial.X (0, m)
  have h := WittVector.nsmul_coeff p x k
  have hid : Function.uncurry ![x.coeff] = (MvPolynomial.X : Fin 1 × ℕ → A) := by
    funext ⟨i, m⟩
    fin_cases i; rfl
  have hev : WittVector.peval (WittVector.wittNSMul p p k) ![x.coeff] =
      MvPolynomial.map (Int.castRingHom (ZMod p)) (WittVector.wittNSMul p p k) := by
    change MvPolynomial.aeval _ _ = _
    rw [hid]
    exact aeval_X_eq_map (ZMod p) _
  rw [← hev, ← h, nsmul_eq_mul, mul_comm]
  cases k with
  | zero => exact WittVector.mul_charP_coeff_zero x
  | succ m => exact WittVector.mul_charP_coeff_succ x m

omit hp in
theorem hasSubst_finCases {τ : Type*} {u₀ u₁ : ℕ → MvPowerSeries τ R} (h₀ : HasSubst u₀)
    (h₁ : HasSubst u₁) :
    HasSubst
        (fun im : Fin 2 × ℕ =>
            (Fin.cases (u₀ im.2) (fun _ => u₁ im.2) im.1 : MvPowerSeries τ R)) := by
  refine ⟨fun ⟨i, m⟩ => Fin.cases (h₀.const_coeff m) (fun _ => h₁.const_coeff m) i, fun e => ?_⟩
  refine
      (((h₀.coeff_zero e).image (Prod.mk 0)).union ((h₁.coeff_zero e).image (Prod.mk 1))).subset ?_
  rintro ⟨i, m⟩ him
  revert him
  refine Fin.cases (fun him => Or.inl ⟨m, him, rfl⟩) (fun l him => Or.inr ⟨m, him, ?_⟩) i
  fin_cases l; rfl

variable (p R) in
def stepFam (n : ℕ) : Fin 2 × ℕ → MvPowerSeries ℕ R :=
  fun im => Fin.cases (nsmulFam p R n im.2) (fun _ => X im.2) im.1

theorem hasSubst_stepFam (n : ℕ) : HasSubst (stepFam p R n) :=
  hasSubst_finCases (hasSubst_nsmulFam n) HasSubst.X

theorem stepFam_eq (n : ℕ) : stepFam p R n = fun im : Fin 2 × ℕ =>
    ((MvPolynomial.map (Int.castRingHom R) (Fin.cases
      (MvPolynomial.rename Prod.snd (WittVector.wittNSMul p n im.2)) (fun _ => MvPolynomial.X im.2)
        im.1 : MvPolynomial ℕ ℤ) : MvPolynomial ℕ R) : MvPowerSeries ℕ R) := by
  funext ⟨i, m⟩
  refine Fin.cases rfl (fun l => ?_) i
  simp [stepFam]

theorem nsmulFam_succ (n k : ℕ) :
    nsmulFam p R (n + 1) k = subst (stepFam p R n) (addFam p R k) := by
  have hfun : (fun im : Fin 2 × ℕ => MvPolynomial.rename Prod.snd
      (Fin.cases (WittVector.wittNSMul p n im.2) (fun _ => MvPolynomial.X (0, im.2)) im.1 :
        MvPolynomial (Fin 1 × ℕ) ℤ)) =
      fun im => (Fin.cases (MvPolynomial.rename Prod.snd (WittVector.wittNSMul p n im.2))
        (fun _ => MvPolynomial.X im.2) im.1 : MvPolynomial ℕ ℤ) := by
    funext ⟨i, m⟩
    refine Fin.cases rfl (fun l => ?_) i
    simp
  rw [stepFam_eq, subst_coe_addFam, nsmulFam, ← aeval_wittNSMul_wittAdd,
    MvPolynomial.comp_aeval_apply, hfun]

theorem nsmulFam_zero (k : ℕ) : nsmulFam p R 0 k = 0 := by
  rw [nsmulFam, wittNSMul_zero, map_zero, map_zero, MvPolynomial.coe_zero]

theorem nsmulFam_self [CharP R p] (k : ℕ) :
    nsmulFam p R p k = subst (frobFam p R) (verFam R k) := by
  have hcast : Int.castRingHom R = (ZMod.castHom (dvd_refl p) R).comp (Int.castRingHom (ZMod p)) :=
    RingHom.ext_int _ _
  rw [nsmulFam, hcast, ← MvPolynomial.map_map, MvPolynomial.map_rename, map_wittNSMul_self]
  cases k with
  | zero =>
    change
        ((MvPolynomial.map _
            (MvPolynomial.rename Prod.snd (0 : MvPolynomial (Fin 1 × ℕ) (ZMod p))) :
      MvPolynomial ℕ R) : MvPowerSeries ℕ R) = subst (frobFam p R) 0
    rw [map_zero, map_zero, MvPolynomial.coe_zero, ← coe_substAlgHom hasSubst_frobFam, map_zero]
  | succ m =>
    change ((MvPolynomial.map _ (MvPolynomial.rename Prod.snd
        (MvPolynomial.X ((0 : Fin 1), m) ^ p : MvPolynomial (Fin 1 × ℕ) (ZMod p))) :
      MvPolynomial ℕ R) : MvPowerSeries ℕ R) = subst (frobFam p R) (X m)
    rw [map_pow, MvPolynomial.rename_X, map_pow, MvPolynomial.map_X, MvPolynomial.coe_pow,
      MvPolynomial.coe_X, subst_X hasSubst_frobFam]
    rfl

end WittLaw

namespace CartierModule

variable {Φ : MvFormalGroup d R} {Φ' : MvFormalGroup d' R} {Φ'' : MvFormalGroup d'' R}

theorem subst_nsmulFam [Φ.IsComm] (f : CartierModule p Φ) (n : ℕ) (j : Fin d) :
    subst (WittLaw.nsmulFam p R n) (f.toPowerSeries j) = (n • f).toPowerSeries j := by
  induction n generalizing j with
  | zero =>
    rw [zero_nsmul]
    have h0 : WittLaw.nsmulFam p R 0 = fun _ => 0 := funext WittLaw.nsmulFam_zero
    rw [h0]
    exact subst_zero_of_constantCoeff_eq_zero (f.constantCoeff_eq_zero j)
  | succ n ih =>
    have hf := f.constantCoeff_eq_zero
    have hS := WittLaw.hasSubst_stepFam (p := p) (R := R) n
    have hfam : WittLaw.nsmulFam p R (n + 1) =
        fun k => subst (WittLaw.stepFam p R n) (WittLaw.addFam p R k) :=
      funext (WittLaw.nsmulFam_succ n)
    rw [hfam, ← subst_comp_subst_apply (hasSubst_addFam p R) hS, f.subst_addFam,
      subst_subst_elim Φ (constantCoeff_inBlk 0 hf) (constantCoeff_inBlk 1 hf) hS, succ_nsmul,
      toPowerSeries_add]
    congr 1
    funext s
    rcases s with l | l
    · change subst (WittLaw.stepFam p R n) (subst (blk 0) (f.toPowerSeries l)) =
        (n • f).toPowerSeries l
      rw [subst_comp_subst_apply (hasSubst_blk 0) hS, ← ih l]
      congr 1
      funext m
      exact subst_X hS ((0 : Fin 2), m)
    · change subst (WittLaw.stepFam p R n) (subst (blk 1) (f.toPowerSeries l)) = f.toPowerSeries l
      rw [subst_comp_subst_apply (hasSubst_blk 1) hS]
      have hX : (fun m => subst (WittLaw.stepFam p R n) (blk (R := R) 1 m)) =
          fun m => (X m : MvPowerSeries ℕ R) := by
        funext m
        exact subst_X hS ((1 : Fin 2), m)
      rw [hX]
      exact congrFun subst_self _

theorem verschiebung_frobenius [Φ.IsComm] [CharP R p] (f : CartierModule p Φ) :
    verschiebung (frobenius f) = (p : ℕ) • f := by
  apply CartierModule.ext
  funext j
  rw [verschiebung, frobenius, precomp_precomp, ← subst_nsmulFam]
  congr 1
  funext k
  exact (WittLaw.nsmulFam_self k).symm

theorem frobenius_verschiebung_eq_nsmul [Φ.IsComm] [CharP R p] (f : CartierModule p Φ) :
    frobenius (verschiebung f) = (p : ℕ) • f := by
  rw [frobenius_verschiebung, verschiebung_frobenius]

def tangent [Φ.IsComm] : CartierModule p Φ →+ (Fin d → R) where
  toFun f := fun j => coeff (Finsupp.single 0 1) (f.toPowerSeries j)
  map_zero' := by
    funext j
    simp
  map_add' f g := by
    funext j
    change coeff (Finsupp.single 0 1) (subst (Sum.elim f.toPowerSeries g.toPowerSeries)
      (Φ.toPowerSeries j)) = _
    have h0 : ∀ s, ((Sum.elim f.toPowerSeries g.toPowerSeries) s).constantCoeff = 0 := by
      rintro (l | l)
      exacts [f.constantCoeff_eq_zero l, g.constantCoeff_eq_zero l]
    rw [coeff_single_subst h0, Fintype.sum_sum_type]
    simp only [Sum.elim_inl, Sum.elim_inr, Φ.coeff_single_inl, Φ.coeff_single_inr, ite_mul,
      one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
    rfl

@[simp] theorem tangent_apply [Φ.IsComm] (f : CartierModule p Φ) (j : Fin d) :
    tangent f j = coeff (Finsupp.single 0 1) (f.toPowerSeries j) := rfl

theorem tangent_verschiebung [Φ.IsComm] [CharP R p] (f : CartierModule p Φ) :
    tangent (verschiebung f) = 0 := by
  funext j
  rw [tangent_apply, toPowerSeries_verschiebung_eq_expand]
  exact MvPowerSeries.coeff_expand_of_not_dvd p hp.out.ne_zero _ (i := 0)
    (by simpa using hp.out.one_lt.ne')

theorem tangent_map [Φ.IsComm] [Φ'.IsComm] (φ : Φ.Hom Φ') (f : CartierModule p Φ) :
    tangent (map φ f) = (MvFormalGroup.linearPart φ.toPowerSeries).mulVec (tangent f) := by
  funext i
  change coeff (Finsupp.single 0 1) (subst f.toPowerSeries (φ.toPowerSeries i)) = _
  rw [coeff_single_subst f.constantCoeff_eq_zero, Matrix.mulVec]
  rfl

def curveFam (R : Type u) [CommRing R] : ℕ → PowerSeries R
  | 0 => PowerSeries.X
  | _ + 1 => 0

omit hp in
theorem constantCoeff_curveFam (n : ℕ) : MvPowerSeries.constantCoeff (curveFam R n) = 0 := by
  cases n with
  | zero => exact MvPowerSeries.constantCoeff_X _
  | succ n => exact map_zero _

omit hp in
theorem hasSubst_curveFam : HasSubst (curveFam R) := by
  refine ⟨fun n => by rw [constantCoeff_curveFam]; exact IsNilpotent.zero, fun e => ?_⟩
  refine (Set.finite_singleton 0).subset fun n hn => ?_
  cases n with
  | zero => rfl
  | succ n => exact absurd (by simp [curveFam]) hn

def curve (f : CartierModule p Φ) : Fin d → PowerSeries R :=
  fun j => subst (curveFam R) (f.toPowerSeries j)

theorem curve_apply (f : CartierModule p Φ) (j : Fin d) :
    curve f j = subst (curveFam R) (f.toPowerSeries j) := rfl

theorem constantCoeff_curve (f : CartierModule p Φ) (j : Fin d) :
    PowerSeries.constantCoeff (curve f j) = 0 :=
  constantCoeff_subst_eq_zero hasSubst_curveFam constantCoeff_curveFam (f.constantCoeff_eq_zero j)

theorem curve_add [Φ.IsComm] (f g : CartierModule p Φ) (j : Fin d) :
    curve (f + g) j = subst (Sum.elim (curve f) (curve g)) (Φ.toPowerSeries j) :=
  subst_subst_elim Φ f.constantCoeff_eq_zero g.constantCoeff_eq_zero hasSubst_curveFam j

theorem curve_verschiebung [Φ.IsComm] [CharP R p] (f : CartierModule p Φ) (j : Fin d) :
    curve (verschiebung f) j = PowerSeries.expand p hp.out.ne_zero (curve f j) := by
  change subst (curveFam R) (subst (WittLaw.frobFam p R) (f.toPowerSeries j)) =
    MvPowerSeries.expand p hp.out.ne_zero (subst (curveFam R) (f.toPowerSeries j))
  rw [MvPowerSeries.expand, substAlgHom_apply,
    subst_comp_subst_apply WittLaw.hasSubst_frobFam hasSubst_curveFam,
    subst_comp_subst_apply hasSubst_curveFam (HasSubst.X_pow hp.out.ne_zero)]
  congr 1
  funext n
  cases n with
  | zero =>
    change subst (curveFam R) (X 0 ^ p : MvPowerSeries ℕ R) =
      subst (fun s : Unit => (X s : MvPowerSeries Unit R) ^ p) PowerSeries.X
    rw [subst_pow hasSubst_curveFam, subst_X hasSubst_curveFam, PowerSeries.X,
      subst_X (HasSubst.X_pow hp.out.ne_zero)]
    rfl
  | succ m =>
    change subst (curveFam R) (X (m + 1) ^ p : MvPowerSeries ℕ R) =
      subst (fun s : Unit => (X s : MvPowerSeries Unit R) ^ p) (0 : PowerSeries R)
    rw [subst_pow hasSubst_curveFam, subst_X hasSubst_curveFam,
      ← coe_substAlgHom (HasSubst.X_pow hp.out.ne_zero), map_zero]
    exact zero_pow hp.out.ne_zero

theorem coeff_one_curve [Φ.IsComm] (f : CartierModule p Φ) (j : Fin d) :
    PowerSeries.coeff 1 (curve f j) = tangent f j := by
  classical
  rw [tangent_apply, curve_apply]
  change MvPowerSeries.coeff (Finsupp.single () 1) (subst (curveFam R) (f.toPowerSeries j)) = _
  rw [coeff_subst hasSubst_curveFam]
  have hterm : ∀ e : ℕ →₀ ℕ, e ≠ Finsupp.single 0 1 →
      coeff e (f.toPowerSeries j) •
        coeff (Finsupp.single () 1) (e.prod fun n k => curveFam R n ^ k) = 0 := by
    intro e he
    by_cases hsupp : ∃ n ∈ e.support, n ≠ 0
    · obtain ⟨n, hn, hn0⟩ := hsupp
      have hzero : (e.prod fun n k => curveFam R n ^ k) = 0 := by
        rw [Finsupp.prod]
        refine Finset.prod_eq_zero hn ?_
        obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn0
        change (0 : PowerSeries R) ^ e (m + 1) = 0
        exact zero_pow (Finsupp.mem_support_iff.mp hn)
      rw [hzero, map_zero, smul_zero]
    · push Not at hsupp
      have he0 : e = Finsupp.single 0 (e 0) := by
        ext n
        by_cases hn : n = 0
        · subst hn; simp
        · rw [Finsupp.single_apply, ite_eq_right (Ne.symm hn)]
          by_contra hne
          exact hn (hsupp n (Finsupp.mem_support_iff.mpr hne))
      have hk : e 0 ≠ 1 := fun h1 => he (by rw [he0, h1])
      rw [he0, Finsupp.prod_single_index (by simp)]
      change coeff _ (f.toPowerSeries j) • coeff (Finsupp.single () 1)
        ((PowerSeries.X : PowerSeries R) ^ e 0) = 0
      rw [PowerSeries.X, coeff_X_pow, ite_eq_right, smul_zero]
      intro h
      exact hk ((Finsupp.single_injective ()) h).symm
  rw [finsum_eq_single _ (Finsupp.single 0 1) hterm, Finsupp.prod_single_index (by simp)]
  change coeff _ (f.toPowerSeries j) • coeff (Finsupp.single () 1)
    ((PowerSeries.X : PowerSeries R) ^ 1) = _
  rw [pow_one, PowerSeries.X, coeff_X, ite_eq_left rfl, smul_eq_mul, mul_one]

namespace Examples

def addLinear (p : ℕ) [Fact p.Prime] {d : ℕ} {R : Type u} [CommRing R] (v : Fin d → R) :
    CartierModule p (addMv d R) where
  toPowerSeries := fun i => v i • (X 0 : MvPowerSeries ℕ R)
  constantCoeff_eq_zero := fun i => by simp
  subst_eq := by
    intro i
    have hc : ∀ l, ((fun l => v l • (X 0 : MvPowerSeries ℕ R)) l).constantCoeff = 0 :=
      fun l => by simp
    have h0 : ∀ s, ((Sum.elim (inBlk 0 fun l => v l • (X 0 : MvPowerSeries ℕ R))
        (inBlk 1 fun l => v l • (X 0 : MvPowerSeries ℕ R))) s).constantCoeff = 0 := by
      rintro (l | l)
      exacts [constantCoeff_inBlk 0 hc l, constantCoeff_inBlk 1 hc l]
    change subst (WittLaw.addFam p R) (v i • (X 0 : MvPowerSeries ℕ R)) =
      subst (Sum.elim (inBlk 0 fun l => v l • (X 0 : MvPowerSeries ℕ R))
        (inBlk 1 fun l => v l • (X 0 : MvPowerSeries ℕ R)))
        ((X (Sum.inl i) : MvPowerSeries (Fin d ⊕ Fin d) R) + X (Sum.inr i))
    rw [subst_X_add_X h0]
    simp only [Sum.elim_inl, Sum.elim_inr, inBlk_apply]
    rw [← coe_substAlgHom (hasSubst_addFam p R), ← coe_substAlgHom (hasSubst_blk 0),
      ← coe_substAlgHom (hasSubst_blk 1), AlgHom.map_smul_of_tower, AlgHom.map_smul_of_tower,
      AlgHom.map_smul_of_tower, coe_substAlgHom, coe_substAlgHom, coe_substAlgHom,
      subst_X (hasSubst_addFam p R), subst_X (hasSubst_blk 0), subst_X (hasSubst_blk 1),
      WittLaw.addFam, WittVector.wittAdd_zero, ← smul_add]
    congr 1
    simp [WittLaw.blk]

@[simp] theorem toPowerSeries_addLinear (v : Fin d → R) (i : Fin d) :
    (addLinear p v).toPowerSeries i = v i • (X 0 : MvPowerSeries ℕ R) := rfl

theorem tangent_addLinear (v : Fin d → R) : tangent (addLinear p v) = v := by
  classical
  funext i
  rw
      [tangent_apply, toPowerSeries_addLinear, map_smul, coeff_X, ite_eq_left rfl, smul_eq_mul,
          mul_one]

theorem tangent_surjective_addMv :
    Function.Surjective (tangent : CartierModule p (addMv d R) → Fin d → R) :=
  fun v => ⟨addLinear p v, tangent_addLinear v⟩

theorem addLinear_ne_zero [Nontrivial R] {v : Fin d → R} (hv : v ≠ 0) : addLinear p v ≠ 0 := by
  intro h
  apply hv
  have := tangent_addLinear (p := p) v
  rw [h, map_zero] at this
  exact this.symm

end Examples

end CartierModule

end MvFormalGroup

end
