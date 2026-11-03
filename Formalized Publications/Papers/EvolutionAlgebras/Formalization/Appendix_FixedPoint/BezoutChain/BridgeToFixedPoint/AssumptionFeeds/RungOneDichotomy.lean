/-
Copyright (c) 2026 Andres Barei. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andres Barei
-/
import Appendix_FixedPoint.BezoutChain.BridgeToFixedPoint.FixedPointFromBezout
import Appendix_FixedPoint.BezoutChain.BridgeToFixedPoint.CoordinatizationSemiring
import Appendix_FixedPoint.BezoutChain.Regularity.Assembly.JointAssembly
import Section_2_Preliminaries.A_Preliminaries
import Mathlib.Data.Finsupp.Weight
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Option
import Mathlib.FieldTheory.IsAlgClosed.Basic

/-!
# Rung-1 dichotomy without orthogonality
Proves per-instance `HdichRung1` from realized algebra data `(b, hexp, hN)`
plus scalar-compatibility and algebraic closedness — with no orthogonality
hypothesis — conditional on the few-forms common-zero lemma
(`FewFormsCommonZero`, design note §3 L2, the explicitly scoped residual R1).

## Proof (design note §3: L0 + L1 + L3; L2 as hypothesis)

* L0 (`factor_pair_of_div_of_cross`, `isHomogeneous_one_of_X_mul`):
  Hdich-failure at `(I0, k)` gives `L0` with `F_I0 = X_I0 * L0`; the
  vanishing cross term cancels (domain) to `F_k = X_k * L0`; homogeneity
  pins `L0` at degree 1 (or `L0 = 0`).
* L1 (`eval_bridgeForms_eq_sqCoords`, `sqCoords_eq_mul_of_bridge_factor`):
  `(x²)_d = x'_i * L0(x')` via `eval_mkQuadForm` + `sqCoords_shift`.
* L2 (`FewFormsCommonZero`, hypothesis): `m` homogeneous positive-degree
  forms in `N` variables, `m < N`, over an algebraically closed field have
  a common nonzero zero. Applied to `{L0'} ∪ {Q_j}` (`n - 1` forms in `n`
  variables; `L0 = 0` case: `n - 2` forms; `n = 1` flows through the
  counting contradiction uniformly).
* L3 (main-theorem close): `sq_expand` + `eq_zero_of_mem_sq_eq_zero` +
  `coordVec_eq_zero` — the Leg-B pattern (`Hge2HdichRealized`).

## Spine note

The polynomial eval-bridge speaks `Appendix_FixedPoint.BezoutChain.sqCoords` (Ring spine,
`FixedPointFromBezout`), while `sq_expand` speaks
`CoordinatizationSemiring.sqCoords` (Semiring spine); the bodies are identical,
bridged by `sqCoords_spine_eq` (`rfl`).

Conditional on exactly `[FewFormsCommonZero]` given realized algebra
data + scalar-compatibility + `[IsAlgClosed K]`.

## Import DAG

New leaf module (no importers): `BridgeToFixedPoint/FixedPointFromBezout` (bridge forms
+ eval lemmas), `BridgeToFixedPoint/CoordinatizationSemiring` (Semiring-spine toolkit),
`Regularity/JointAssembly` (`HdichRung1` address), `A_Preliminaries`
(`absNilpotent`), Mathlib (`IsAlgClosed`, Fintype, Finsupp-weight). No cycle
risk. `MkSystemBridge` is deliberately not imported (it duplicates the
`E.B.*` bridge address set used by `HdichRung1`).
-/

namespace EvolutionAlgebras
namespace Appendix_FixedPoint.BezoutChain
namespace RungOneDichotomy

/-! ## L2 residual: few-forms common zero -/

/-- Few-forms common zero (design note §3 L2, residual R1): `m` homogeneous
positive-degree forms in `N` variables over an algebraically closed field,
`m < N`, have a common nonzero zero. Zero forms are allowed (they vanish
everywhere); only homogeneity + degree `≥ 1` is required.

Status: residual (stated, not proved — the scoped L2 gap). -/
def FewFormsCommonZero (K : Type*) [Field K] [IsAlgClosed K] : Prop :=
  ∀ (N : ℕ) {ι : Type} [Fintype ι] (_hcard : Fintype.card ι < N)
    (F : ι → MvPolynomial (Fin N) K) (d : ι → ℕ),
    (∀ j, (F j).IsHomogeneous (d j)) → (∀ j, 1 ≤ d j) →
      ∃ a : Fin N → K, a ≠ 0 ∧ ∀ j, MvPolynomial.eval a (F j) = 0

#print axioms FewFormsCommonZero

/-! ## L0: factor extraction -/

/-- L0-cancel: from `F0 = X0 * L0` and vanishing cross
`X0 * Fk - Xk * F0 = 0`, cancel `X0` (domain, `X0 ≠ 0`) to get
`Fk = Xk * L0`.
-/
theorem factor_pair_of_div_of_cross {σ : Type*} {K : Type*} [Field K]
    {F0 Fk X0 Xk L0 : MvPolynomial σ K}
    (hdiv : F0 = X0 * L0) (hcross : X0 * Fk - Xk * F0 = 0)
    (hX0 : X0 ≠ 0) : Fk = Xk * L0 := by
  have hsub := sub_eq_zero.mp hcross
  rw [hdiv] at hsub
  have hfactor : Xk * (X0 * L0) = X0 * (Xk * L0) := by ring
  rw [hfactor] at hsub
  exact mul_left_cancel₀ hX0 hsub

#print axioms factor_pair_of_div_of_cross

/-- L0-degree: a factor `L0` of a homogeneous degree-2 form through `X s`
is homogeneous of degree 1 (support argument via `coeff_X_mul`).
-/
theorem isHomogeneous_one_of_X_mul {σ : Type*} {K : Type*} [Field K]
    (s : σ) {F L0 : MvPolynomial σ K}
    (hF : F.IsHomogeneous 2) (hFac : F = MvPolynomial.X s * L0) :
    L0.IsHomogeneous 1 := by
  intro d hd
  have hmem : F.coeff (Finsupp.single s 1 + d) ≠ 0 := by
    rw [hFac, MvPolynomial.coeff_X_mul]
    exact hd
  have h2 : Finsupp.weight (1 : σ → ℕ) (Finsupp.single s 1 + d) = 2 := hF hmem
  rw [map_add, Finsupp.weight_single] at h2
  simp only [Pi.one_apply, smul_eq_mul, mul_one] at h2
  omega

#print axioms isHomogeneous_one_of_X_mul

/-! ## L1: eval bridge -/

/-- Spine bridge: the Ring-spine `Appendix_FixedPoint.BezoutChain.sqCoords` (seen by
`eval_mkQuadForm`) equals the Semiring-spine `CoordinatizationSemiring.sqCoords`
(seen by `sq_expand`); bodies are identical.
-/
theorem sqCoords_spine_eq (K : Type*) [Field K] {n : ℕ}
    (c : Fin n → Fin n → Fin n → K) (k : Fin n) (X : Fin n → K) :
    EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.sqCoords K c k X
      = CoordinatizationSemiring.sqCoords K c k X := rfl

#print axioms sqCoords_spine_eq

/-- L1-eval: polynomial evaluation of a bridge form equals the
(Semiring-spine) squared-coordinates at the shifted index, via
`eval_mkQuadForm` + `sqCoords_shift`.
-/
theorem eval_bridgeForms_eq_sqCoords (n : ℕ) (K : Type*) [Field K]
    (c : Fin n → Fin n → Fin n → K) (hn : 0 < n)
    (X : Fin n → K) (X' : Fin (statementIndex n + 1) → K)
    (hX : ∀ j, X' j = X (shiftEquiv n hn j)) (j : Fin (statementIndex n + 1)) :
    MvPolynomial.eval X' (bridgeForms n K c hn j)
      = CoordinatizationSemiring.sqCoords K c (shiftEquiv n hn j) X := by
  have h : MvPolynomial.eval X' (bridgeForms n K c hn j)
      = sqCoords K c (shiftEquiv n hn j) X := by
    change MvPolynomial.eval X'
      (mkQuadForm (statementIndex n + 1) K (shiftConsts n K c hn) j) = _
    rw [eval_mkQuadForm]
    change sqCoords K
      (fun p q r => c (shiftEquiv n hn p) (shiftEquiv n hn q)
        (shiftEquiv n hn r)) j X' = _
    exact sqCoords_shift (statementIndex n + 1) n K (shiftEquiv n hn) c X' X j hX
  rwa [sqCoords_spine_eq] at h

#print axioms eval_bridgeForms_eq_sqCoords

/-- L1-factor: at a factored bridge form `F j = X j * L0`, the
squared-coordinate equals `X' j * eval X' L0`.
-/
theorem sqCoords_eq_mul_of_bridge_factor (n : ℕ) (K : Type*) [Field K]
    (c : Fin n → Fin n → Fin n → K) (hn : 0 < n)
    (X : Fin n → K) (X' : Fin (statementIndex n + 1) → K)
    (hX : ∀ j, X' j = X (shiftEquiv n hn j)) (j : Fin (statementIndex n + 1))
    (L0 : MvPolynomial (Fin (statementIndex n + 1)) K)
    (hF : bridgeForms n K c hn j = MvPolynomial.X j * L0) :
    CoordinatizationSemiring.sqCoords K c (shiftEquiv n hn j) X
      = X' j * MvPolynomial.eval X' L0 := by
  have hb := eval_bridgeForms_eq_sqCoords n K c hn X X' hX j
  rw [hF, MvPolynomial.eval_mul, MvPolynomial.eval_X] at hb
  exact hb.symm

#print axioms sqCoords_eq_mul_of_bridge_factor

/-! ## Index counting for the L2 application -/

/-- Complement-of-two-indices counting: removing two distinct indices leaves
`card + 1 < n` (feeds the L2 `m < N` side goal in both cases; `n = 1` flows
through the counting contradiction uniformly).
-/
theorem card_compl_two_add_one_lt (n : ℕ) (hn : 0 < n) (d0 d1 : Fin n)
    (hdd : d0 ≠ d1) :
    Fintype.card {k' : Fin n // k' ≠ d0 ∧ k' ≠ d1} + 1 < n := by
  classical
  have h10 : d1 ≠ d0 := Ne.symm hdd
  have hcardt : Fintype.card {k' : Fin n // k' ≠ d0} = n - 1 := by
    have h1 : Fintype.card {k' : Fin n // k' ≠ d0}
        = Fintype.card ↥(Finset.univ.erase d0) :=
      Fintype.card_congr
        { toFun := fun x =>
            ⟨x.val, Finset.mem_erase.mpr ⟨x.property, Finset.mem_univ _⟩⟩
          invFun := fun x => ⟨x.val, (Finset.mem_erase.mp x.property).1⟩
          left_inv := fun x => rfl
          right_inv := fun x => rfl }
    rw [h1, Fintype.card_coe, Finset.card_erase_of_mem (Finset.mem_univ d0),
      Finset.card_univ, Fintype.card_fin]
  have hlt : Fintype.card {k' : Fin n // k' ≠ d0 ∧ k' ≠ d1}
      < Fintype.card {k' : Fin n // k' ≠ d0} := by
    have he : Fintype.card {k' : Fin n // k' ≠ d0 ∧ k' ≠ d1}
        = Fintype.card {x : {k' : Fin n // k' ≠ d0} // x.val ≠ d1} :=
      Fintype.card_congr
        (Equiv.subtypeSubtypeEquivSubtypeInter (fun x : Fin n => x ≠ d0)
          (fun x : Fin n => x ≠ d1)).symm
    rw [he]
    have hx : ¬ ((⟨d1, h10⟩ : {k' : Fin n // k' ≠ d0}).val ≠ d1) :=
      fun h => h rfl
    exact Fintype.card_subtype_lt (x := (⟨d1, h10⟩ : {k' : Fin n // k' ≠ d0})) hx
  omega

#print axioms card_compl_two_add_one_lt

/-! ## Main close: unhorth Hdich from `(hexp, hN)` + L2 -/

/-- Rung-1 dichotomy at realized structure constants without horth
(unhorth): per-instance `HdichRung1` from `(b, hexp, hN)` plus
scalar-compatibility and `IsAlgClosed`, conditional on `FewFormsCommonZero`.
Proof: Hdich-failure gives `L0` (L0); the L2 common zero of `{L0'} ∪
{quadrics}` forces a nonzero vector of `V` squaring to zero (L1+L3),
against `hN`.

Conditional on exactly `[FewFormsCommonZero]` given realized algebra
data + scalar-compatibility + `[IsAlgClosed K]`. -/
theorem hdichRung1_unhorth_of_commonZero
    (K E : Type*) [Field K] [IsAlgClosed K]
    [NonUnitalNonAssocSemiring E] [Module K E]
    (V : Submodule K E)
    (n : ℕ) (hn : 0 < n) (c : Fin n → Fin n → Fin n → K)
    (b : Module.Basis (Fin n) K V)
    (hexp : ∀ i j, (b i : E) * (b j : E) = ∑ k, c i j k • (b k : E))
    (hN : absNilpotent K E V = {0})
    (htower : IsScalarTower K E E) (hcomm : SMulCommClass K E E)
    (hL2 : FewFormsCommonZero K) :
    JointAssembly.HdichRung1 n K c hn := by
  classical
  intro k hk
  set I0 : Fin (statementIndex n + 1) := ⟨0, Nat.zero_lt_succ _⟩
  have hkI0 : k ≠ I0 := by
    intro h
    rw [h] at hk
    have hI0v : I0.val = 0 := rfl
    omega
  by_contra hcon
  rw [not_or] at hcon
  obtain ⟨hdiv2, hex⟩ := hcon
  have hdiv : MvPolynomial.X I0 ∣ bridgeForms n K c hn I0 :=
    not_not.mp hdiv2
  obtain ⟨L0, hF0⟩ := hdiv
  have hcross0 : MvPolynomial.X I0 * bridgeForms n K c hn k
      - MvPolynomial.X k * bridgeForms n K c hn I0 = 0 := by
    by_contra hc
    exact hex ⟨L0, hF0, hc⟩
  have hFk : bridgeForms n K c hn k = MvPolynomial.X k * L0 :=
    factor_pair_of_div_of_cross hF0 hcross0 (MvPolynomial.X_ne_zero _)
  set d0 := shiftEquiv n hn I0
  set d1 := shiftEquiv n hn k
  have hdd : d0 ≠ d1 := fun h =>
    hkI0 ((shiftEquiv n hn).injective
      (h : shiftEquiv n hn I0 = shiftEquiv n hn k)).symm
  have hcount : Fintype.card {k' : Fin n // k' ≠ d0 ∧ k' ≠ d1} + 1 < n :=
    card_compl_two_add_one_lt n hn d0 d1 hdd
  set Q : Fin n → MvPolynomial (Fin n) K := fun k' =>
    (bridgeForms n K c hn ((shiftEquiv n hn).symm k')).rename
      ⇑(shiftEquiv n hn)
  have hQhom : ∀ k', (Q k').IsHomogeneous 2 := fun k' => by
    change ((bridgeForms n K c hn ((shiftEquiv n hn).symm k')).rename
      ⇑(shiftEquiv n hn)).IsHomogeneous 2
    exact MvPolynomial.IsHomogeneous.rename_isHomogeneous
      (bridgeForms_homogeneous n K c hn ((shiftEquiv n hn).symm k'))
  have hQeval : ∀ (a : Fin n → K) (k' : Fin n),
      MvPolynomial.eval a (Q k')
        = CoordinatizationSemiring.sqCoords K c k' a := by
    intro a k'
    have hb := eval_bridgeForms_eq_sqCoords n K c hn a
      (a ∘ ⇑(shiftEquiv n hn)) (fun j => rfl) ((shiftEquiv n hn).symm k')
    rw [Equiv.apply_symm_apply] at hb
    have hrw : MvPolynomial.eval a (Q k')
        = MvPolynomial.eval (a ∘ ⇑(shiftEquiv n hn))
          (bridgeForms n K c hn ((shiftEquiv n hn).symm k')) := by
      change MvPolynomial.eval a
        ((bridgeForms n K c hn ((shiftEquiv n hn).symm k')).rename
          ⇑(shiftEquiv n hn)) = _
      rw [MvPolynomial.eval_rename]
    rw [hrw]
    exact hb
  by_cases hL0 : L0 = 0
  · subst hL0
    rw [mul_zero] at hF0 hFk
    have hlt0 : Fintype.card {k' : Fin n // k' ≠ d0 ∧ k' ≠ d1} < n := by
      omega
    obtain ⟨a, ha0, hvan⟩ := hL2 n hlt0
      (fun t : {k' : Fin n // k' ≠ d0 ∧ k' ≠ d1} => Q t.val)
      (fun _ => 2) (fun t => hQhom t.val) (fun _ => one_le_two)
    have hsq0 : ∀ k' : Fin n, CoordinatizationSemiring.sqCoords K c k' a = 0 := by
      intro k'
      by_cases hk0 : k' = d0
      · subst hk0
        have hb := eval_bridgeForms_eq_sqCoords n K c hn a
          (a ∘ ⇑(shiftEquiv n hn)) (fun j => rfl) I0
        rw [hF0, map_zero] at hb
        rw [show shiftEquiv n hn I0 = d0 from rfl] at hb
        exact hb.symm
      · by_cases hk1 : k' = d1
        · subst hk1
          have hb := eval_bridgeForms_eq_sqCoords n K c hn a
            (a ∘ ⇑(shiftEquiv n hn)) (fun j => rfl) k
          rw [hFk, map_zero] at hb
          rw [show shiftEquiv n hn k = d1 from rfl] at hb
          exact hb.symm
        · have hw : MvPolynomial.eval a (Q k') = 0 := hvan ⟨k', hk0, hk1⟩
          rw [hQeval a k'] at hw
          exact hw
    have hsq := @CoordinatizationSemiring.sq_expand K E inferInstance inferInstance
      inferInstance _ _ b c hexp a htower hcomm
    simp only [hsq0, zero_smul, Finset.sum_const_zero] at hsq
    have hmem := CoordinatizationSemiring.coordVec_mem K E b a
    have hcz := CoordinatizationSemiring.eq_zero_of_mem_sq_eq_zero K E V hN hmem hsq
    have haz := CoordinatizationSemiring.coordVec_eq_zero K E b a hcz
    exact ha0 haz
  · have hL0h : L0.IsHomogeneous 1 :=
      isHomogeneous_one_of_X_mul I0
        (bridgeForms_homogeneous n K c hn I0) hF0
    set L0' : MvPolynomial (Fin n) K := L0.rename ⇑(shiftEquiv n hn)
    have hL0'h : L0'.IsHomogeneous 1 := by
      change (L0.rename ⇑(shiftEquiv n hn)).IsHomogeneous 1
      exact MvPolynomial.IsHomogeneous.rename_isHomogeneous hL0h
    have hL0'eval : ∀ a : Fin n → K, MvPolynomial.eval a L0'
        = MvPolynomial.eval (a ∘ ⇑(shiftEquiv n hn)) L0 := by
      intro a
      change MvPolynomial.eval a (L0.rename ⇑(shiftEquiv n hn)) = _
      rw [MvPolynomial.eval_rename]
    have hlt1 : Fintype.card (Option {k' : Fin n // k' ≠ d0 ∧ k' ≠ d1})
        < n := by
      rw [Fintype.card_option]
      omega
    obtain ⟨a, ha0, hvan⟩ := hL2 n hlt1
      (fun o : Option {k' : Fin n // k' ≠ d0 ∧ k' ≠ d1} => match o with
        | none => L0'
        | some t => Q t.val)
      (fun o => match o with | none => 1 | some _ => 2)
      (fun o => match o with
        | none => hL0'h
        | some t => hQhom t.val)
      (fun o => match o with | none => le_refl 1 | some _ => one_le_two)
    have hL0v : MvPolynomial.eval (a ∘ ⇑(shiftEquiv n hn)) L0 = 0 := by
      have hv : MvPolynomial.eval a L0' = 0 := hvan none
      rwa [hL0'eval a] at hv
    have hsq0 : ∀ k' : Fin n, CoordinatizationSemiring.sqCoords K c k' a = 0 := by
      intro k'
      by_cases hk0 : k' = d0
      · subst hk0
        have hb := sqCoords_eq_mul_of_bridge_factor n K c hn a
          (a ∘ ⇑(shiftEquiv n hn)) (fun j => rfl) I0 L0 hF0
        rw [show shiftEquiv n hn I0 = d0 from rfl, hL0v, mul_zero] at hb
        exact hb
      · by_cases hk1 : k' = d1
        · subst hk1
          have hb := sqCoords_eq_mul_of_bridge_factor n K c hn a
            (a ∘ ⇑(shiftEquiv n hn)) (fun j => rfl) k L0 hFk
          rw [show shiftEquiv n hn k = d1 from rfl, hL0v, mul_zero] at hb
          exact hb
        · have hw : MvPolynomial.eval a (Q k') = 0 :=
            hvan (some ⟨k', hk0, hk1⟩)
          rw [hQeval a k'] at hw
          exact hw
    have hsq := @CoordinatizationSemiring.sq_expand K E inferInstance inferInstance
      inferInstance _ _ b c hexp a htower hcomm
    simp only [hsq0, zero_smul, Finset.sum_const_zero] at hsq
    have hmem := CoordinatizationSemiring.coordVec_mem K E b a
    have hcz := CoordinatizationSemiring.eq_zero_of_mem_sq_eq_zero K E V hN hmem hsq
    have haz := CoordinatizationSemiring.coordVec_eq_zero K E b a hcz
    exact ha0 haz

#print axioms hdichRung1_unhorth_of_commonZero

end RungOneDichotomy
end Appendix_FixedPoint.BezoutChain
end EvolutionAlgebras
