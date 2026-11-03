/-
Copyright (c) 2026 Andres Barei. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andres Barei
-/
import Appendix_FixedPoint.BezoutChain.Regularity.CohenMacaulayLink.CMQuotientFull
import Appendix_FixedPoint.BezoutChain.Regularity.CohenMacaulayLink.QuotientByRegularIsCM
import Appendix_FixedPoint.BezoutChain.Regularity.CohenMacaulayLink.CMPositiveDimHasDepth

/-!
# C1-full greedy tower: `GreedyOfResiduals` assembly
Proves the §3 greedy assembly tower: strong induction on `n` + the
inner greedy construction (A2 + A3 + C2-av + B-reg + C2-mk per step, closed
by the capstone `K_of_greedy`), with the IH re-presentation
(`RepConcat`) proved here.

## Status: proved (no tower residuals)

* `greedy_extend` (§2 assembly), `isRegular_map_ringEquiv` (verdict
  finding 1), `isRegular_snoc_of_isSMulRegular_quotient` (verdict
  finding 2), `tower_dim_add_length` (rep-dim), plus the `WithBot ℕ∞`
  dim plumbing.
* `RepConcat` (design note §3 full binders, `Nonempty` form): a
  regular-quotient-of-CI-quotient is CI — proved as `repConcat_proof`
  (lifts + span-append algebra + regularity induction via
  `isRegular_append_of_isRegular_quotient` + dq identification via
  `quotEquivOfEquiv`).
* `ciQuotient_tower_step` (rep-tower) and `greedy_of_residuals`
  (`∀ n, GreedyOfResiduals.{uK,uS,uS,uK,uS} n`), closing the C1Full
  `GreedyOfResiduals` residual on the universe diagonal. The only
  remaining assumptions are the proved C1Full residuals `FirstReg` and
  `C3aGapAll` (taken as hypotheses, as the design note specifies).

## Universe note (why the diagonal)

`GreedyOfResiduals.{u₁,u₂,u₃,u₄,u₅} n` is
`FirstReg.{u₁,u₂} → C3aGapAll.{u₃} → GreedyWitness.{u₄,u₅} n`.
The residuals can only fire at their own universes, so the provable form
is the diagonal `GreedyOfResiduals.{uK,uS,uS,uK,uS} n`: `FirstReg` fires
at the `(K, S)` of `GreedyWitness`, `C3aGapAll` fires at each tower rung
`T_j = S ⧸ span(ys)` (same universe as `S`). Off-diagonal instances are
not claimed.

## Circularity

This file imports only `CMQuotientFull/C2/C3` (same import
closure as C1Full: no `DimEqualsEmbdim`, no `AssociatedGradedRing`, no
crux-ring files). C3
enters only via proved A2 (`maximalIdeal_notMem_associatedPrimes_of_isCM`)
at smaller dimension and the pure-dq helpers (`memSet_cons`,
`memSet_nil`, `memSet_map`, `map_span_image`,
`isRegular_spanQuotient_of_isRegular_quotSMulTop`,
`smul_top_eq_span_singleton`); the C3a localization theorem and F7 are
never consumed (pattern-mirroring only). A grep for the
forbidden identifiers is empty here.

-/

namespace EvolutionAlgebras
namespace Appendix_FixedPoint.BezoutChain
namespace CMQuotientGreedyTower

open RingTheory.Sequence

universe u uK uS uT

/-! ## §A: dimension plumbing (`WithBot ℕ∞` nat extraction) -/

/-- From `d + ↑j = ↑m` (nat casts in `WithBot ℕ∞`) conclude `d = ↑(m - j)`.
Feeds the IH firing (`dim T_j ≤ ↑(n-1)`) and positivity from rep-dim. -/
theorem withBot_natCast_sub_of_add_eq (d : WithBot ℕ∞) (j m : ℕ)
    (h : d + ((j : ℕ) : WithBot ℕ∞) = ((m : ℕ) : WithBot ℕ∞)) :
    d = ((m - j : ℕ) : WithBot ℕ∞) := by
  have hj : ((j : ℕ) : WithBot ℕ∞) = ((((j : ℕ) : ℕ∞)) : WithBot ℕ∞) :=
    (WithBot.coe_natCast j).symm
  have hm : ((m : ℕ) : WithBot ℕ∞) = ((((m : ℕ) : ℕ∞)) : WithBot ℕ∞) :=
    (WithBot.coe_natCast m).symm
  rw [hj, hm] at h
  have hne : d ≠ ⊥ := by
    rintro rfl
    have hbot : (⊥ : WithBot ℕ∞) + ((((j : ℕ) : ℕ∞)) : WithBot ℕ∞) = ⊥ := by
      simp
    rw [hbot] at h
    exact WithBot.bot_ne_coe h
  obtain ⟨e, rfl⟩ := WithBot.ne_bot_iff_exists.mp hne
  rw [← WithBot.coe_add, WithBot.coe_eq_coe] at h
  have hetop : e ≠ ⊤ := by
    rintro rfl
    simp at h
  obtain ⟨e', rfl⟩ := ENat.ne_top_iff_exists.mp hetop
  rw [← Nat.cast_add] at h
  have hnm : e' + j = m := by
    exact_mod_cast h
  have he' : e' = m - j := by
    omega
  rw [he', WithBot.coe_natCast]

#print axioms withBot_natCast_sub_of_add_eq

/-- Dimension as a nat cast (`K_zero`:198-211 pattern, general `n`):
`dim S ≤ ↑n` gives `m₀'` with `dim S = ↑m₀'` and `m₀' ≤ n`. -/
theorem dim_eq_natCast_of_le (S : Type u) [CommRing S] [IsLocalRing S]
    [IsNoetherianRing S] (n : ℕ)
    (hdim : ringKrullDim S ≤ (((n : ℕ) : ℕ∞) : WithBot ℕ∞)) :
    ∃ m₀', ringKrullDim S = ((m₀' : ℕ) : WithBot ℕ∞) ∧ m₀' ≤ n := by
  have hne : ringKrullDim S ≠ ⊥ := by
    rw [← Module.supportDim_self_eq_ringKrullDim]
    exact (Module.supportDim_ne_bot_iff_nontrivial _ _).mpr inferInstance
  obtain ⟨d, hd⟩ := WithBot.ne_bot_iff_exists.mp hne
  rw [← hd, WithBot.coe_le_coe] at hdim
  have htop : d ≠ ⊤ := by
    rintro rfl
    simp at hdim
  obtain ⟨m₀', rfl⟩ := ENat.ne_top_iff_exists.mp htop
  rw [ENat.natCast_le_natCast] at hdim
  exact ⟨m₀', by rw [← hd, WithBot.coe_natCast], hdim⟩

#print axioms dim_eq_natCast_of_le

/-- Positivity: `dim = ↑k` with `k ≥ 1` gives `¬ KrullDimLE 0`
(the `:267-270` `krullDimLE_iff` pattern, both directions needed). -/
theorem not_krullDimLE_zero_of_dim_eq (T : Type u) [CommRing T] (k : ℕ)
    (hk : 1 ≤ k) (hdk : ringKrullDim T = ((k : ℕ) : WithBot ℕ∞)) :
    ¬ Ring.KrullDimLE 0 T := by
  intro hcon
  have hle0 := Ring.krullDimLE_iff.mp hcon
  rw [hdk] at hle0
  have g1 : ((k : ℕ) : WithBot ℕ∞) = ((((k : ℕ) : ℕ∞)) : WithBot ℕ∞) :=
    (WithBot.coe_natCast k).symm
  have g0 : ((0 : ℕ) : WithBot ℕ∞) = ((((0 : ℕ) : ℕ∞)) : WithBot ℕ∞) :=
    (WithBot.coe_natCast 0).symm
  rw [g1, g0, WithBot.coe_le_coe, ENat.natCast_le_natCast] at hle0
  omega

#print axioms not_krullDimLE_zero_of_dim_eq

/-! ## §B: the greedy step lemma (design note §2, pure assembly) -/

/-- The greedy step lemma (design note §2, full binders): a CM local ring of
positive dimension carries a regular element in `𝔪`, via A2 + C2-av-app
+ B-reg. Fires on every tower rung `T_j`. -/
theorem greedy_extend (T : Type u) [CommRing T] [IsLocalRing T]
    [IsNoetherianRing T]
    (hCM : CMQuotientPartial.IsCM T)
    (hpos : ¬ Ring.KrullDimLE 0 T)
    (hC3a : CMQuotientFull.C3aGapAll.{u})
    (hfinT : ringKrullDim T < ⊤) :
    ∃ y ∈ IsLocalRing.maximalIdeal T, IsSMulRegular T y := by
  have hmax : IsLocalRing.maximalIdeal T ∉ associatedPrimes T T :=
    CMQuotientFull.maximalIdeal_notMem_associatedPrimes_of_isCM T hCM
      hpos hC3a hfinT
  obtain ⟨y, hyI, hyavoid⟩ :=
    CMQuotientFull.exists_mem_maximal_avoid_ass T hmax
  exact ⟨y, hyI,
    CMQuotientFull.isSMulRegular_of_forall_notMem_associatedPrimes T y
      hyI hyavoid⟩

#print axioms greedy_extend

/-! ## §C: `IsRegular` across a ring equiv -/

/-- `IsRegular` transports across a ring equiv (possibly cross-universe)
to the mapped list. Standalone version of the C3:688-703 inline
pattern (via mathlib `AddEquiv.isRegular_congr` + `Forall₂`); needed for
the `x̃s`-regularity step of rep-concat. -/
theorem isRegular_map_ringEquiv {A : Type u} {B : Type uT} [CommRing A]
    [CommRing B] (e : A ≃+* B) (rs : List A) :
    IsRegular A rs ↔ IsRegular B (rs.map ⇑e) := by
  have h2 : List.Forall₂
      (fun (a : A) (b : B) => ∀ x, e.toAddEquiv (a • x) = b • e.toAddEquiv x)
      rs (rs.map ⇑e) := by
    rw [List.forall₂_map_right_iff, List.forall₂_same]
    intro a _ x
    change ⇑e (a • x) = (⇑e a) • ⇑e x
    rw [smul_eq_mul, smul_eq_mul, map_mul]
  exact e.toAddEquiv.isRegular_congr h2

#print axioms isRegular_map_ringEquiv

/-- A ring equiv between local rings preserves maximal-ideal membership
(units go to units, `𝔪` is the nonunits). Needed for the lift-maximality
step of rep-concat. -/
theorem mem_maximalIdeal_of_ringEquiv {A : Type u} {B : Type uT} [CommRing A]
    [IsLocalRing A] [CommRing B] [IsLocalRing B] (e : A ≃+* B) (x : A) :
    ⇑e x ∈ IsLocalRing.maximalIdeal B ↔ x ∈ IsLocalRing.maximalIdeal A := by
  rw [IsLocalRing.mem_maximalIdeal, IsLocalRing.mem_maximalIdeal,
    mem_nonunits_iff, mem_nonunits_iff]
  constructor
  · intro h hu
    exact h (hu.map e.toRingHom)
  · intro h huB
    apply h
    have hmap := huB.map e.symm.toRingHom
    have hsymm : e.symm.toRingHom (⇑e x) = x := e.symm_apply_apply x
    rwa [hsymm] at hmap

#print axioms mem_maximalIdeal_of_ringEquiv

/-! ## §D: the snoc lemma -/

/-- Appending a quotient-regular lift preserves regularity: from
`IsRegular S ys` and `IsSMulRegular (S ⧸ span ys) (mk y)`, get
`IsRegular S (ys ++ [y])`. The weak part is mathlib
`isWeaklyRegular_append_iff` + the module/ring-quotient bridge
(`quotEquivOfEq` + `algebraMap`); properness mirrors
`VariableInductionCM.singleton_isRegular_of_mem_maximal`. -/
theorem isRegular_snoc_of_isSMulRegular_quotient (S : Type u) [CommRing S]
    [IsLocalRing S] [IsNoetherianRing S] (ys : List S) (y : S)
    (hmem : ∀ r ∈ ys ++ [y], r ∈ IsLocalRing.maximalIdeal S)
    (hreg : IsRegular S ys)
    (hregy : IsSMulRegular (S ⧸ Ideal.span {x | x ∈ ys})
      (Ideal.Quotient.mk (Ideal.span {x | x ∈ ys}) y)) :
    IsRegular S (ys ++ [y]) := by
  rw [isRegular_iff]
  constructor
  · rw [isWeaklyRegular_append_iff]
    refine ⟨hreg.toIsWeaklyRegular, ?_⟩
    rw [isWeaklyRegular_singleton_iff]
    have hsmul : Ideal.ofList ys • (⊤ : Submodule S S) =
        ((Ideal.span {x | x ∈ ys}) : Submodule S S) := by
      rw [QuotientByRegularIsCM.smul_top_eq_self]
    let eₗ : (S ⧸ (Ideal.ofList ys • ⊤ : Submodule S S)) ≃ₗ[S]
        (S ⧸ Ideal.span {x | x ∈ ys}) :=
      Submodule.quotEquivOfEq _ _ hsmul
    rw [eₗ.isSMulRegular_congr y]
    have halg : ∀ z : (S ⧸ Ideal.span {x | x ∈ ys}),
        (Ideal.Quotient.mk (Ideal.span {x | x ∈ ys}) y) • z = y • z := by
      intro z
      rw [← Ideal.Quotient.algebraMap_eq]
      exact algebraMap_smul (S ⧸ Ideal.span {x | x ∈ ys}) y z
    have hfun : ((Ideal.Quotient.mk (Ideal.span {x | x ∈ ys}) y) • ·) =
        (y • ·) := funext halg
    unfold IsSMulRegular
    unfold IsSMulRegular at hregy
    rwa [hfun] at hregy
  · have hspan_le : Ideal.span {r | r ∈ ys ++ [y]} ≤
        IsLocalRing.maximalIdeal S := by
      rw [Ideal.span_le]
      intro r hr
      exact hmem r hr
    have hspan : Ideal.span {r | r ∈ ys ++ [y]} ≠ ⊤ :=
      ne_top_of_le_ne_top (Ideal.IsMaximal.ne_top inferInstance) hspan_le
    change (⊤ : Submodule S S) ≠ Ideal.span {r | r ∈ ys ++ [y]} • ⊤
    rw [Submodule.span_smul_eq, Submodule.set_smul_top_eq_span]
    exact Ne.symm hspan

#print axioms isRegular_snoc_of_isSMulRegular_quotient

/-! ## §E: rep-dim (exact dim of the tower rung) -/

/-- Rep-dim (design note §3, full binders): exact dim of the tower rung —
`dim (S ⧸ span ys) + len = dim S` for `ys` regular in `𝔪`. Strong
induction on a length bound (the C3-F7:827-842 shape); the cons case is
the C2-dim exact drop across the dq identification
(`hspancons`/`hspanmap` mirror C3:893-903), with mapped-list regularity
via C3:622 and arithmetic by `add_assoc`. -/
theorem tower_dim_add_length (S : Type u) [CommRing S] [IsLocalRing S]
    [IsNoetherianRing S] (ys : List S)
    (hmem : ∀ r ∈ ys, r ∈ IsLocalRing.maximalIdeal S)
    (hreg : IsRegular S ys)
    [IsLocalRing (S ⧸ Ideal.span {x | x ∈ ys})] :
    ringKrullDim (S ⧸ Ideal.span {x | x ∈ ys}) + ((ys.length : ℕ) : WithBot ℕ∞)
      = ringKrullDim S := by
  have hnil : ∀ (T : Type u) [CommRing T] [IsLocalRing T] [IsNoetherianRing T]
      [IsLocalRing (T ⧸ Ideal.span {x | x ∈ ([] : List T)})],
      ringKrullDim (T ⧸ Ideal.span {x | x ∈ ([] : List T)}) +
          ((((([] : List T).length : ℕ)) : WithBot ℕ∞))
        = ringKrullDim T := by
    intro T _ _ _ _
    have hspan : Ideal.span {x : T | x ∈ ([] : List T)} = ⊥ := by
      rw [CMPositiveDimHasDepth.memSet_nil, Ideal.span_empty]
    have e : (T ⧸ Ideal.span {x : T | x ∈ ([] : List T)}) ≃+* T :=
      (Ideal.quotEquivOfEq hspan).trans (RingEquiv.quotientBot T)
    have hdimT : ringKrullDim (T ⧸ Ideal.span {x : T | x ∈ ([] : List T)}) =
        ringKrullDim T :=
      ringKrullDim_eq_of_ringEquiv e
    rw [hdimT, List.length_nil, Nat.cast_zero, add_zero]
  suffices haux : ∀ (n : ℕ) (T : Type u) [CommRing T] [IsLocalRing T]
      [IsNoetherianRing T] (ls : List T)
      [IsLocalRing (T ⧸ Ideal.span {x | x ∈ ls})],
      ls.length ≤ n → (∀ r ∈ ls, r ∈ IsLocalRing.maximalIdeal T) →
      IsRegular T ls →
      ringKrullDim (T ⧸ Ideal.span {x | x ∈ ls}) +
          ((ls.length : ℕ) : WithBot ℕ∞)
        = ringKrullDim T by
    exact haux ys.length S ys le_rfl hmem hreg
  intro n
  induction n with
  | zero =>
    intro T _ _ _ ls _ hlen hmem hreg
    have hnil' : ls = [] :=
      List.length_eq_zero_iff.mp (Nat.le_zero.mp hlen)
    subst hnil'
    exact hnil T
  | succ n ih =>
    intro T _ _ _ ls _ hlen hmem hreg
    cases ls with
    | nil =>
      exact hnil T
    | cons a l =>
      rw [isRegular_cons_iff] at hreg
      obtain ⟨ha_reg, htail⟩ := hreg
      have ha_mem : a ∈ IsLocalRing.maximalIdeal T :=
        hmem a (List.mem_cons.mpr (Or.inl rfl))
      have hmem_tail : ∀ r ∈ l, r ∈ IsLocalRing.maximalIdeal T :=
        fun r hr => hmem r (List.mem_cons.mpr (Or.inr hr))
      have hspan_le : Ideal.span {a} ≤ IsLocalRing.maximalIdeal T := by
        rw [Ideal.span_le]
        intro y hy
        rw [Set.mem_singleton_iff] at hy
        rw [hy]
        exact ha_mem
      have hloc1 : IsLocalRing (T ⧸ Ideal.span {a}) :=
        QuotientByRegularIsCM.isLocalRing_quotient_of_le_maximal _ hspan_le
      have hdim1 : ringKrullDim (T ⧸ Ideal.span {a}) + 1 = ringKrullDim T :=
        ringKrullDim_quotient_span_singleton_succ_eq_ringKrullDim ha_reg ha_mem
      have hmem1 : ∀ s ∈ l.map (Ideal.Quotient.mk (Ideal.span {a})),
          s ∈ IsLocalRing.maximalIdeal (T ⧸ Ideal.span {a}) := by
        intro s hs
        rw [List.mem_map] at hs
        obtain ⟨r, hr, rfl⟩ := hs
        rw [QuotientByRegularIsCM.maximalIdeal_quotient_eq_map _ hspan_le]
        exact Ideal.mem_map_of_mem _ (hmem_tail r hr)
      have hreg1 : IsRegular (T ⧸ Ideal.span {a})
          (l.map (Ideal.Quotient.mk (Ideal.span {a}))) :=
        CMPositiveDimHasDepth.isRegular_spanQuotient_of_isRegular_quotSMulTop a l
          (Submodule.quotEquivOfEq _ _
            (CMPositiveDimHasDepth.smul_top_eq_span_singleton a))
          (fun s => Submodule.quotEquivOfEq_mk _ _
            (CMPositiveDimHasDepth.smul_top_eq_span_singleton a) s)
          htail
      have hlen1 : (l.map (Ideal.Quotient.mk (Ideal.span {a}))).length ≤ n := by
        rw [List.length_map]
        rw [List.length_cons] at hlen
        exact Nat.le_of_succ_le_succ hlen
      have hspanmap : Ideal.span {x : T ⧸ Ideal.span {a} | x ∈ l.map
            (Ideal.Quotient.mk (Ideal.span {a}))}
          = Ideal.map (Ideal.Quotient.mk (Ideal.span {a}))
            (Ideal.span {x : T | x ∈ l}) := by
        rw [CMPositiveDimHasDepth.memSet_map, CMPositiveDimHasDepth.map_span_image]
      have hspancons : Ideal.span {x : T | x ∈ a :: l}
          = Ideal.span {a} ⊔ Ideal.span {x : T | x ∈ l} := by
        rw [CMPositiveDimHasDepth.memSet_cons, Ideal.span_insert]
      have hle_map : Ideal.span {x : T ⧸ Ideal.span {a} | x ∈ l.map
            (Ideal.Quotient.mk (Ideal.span {a}))}
          ≤ IsLocalRing.maximalIdeal (T ⧸ Ideal.span {a}) := by
        rw [Ideal.span_le]
        intro s hs
        exact hmem1 s hs
      have hlocMap : IsLocalRing ((T ⧸ Ideal.span {a})
          ⧸ Ideal.span {x | x ∈ l.map
            (Ideal.Quotient.mk (Ideal.span {a}))}) :=
        QuotientByRegularIsCM.isLocalRing_quotient_of_le_maximal _ hle_map
      have hIH := ih (T ⧸ Ideal.span {a})
        (l.map (Ideal.Quotient.mk (Ideal.span {a}))) hlen1 hmem1 hreg1
      have eDQ : ((T ⧸ Ideal.span {a}) ⧸ Ideal.span {x | x ∈ l.map
            (Ideal.Quotient.mk (Ideal.span {a}))}) ≃+*
          (T ⧸ Ideal.span {x | x ∈ a :: l}) :=
        (Ideal.quotEquivOfEq hspanmap).trans
          ((DoubleQuot.quotQuotEquivQuotSup (Ideal.span {a})
            (Ideal.span {x : T | x ∈ l})).trans
            (Ideal.quotEquivOfEq hspancons).symm)
      have hdimDQ : ringKrullDim ((T ⧸ Ideal.span {a}) ⧸ Ideal.span {x | x ∈ l.map
            (Ideal.Quotient.mk (Ideal.span {a}))}) =
          ringKrullDim (T ⧸ Ideal.span {x | x ∈ a :: l}) :=
        ringKrullDim_eq_of_ringEquiv eDQ
      rw [List.length_map, hdimDQ] at hIH
      rw [List.length_cons]
      have hcast : (((l.length + 1 : ℕ)) : WithBot ℕ∞) =
          ((l.length : ℕ) : WithBot ℕ∞) + 1 := by
        rw [Nat.cast_add, Nat.cast_one]
      rw [hcast, ← add_assoc, hIH, hdim1]

#print axioms tower_dim_add_length

/-! ## §F: rep-concat statement + rep-tower -/

/-- `[RepConcat]` (the §3 hard core, exact design note full binders, proved by
`repConcat_proof` below): a regular-quotient-of-CI-quotient is CI. Given
`S ≃+* R_Q ⧸ span(rs₀)` and `T ≃+* S ⧸ span(ys)` with `ys` regular in
`𝔪_S`, `T` is a CI quotient of `R_Q` (witness list `rs₀ ++ x̃s` for
`R_Q`-lifts `x̃s` of `ys`, via the dq iso). The two identifications are
stated with `Nonempty` (C1Full `FirstReg`/`IsCIQuotient` convention) rather
than the design note's explicit equiv binders; the forms are interchangeable.
Proof sketch: `T ≃+*
(R_Q ⧸ I₀) ⧸ J ≃+* R_Q ⧸ (I₀ ⊔ J)` (`DoubleQuot.quotQuotEquivQuotSup`),
`I₀ ⊔ J = span(rs₀ ++ x̃s)` (`Ideal.map_span`; lifts via
`Ideal.Quotient.mk_surjective`; lift-maximality by C2-comp backwards),
regularity of `rs₀ ++ x̃s` by the append induction
(`isWeaklyRegular_append_iff` + `isRegular_map_ringEquiv` above + the
C3:622 bridge). -/
def RepConcat : Prop :=
  ∀ (m : ℕ) (K : Type uK) [Field K]
    (Q : Ideal (MvPolynomial (Fin m) K)) [Q.IsPrime]
    (S : Type uS) [CommRing S] [IsLocalRing S] [IsNoetherianRing S]
    (rs₀ : List (Localization.AtPrime Q)),
    (∀ r ∈ rs₀, r ∈ IsLocalRing.maximalIdeal (Localization.AtPrime Q)) →
    IsRegular (Localization.AtPrime Q) rs₀ →
    Nonempty (S ≃+* ((Localization.AtPrime Q) ⧸ Ideal.span {x | x ∈ rs₀})) →
    ∀ (ys : List S),
    (∀ r ∈ ys, r ∈ IsLocalRing.maximalIdeal S) →
    IsRegular S ys →
    ∀ (T : Type uT) [CommRing T] [IsLocalRing T] [IsNoetherianRing T],
    Nonempty (T ≃+* (S ⧸ Ideal.span {x | x ∈ ys})) →
    CMQuotientFull.IsCIQuotient m K Q T

/-- Rep-tower (design note §3, corollary of rep-concat): each tower rung `T_j`
is a CI quotient. Destructure `hCI`, apply `RepConcat` with
`⟨RingEquiv.refl _⟩` (local/Noetherian instances via C2-loc +
mathlib quotient instance). -/
theorem ciQuotient_tower_step (m : ℕ) (K : Type uK) [Field K]
    (Q : Ideal (MvPolynomial (Fin m) K)) [Q.IsPrime]
    (S : Type uS) [CommRing S] [IsLocalRing S] [IsNoetherianRing S]
    (hRep : RepConcat.{uK, uS, uS})
    (hCI : CMQuotientFull.IsCIQuotient m K Q S)
    (ys : List S)
    (hmem : ∀ r ∈ ys, r ∈ IsLocalRing.maximalIdeal S)
    (hreg : IsRegular S ys) :
    CMQuotientFull.IsCIQuotient m K Q
      (S ⧸ Ideal.span {x | x ∈ ys}) := by
  obtain ⟨rs₀, hmem₀, hreg₀, ⟨eS⟩⟩ := hCI
  have hspan_le : Ideal.span {x | x ∈ ys} ≤ IsLocalRing.maximalIdeal S := by
    rw [Ideal.span_le]
    intro r hr
    exact hmem r hr
  have _hloc := QuotientByRegularIsCM.isLocalRing_quotient_of_le_maximal _ hspan_le
  exact hRep m K Q S rs₀ hmem₀ hreg₀ ⟨eS⟩ ys hmem hreg _ ⟨RingEquiv.refl _⟩

#print axioms ciQuotient_tower_step

/-! ## §G: main theorem (strong induction + inner greedy construction) -/

/-- Main theorem (design note §1): the greedy tower, conditional on
`[RepConcat]` (+ the proved `[FirstReg]`/`[C3aGapAll]` taken as
hypotheses; `C3aGapAll` closed via `AssociatedPrimes.FiniteDimDischarge`, `hC3a`
vestigial). Strong induction on `n` (`Nat.strongRecOn`); the outer IH
fires at `n - 1` on each rung `T_j` (`j ≥ 1`) via rep-tower +
`K_of_greedy`, giving `IsCM T_j`; the first element comes from the
domain case (`rs₀ = []`) or `[FirstReg]`; later elements extend via
`greedy_extend` + `mk`-lift + the snoc lemma. Stated on the universe
diagonal (see header note). -/
theorem greedy_of_residuals_of_repConcat (hRep : RepConcat.{uK, uS, uS}) :
    ∀ n, CMQuotientFull.GreedyOfResiduals.{uK, uS, uS, uK, uS} n := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    unfold CMQuotientFull.GreedyOfResiduals
    intro hFR hC3a
    unfold CMQuotientFull.GreedyWitness
    intro m K _ Q _ S _ _ _ hCI hdim
    obtain ⟨rs₀, hmem₀, hreg₀, ⟨eS⟩⟩ := hCI
    obtain ⟨m₀', hm₀'eq, hm₀'le⟩ := dim_eq_natCast_of_le S n hdim
    by_cases hm₀'0 : m₀' = 0
    · subst hm₀'0
      refine ⟨[], ?_, VariableInductionCM.empty_isRegular, ?_⟩
      · intro r hr
        exact (List.not_mem_nil hr).elim
      · simp only [List.length_nil]
        rw [hm₀'eq]
    · have hm₀'pos : 1 ≤ m₀' := Nat.one_le_iff_ne_zero.mpr hm₀'0
      have hn1 : n - 1 < n := by
        omega
      have inner : ∀ j, j ≤ m₀' → ∃ ys : List S,
          ys.length = j ∧ (∀ r ∈ ys, r ∈ IsLocalRing.maximalIdeal S) ∧
            IsRegular S ys := by
        intro j
        induction j with
        | zero =>
          intro _
          exact ⟨[], rfl, fun r hr => (List.not_mem_nil hr).elim,
            VariableInductionCM.empty_isRegular⟩
        | succ j ihj =>
          intro hle
          have hle' : j ≤ m₀' := Nat.le_of_succ_le hle
          obtain ⟨ys, hlen, hmem, hreg⟩ := ihj hle'
          by_cases hj0 : j = 0
          · subst hj0
            have hposS :=
              not_krullDimLE_zero_of_dim_eq S m₀' hm₀'pos hm₀'eq
            have hex : ∃ z ∈ IsLocalRing.maximalIdeal S, IsSMulRegular S z := by
              by_cases hrs0 : rs₀ = []
              · subst hrs0
                exact CMQuotientFull.firstReg_domain_case m K Q S eS
                  hposS
              · exact hFR m K Q S rs₀ hrs0 hmem₀ hreg₀ ⟨eS⟩ hposS
            obtain ⟨z, hzmem, hzreg⟩ := hex
            refine ⟨[z], by simp, ?_,
              VariableInductionCM.singleton_isRegular_of_mem_maximal hzmem hzreg⟩
            intro r hr
            obtain rfl := List.mem_singleton.mp hr
            exact hzmem
          · have hjpos : 1 ≤ j := Nat.one_le_iff_ne_zero.mpr hj0
            have hspan_le : Ideal.span {x | x ∈ ys} ≤
                IsLocalRing.maximalIdeal S := by
              rw [Ideal.span_le]
              intro r hr
              exact hmem r hr
            have hlocT : IsLocalRing (S ⧸ Ideal.span {x | x ∈ ys}) :=
              QuotientByRegularIsCM.isLocalRing_quotient_of_le_maximal _ hspan_le
            have hrep_dim := tower_dim_add_length S ys hmem hreg
            rw [hlen, hm₀'eq] at hrep_dim
            have hdimT :
                ringKrullDim (S ⧸ Ideal.span {x | x ∈ ys}) =
                  ((m₀' - j : ℕ) : WithBot ℕ∞) :=
              withBot_natCast_sub_of_add_eq _ j m₀' hrep_dim
            have hmj_le : m₀' - j ≤ n - 1 := by
              omega
            have hmj_pos : 1 ≤ m₀' - j := by
              omega
            have hGW : CMQuotientFull.GreedyWitness.{uK, uS} (n - 1) :=
              ih (n - 1) hn1 hFR hC3a
            have hK := CMQuotientFull.K_of_greedy (n - 1) hGW
            have hCI_T := ciQuotient_tower_step m K Q S hRep
              ⟨rs₀, hmem₀, hreg₀, ⟨eS⟩⟩ ys hmem hreg
            have hdimT_le : ringKrullDim (S ⧸ Ideal.span {x | x ∈ ys}) ≤
                (((n - 1 : ℕ) : ℕ∞) : WithBot ℕ∞) := by
              rw [hdimT]
              have g1 : ((m₀' - j : ℕ) : WithBot ℕ∞) =
                  ((((m₀' - j : ℕ) : ℕ∞)) : WithBot ℕ∞) :=
                (WithBot.coe_natCast _).symm
              rw [g1, WithBot.coe_le_coe, ENat.natCast_le_natCast]
              exact hmj_le
            have hCM_T := hK m K Q (S ⧸ Ideal.span {x | x ∈ ys}) hCI_T hdimT_le
            have hposT :=
              not_krullDimLE_zero_of_dim_eq _ (m₀' - j) hmj_pos hdimT
            have hfinTj : ringKrullDim (S ⧸ Ideal.span {x | x ∈ ys}) < ⊤ := by
              rw [hdimT]
              exact WithBot.coe_lt_coe.mpr (ENat.natCast_lt_top _)
            obtain ⟨y, hymem, hyreg⟩ := greedy_extend _ hCM_T hposT hC3a hfinTj
            obtain ⟨ytil, hytil⟩ := Ideal.Quotient.mk_surjective y
            have hytil_mem : ytil ∈ IsLocalRing.maximalIdeal S := by
              apply QuotientByRegularIsCM.mem_of_mk_mem_map _ hspan_le
              have hmap := QuotientByRegularIsCM.maximalIdeal_quotient_eq_map
                (Ideal.span {x | x ∈ ys}) hspan_le
              rw [hytil, ← hmap]
              exact hymem
            have hyreg_mk : IsSMulRegular (S ⧸ Ideal.span {x | x ∈ ys})
                (Ideal.Quotient.mk (Ideal.span {x | x ∈ ys}) ytil) := by
              rwa [hytil]
            have hmem_snoc : ∀ r ∈ ys ++ [ytil],
                r ∈ IsLocalRing.maximalIdeal S := by
              intro r hr
              rw [List.mem_append] at hr
              cases hr with
              | inl h =>
                exact hmem r h
              | inr h =>
                obtain rfl := List.mem_singleton.mp h
                exact hytil_mem
            have hreg_snoc :=
              isRegular_snoc_of_isSMulRegular_quotient S ys ytil hmem_snoc hreg
                hyreg_mk
            refine ⟨ys ++ [ytil], ?_, hmem_snoc, hreg_snoc⟩
            rw [List.length_append, hlen, List.length_singleton]
      obtain ⟨ys, hlen, hmem, hreg⟩ := inner m₀' le_rfl
      refine ⟨ys, hmem, hreg, ?_⟩
      rw [hlen, hm₀'eq]

#print axioms greedy_of_residuals_of_repConcat

/-! ## §H: rep-concat proof (closing `[RepConcat]`) -/

/-- Quotient across an equiv (possibly cross-universe): `S ⧸ J ≃+*
A ⧸ map e J`. Manual `lift` construction (`ringHom_ext` for the inverse
laws); the backward side condition inverts ideal membership via
surjectivity (`mem_map_iff_of_surjective`). -/
noncomputable def quotEquivOfEquiv {S : Type u} {A : Type uT} [CommRing S]
    [CommRing A] (e : S ≃+* A) (J : Ideal S) :
    (S ⧸ J) ≃+* (A ⧸ Ideal.map e.toRingHom J) := by
  have hsurj : Function.Surjective e.toRingHom :=
    fun b => ⟨e.symm b, e.apply_symm_apply b⟩
  refine RingEquiv.ofRingHom
    (Ideal.Quotient.lift J
      ((Ideal.Quotient.mk (Ideal.map e.toRingHom J)).comp e.toRingHom) ?_)
    (Ideal.Quotient.lift (Ideal.map e.toRingHom J)
      ((Ideal.Quotient.mk J).comp e.symm.toRingHom) ?_) ?_ ?_
  · intro x hx
    rw [RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.mem_map_of_mem _ hx
  · intro y hy
    rw [RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem]
    obtain ⟨x, hx, rfl⟩ :=
      (Ideal.mem_map_iff_of_surjective e.toRingHom hsurj).mp hy
    have hsymm : e.symm.toRingHom (e.toRingHom x) = x :=
      e.symm_apply_apply x
    rw [hsymm]
    exact hx
  · apply Ideal.Quotient.ringHom_ext
    ext q
    simp only [RingHom.comp_apply, Ideal.Quotient.lift_mk, RingHom.id_apply]
    have happ : e.toRingHom (e.symm.toRingHom q) = q :=
      e.apply_symm_apply q
    rw [happ]
  · apply Ideal.Quotient.ringHom_ext
    ext s
    simp only [RingHom.comp_apply, Ideal.Quotient.lift_mk, RingHom.id_apply]
    have happ' : e.symm.toRingHom (e.toRingHom s) = s :=
      e.symm_apply_apply s
    rw [happ']

#print axioms quotEquivOfEquiv

/-- `IsRegular` of an append from the rung: from `IsRegular R rs₀` and
`IsRegular (R ⧸ span rs₀)` on the `mk`-mapped tail, get `IsRegular R
(rs₀ ++ xs)` (all in `𝔪` for properness). Weak part via
`isWeaklyRegular_append_iff` + the module-equiv bridge +
`isWeaklyRegular_map_algebraMap_iff`; properness mirrors
`VariableInductionCM.singleton_isRegular_of_mem_maximal`. -/
theorem isRegular_append_of_isRegular_quotient (R : Type u) [CommRing R]
    [IsLocalRing R] (rs₀ xs : List R)
    (hmem : ∀ r ∈ rs₀ ++ xs, r ∈ IsLocalRing.maximalIdeal R)
    (hreg₀ : IsRegular R rs₀)
    (hregQ : IsRegular (R ⧸ Ideal.span {x | x ∈ rs₀})
      (xs.map (Ideal.Quotient.mk (Ideal.span {x | x ∈ rs₀})))) :
    IsRegular R (rs₀ ++ xs) := by
  rw [isRegular_iff]
  constructor
  · rw [isWeaklyRegular_append_iff]
    refine ⟨hreg₀.toIsWeaklyRegular, ?_⟩
    have hsmul : Ideal.ofList rs₀ • (⊤ : Submodule R R) =
        ((Ideal.span {x | x ∈ rs₀}) : Submodule R R) := by
      rw [QuotientByRegularIsCM.smul_top_eq_self]
    let eₗ : (R ⧸ (Ideal.ofList rs₀ • ⊤ : Submodule R R)) ≃ₗ[R]
        (R ⧸ Ideal.span {x | x ∈ rs₀}) :=
      Submodule.quotEquivOfEq _ _ hsmul
    have hweakQ := hregQ.toIsWeaklyRegular
    rw [eₗ.isWeaklyRegular_congr xs,
      ← isWeaklyRegular_map_algebraMap_iff
        (R ⧸ Ideal.span {x | x ∈ rs₀}) (R ⧸ Ideal.span {x | x ∈ rs₀}) xs,
      Ideal.Quotient.algebraMap_eq]
    exact hweakQ
  · have hspan_le : Ideal.span {r | r ∈ rs₀ ++ xs} ≤
        IsLocalRing.maximalIdeal R := by
      rw [Ideal.span_le]
      intro r hr
      exact hmem r hr
    have hspan : Ideal.span {r | r ∈ rs₀ ++ xs} ≠ ⊤ :=
      ne_top_of_le_ne_top (Ideal.IsMaximal.ne_top inferInstance) hspan_le
    change (⊤ : Submodule R R) ≠ Ideal.span {r | r ∈ rs₀ ++ xs} • ⊤
    rw [Submodule.span_smul_eq, Submodule.set_smul_top_eq_span]
    exact Ne.symm hspan

#print axioms isRegular_append_of_isRegular_quotient

/-- Rep-concat (design note §3): a regular-quotient-of-CI-quotient is CI.
`R_Q`-lifts `x̃s` of `ys` (`mk`-surjectivity, maximal by C2-comp
backwards); witness list `rs₀ ++ x̃s`; the identification via
`quotEquivOfEquiv` + the dq iso (`DoubleQuot.quotQuotEquivQuotSup`) +
span-append algebra (`Ideal.map_span`, `Ideal.ofList_append`);
regularity by `isRegular_append_of_isRegular_quotient` +
`isRegular_map_ringEquiv`. -/
theorem repConcat_proof : RepConcat.{uK, uS, uT} := by
  intro m K _ Q _ S _ _ _ rs₀ hmem₀ hreg₀ hNeS ys hmem hreg T _ _ _ hNeT
  obtain ⟨eS⟩ := hNeS
  obtain ⟨eT⟩ := hNeT
  have hI₀_le : Ideal.span {x : Localization.AtPrime Q | x ∈ rs₀} ≤
      IsLocalRing.maximalIdeal (Localization.AtPrime Q) := by
    rw [Ideal.span_le]
    intro r hr
    exact hmem₀ r hr
  have hlocQ : IsLocalRing
      ((Localization.AtPrime Q) ⧸ Ideal.span {x | x ∈ rs₀}) :=
    QuotientByRegularIsCM.isLocalRing_quotient_of_le_maximal _ hI₀_le
  have hsurj : ∀ q : ((Localization.AtPrime Q) ⧸
        Ideal.span {x : Localization.AtPrime Q | x ∈ rs₀}),
      ∃ r : Localization.AtPrime Q,
        Ideal.Quotient.mk
          (Ideal.span {x : Localization.AtPrime Q | x ∈ rs₀}) r = q :=
    Ideal.Quotient.mk_surjective
  choose xtilde hxtilde using (fun y => hsurj (eS y))
  have hmapQ := QuotientByRegularIsCM.maximalIdeal_quotient_eq_map
    (Ideal.span {x : Localization.AtPrime Q | x ∈ rs₀}) hI₀_le
  have hmem_lift : ∀ r ∈ ys.map xtilde,
      r ∈ IsLocalRing.maximalIdeal (Localization.AtPrime Q) := by
    intro r hr
    rw [List.mem_map] at hr
    obtain ⟨y, hy, rfl⟩ := hr
    have heSy := (mem_maximalIdeal_of_ringEquiv (A := S) (B := ((Localization.AtPrime Q) ⧸ Ideal.span {x | x ∈ rs₀})) eS y).mpr (hmem y hy)
    have hmem' : Ideal.Quotient.mk
          (Ideal.span {x : Localization.AtPrime Q | x ∈ rs₀}) (xtilde y) ∈
        Ideal.map
          (Ideal.Quotient.mk
            (Ideal.span {x : Localization.AtPrime Q | x ∈ rs₀}))
          (IsLocalRing.maximalIdeal (Localization.AtPrime Q)) := by
      rw [hxtilde y, ← hmapQ]
      exact heSy
    exact QuotientByRegularIsCM.mem_of_mk_mem_map _ hI₀_le _ hmem'
  have hmem_concat : ∀ r ∈ rs₀ ++ ys.map xtilde,
      r ∈ IsLocalRing.maximalIdeal (Localization.AtPrime Q) := by
    intro r hr
    rw [List.mem_append] at hr
    cases hr with
    | inl h => exact hmem₀ r h
    | inr h => exact hmem_lift r h
  have hregQ0 : IsRegular
      ((Localization.AtPrime Q) ⧸ Ideal.span {x | x ∈ rs₀}) (ys.map ⇑eS) :=
    (isRegular_map_ringEquiv (A := S) (B := ((Localization.AtPrime Q) ⧸ Ideal.span {x | x ∈ rs₀})) eS ys).mp hreg
  have hfun : (fun y => Ideal.Quotient.mk
        (Ideal.span {x : Localization.AtPrime Q | x ∈ rs₀}) (xtilde y)) = ⇑eS := by
    funext y
    exact hxtilde y
  have hfun' : (fun y => Ideal.Quotient.mk
        (Ideal.span {x : Localization.AtPrime Q | x ∈ rs₀}) (xtilde y)) =
      ((Ideal.Quotient.mk
        (Ideal.span {x : Localization.AtPrime Q | x ∈ rs₀})) ∘ xtilde) := rfl
  have hmap_eq : (ys.map xtilde).map
        (Ideal.Quotient.mk
          (Ideal.span {x : Localization.AtPrime Q | x ∈ rs₀})) =
      ys.map ⇑eS := by
    rw [List.map_map, ← hfun', hfun]
  have hregQ : IsRegular
      ((Localization.AtPrime Q) ⧸ Ideal.span {x | x ∈ rs₀})
      ((ys.map xtilde).map (Ideal.Quotient.mk
        (Ideal.span {x : Localization.AtPrime Q | x ∈ rs₀}))) := by
    rw [hmap_eq]
    exact hregQ0
  have hreg_concat : IsRegular (Localization.AtPrime Q)
      (rs₀ ++ ys.map xtilde) :=
    isRegular_append_of_isRegular_quotient _ rs₀ (ys.map xtilde) hmem_concat
      hreg₀ hregQ
  have hmap_span : Ideal.map eS.toRingHom (Ideal.span {x : S | x ∈ ys}) =
      Ideal.map
        (Ideal.Quotient.mk
          (Ideal.span {x : Localization.AtPrime Q | x ∈ rs₀}))
        (Ideal.span {x : Localization.AtPrime Q | x ∈ ys.map xtilde}) := by
    simp only [Ideal.map_span]
    have hmemset : ({x : Localization.AtPrime Q | x ∈ ys.map xtilde}) =
        xtilde '' {x : S | x ∈ ys} := by
      ext y
      change (y ∈ ys.map xtilde) ↔ y ∈ xtilde '' {x | x ∈ ys}
      rw [List.mem_map, Set.mem_image]
      exact Iff.rfl
    rw [hmemset, Set.image_image]
    have hfun2 : (fun x => Ideal.Quotient.mk
        (Ideal.span {x : Localization.AtPrime Q | x ∈ rs₀}) (xtilde x)) =
        ⇑eS.toRingHom := hfun
    rw [hfun2]
  have hsup_span : Ideal.span {x : Localization.AtPrime Q | x ∈ rs₀} ⊔
        Ideal.span {x : Localization.AtPrime Q | x ∈ ys.map xtilde} =
      Ideal.span {x : Localization.AtPrime Q | x ∈ rs₀ ++ ys.map xtilde} :=
    (Ideal.ofList_append rs₀ (ys.map xtilde)).symm
  haveI : RingHomSurjective eS.toRingHom := ⟨eS.surjective⟩
  have eStep := @quotEquivOfEquiv S ((Localization.AtPrime Q) ⧸ Ideal.span {x | x ∈ rs₀}) _ (Ideal.Quotient.commRing _) eS (Ideal.span {x : S | x ∈ ys})
  have eFinal : T ≃+* ((Localization.AtPrime Q) ⧸
      Ideal.span {x : Localization.AtPrime Q | x ∈ rs₀ ++ ys.map xtilde}) :=
    eT.trans (eStep.trans ((Ideal.quotEquivOfEq hmap_span).trans
      ((DoubleQuot.quotQuotEquivQuotSup
        (Ideal.span {x : Localization.AtPrime Q | x ∈ rs₀})
        (Ideal.span {x : Localization.AtPrime Q | x ∈ ys.map xtilde})).trans
        (Ideal.quotEquivOfEq hsup_span))))
  exact ⟨rs₀ ++ ys.map xtilde, hmem_concat, hreg_concat, ⟨eFinal⟩⟩

#print axioms repConcat_proof

/-- Main theorem (design note §1), unconditional on tower residuals: the greedy
tower closed by `repConcat_proof`. `FirstReg` + `C3aGapAll` (the proved
residuals) supply the per-step regular elements; `K_of_greedy` closes
each `K n`. Stated on the universe diagonal (see header note). -/
theorem greedy_of_residuals : ∀ n,
    CMQuotientFull.GreedyOfResiduals.{uK, uS, uS, uK, uS} n := by
  intro n
  unfold CMQuotientFull.GreedyOfResiduals
  intro hFR hC3a
  exact greedy_of_residuals_of_repConcat repConcat_proof n hFR hC3a

#print axioms greedy_of_residuals

end CMQuotientGreedyTower
end Appendix_FixedPoint.BezoutChain
end EvolutionAlgebras
