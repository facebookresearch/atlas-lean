/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.LinearAlgebra.SmithNormalForm
public import Mathlib.Algebra.DirectSum.Basic
public import Mathlib.Algebra.Group.Equiv.Basic
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Data.Finset.Sort
public import Mathlib.Data.ZMod.QuotientRing
public import Mathlib.GroupTheory.Finiteness
public import Mathlib.LinearAlgebra.Basis.Submodule
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.Finsupp.Defs
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Mathlib.LinearAlgebra.Quotient.Defs
public import Mathlib.LinearAlgebra.Quotient.Pi
public import Mathlib.RingTheory.Finiteness.Defs

@[expose] public section

open scoped DirectSum

/-!
# Invariant factors of finitely generated abelian groups

This file ports the fundamental theorem of finitely generated abelian groups
in invariant-factor form from `v1/Atlas/AlgebraNotes/code/AbelianGroups.lean`.

## Main results

* `exists_invariant_factor_decomposition`: every finitely generated abelian
  group is the product of a free abelian group and a finite product of cyclic
  groups `ZMod (d i)` with `1 < d i` and `d i ∣ d j` for `i ≤ j`.
* `exists_invariant_factor_decomposition_finite`: the finite case, a product
  of cyclic groups with invariant factors.

The proof in v1 of the invariant-factor conversion
(`elementary_divisors_to_invariant_factors`) is left unproved there; the proof
here instead takes a presentation of `A` by a finite free abelian group and
applies the Smith normal form with divisibility chain
(`Submodule.exists_smith_normal_form_dvd_chain`), then computes the quotient
by the diagonal submodule. The elementary-divisor form
(`AddCommGroup.equiv_free_prod_directSum_zmod`) is not used.
-/

/-- Divisibility propagates along a chain of consecutive divisibilities. -/
private theorem dvd_of_dvd_chain {r : ℕ} {a : Fin r → ℤ}
    (hchain : ∀ (i : ℕ) (hi1 : i < r) (hi2 : i + 1 < r),
      a ⟨i, hi1⟩ ∣ a ⟨i + 1, hi2⟩)
    {i j : Fin r} (hij : i ≤ j) : a i ∣ a j := by
  have P : ∀ t : ℕ, ∀ j : Fin r, j.val = i.val + t → a i ∣ a j := by
    intro t
    induction t with
    | zero =>
      intro j hj
      have h : i = j := Fin.ext (by omega)
      subst h
      exact dvd_refl _
    | succ t ih =>
      intro j hj
      let j' : Fin r := ⟨i.val + t, by omega⟩
      have h1 : a i ∣ a j' := ih j' rfl
      have h2 : a j' ∣ a j := by
        have hstep : a ⟨j.val - 1, by omega⟩ ∣ a ⟨j.val - 1 + 1, by omega⟩ :=
          hchain (j.val - 1) (by omega) (by omega)
        have e1 : (⟨j.val - 1, by omega⟩ : Fin r) = j' :=
          Fin.ext (by show j.val - 1 = i.val + t; omega)
        have e2 : (⟨j.val - 1 + 1, by omega⟩ : Fin r) = j :=
          Fin.ext (by show j.val - 1 + 1 = j.val; omega)
        rwa [e1, e2] at hstep
      exact dvd_trans h1 h2
  exact P (j.val - i.val) j (by omega)

/-- Dropping the trivial factors from a product of cyclic groups. If
`a i` has `natAbs = 1` off `s`, the product over all of `Fin r` is the
product over the subtype `s`. -/
private def piCongrDropTrivial {r : ℕ} {a : Fin r → ℤ}
    (s : Finset (Fin r)) (hs : ∀ i ∉ s, (a i).natAbs = 1) :
    (Π i : Fin r, ZMod (a i).natAbs) ≃+ Π i : ↥s, ZMod (a i).natAbs where
  toFun x := fun i => x i
  invFun y := fun i => if h : i ∈ s then y ⟨i, h⟩ else 0
  left_inv x := by
    funext i
    show (if h : i ∈ s then x i else 0) = x i
    split_ifs with h
    · rfl
    · have h1 : (a i).natAbs = 1 := hs i h
      have hsub : Subsingleton (ZMod (a i).natAbs) := h1 ▸ inferInstance
      exact @Subsingleton.elim _ hsub _ _
  right_inv y := by
    funext i
    show (if h : (i : Fin r) ∈ s then y ⟨(i : Fin r), h⟩ else 0) = y i
    split_ifs with h
    · congr 1
    · exact absurd i.2 h
  map_add' x y := rfl

/-- Reindexing a product over a finset-subtype by the increasing bijection
`Finset.orderIsoOfFin`. -/
private def piCongrOrderIsoOfFin {r : ℕ} {a : Fin r → ℤ}
    (s : Finset (Fin r)) :
    (Π i : ↥s, ZMod (a i).natAbs) ≃+
      Π j : Fin s.card, ZMod (a (s.orderIsoOfFin rfl j : Fin r)).natAbs :=
  { (Equiv.piCongrLeft (fun i : ↥s => ZMod (a i).natAbs)
      (s.orderIsoOfFin rfl).toEquiv).symm with
    map_add' := by
      intro x y
      funext j
      rfl }

/-- Splitting a product of quotients over `Fin m` along an equivalence
`Fin r ⊕ Fin (m - r) ≃ Fin m`. -/
private def piQuotientSplit {m r : ℕ} (D : Fin m → Submodule ℤ ℤ)
    (e' : Fin r ⊕ Fin (m - r) ≃ Fin m) :
    (Π j : Fin m, ℤ ⧸ D j) ≃+
      (Π i : Fin r, ℤ ⧸ D (e' (Sum.inl i))) ×
        (Π t : Fin (m - r), ℤ ⧸ D (e' (Sum.inr t))) :=
  { (Equiv.piCongrLeft (fun j => ℤ ⧸ D j) e').symm.trans
      (Equiv.sumPiEquivProdPi (fun x => ℤ ⧸ D (e' x))) with
    map_add' := by
      intro x y
      exact Prod.ext rfl rfl }

/-- The coordinates of a combination of Smith-basis vectors of `N`. -/
private theorem equivFun_sum_basis {n r : ℕ} (hrm : r ≤ n)
    {N : Submodule ℤ (Fin n → ℤ)} {bM : Module.Basis (Fin n) ℤ (Fin n → ℤ)}
    {bN : Module.Basis (Fin r) ℤ N} {a : Fin r → ℤ}
    (hsnf : ∀ i, (bN i : Fin n → ℤ) = a i • bM (Fin.castLE hrm i)) (c : Fin r → ℤ) :
    bM.equivFun (∑ i, c i • (bN i : Fin n → ℤ)) =
      ∑ i, (c i * a i) • (Pi.single (Fin.castLE hrm i) (1 : ℤ) : Fin n → ℤ) := by
  have hself : ∀ i : Fin r,
      bM.equivFun (bM (Fin.castLE hrm i)) = Pi.single (Fin.castLE hrm i) (1 : ℤ) := by
    intro i
    funext k
    rw [Module.Basis.equivFun_self, Pi.single_apply]
    by_cases h : Fin.castLE hrm i = k
    · simp [h]
    · simp [h, Ne.symm h]
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hsnf, smul_smul, map_smul, hself]

/-- Evaluating a sum of coordinate-single vectors. -/
private theorem sum_singles_apply {n r : ℕ} (hrm : r ≤ n) (a : Fin r → ℤ)
    (c : Fin r → ℤ) (j : Fin n) :
    (∑ i, (c i * a i) • (Pi.single (Fin.castLE hrm i) (1 : ℤ) : Fin n → ℤ)) j =
      if h : j.val < r then c ⟨j.val, h⟩ * a ⟨j.val, h⟩ else 0 := by
  rw [Finset.sum_apply]
  split_ifs with hj
  · rw [Finset.sum_eq_single ⟨j.val, hj⟩]
    · rw [Pi.smul_apply, Pi.single_apply]
      by_cases h : j = Fin.castLE hrm ⟨j.val, hj⟩
      · rw [ite_eq_left h]; simp
      · exact absurd (Fin.ext rfl) h
    · intro i _ hi
      have hne : ¬ (j = Fin.castLE hrm i) := by
        intro heq
        apply hi
        exact Fin.ext (congrArg Fin.val heq).symm
      rw [Pi.smul_apply, Pi.single_apply]
      by_cases h : j = Fin.castLE hrm i
      · exact absurd h hne
      · rw [ite_eq_right h]; simp
    · simp
  · rw [Finset.sum_eq_zero]
    intro i _
    have hne : ¬ (j = Fin.castLE hrm i) := by
      intro heq
      have hval : j.val = (Fin.castLE hrm i).val := congrArg Fin.val heq
      have hval2 : (Fin.castLE hrm i).val = i.val := rfl
      have hi2 := i.2
      omega
    rw [Pi.smul_apply, Pi.single_apply]
    by_cases h : j = Fin.castLE hrm i
    · exact absurd h hne
    · rw [ite_eq_right h]; simp

/-- The image of `N` under the coordinate equivalence of the Smith basis is
the product of the diagonal submodules. -/
private theorem map_basisEquivFun_eq_pi {n r : ℕ} (hrm : r ≤ n)
    {N : Submodule ℤ (Fin n → ℤ)} {bM : Module.Basis (Fin n) ℤ (Fin n → ℤ)}
    {bN : Module.Basis (Fin r) ℤ N} {a : Fin r → ℤ}
    (hsnf : ∀ i, (bN i : Fin n → ℤ) = a i • bM (Fin.castLE hrm i)) :
    Submodule.map (bM.equivFun : (Fin n → ℤ) →ₗ[ℤ] (Fin n → ℤ)) N =
      Submodule.pi Set.univ
        (fun j : Fin n => if h : j.val < r then Submodule.span ℤ {a ⟨j.val, h⟩} else ⊥) := by
  ext x
  simp only [Submodule.mem_map, Submodule.mem_pi, Set.mem_univ, true_implies]
  constructor
  · rintro ⟨y, hy, rfl⟩ j
    obtain ⟨c, hc⟩ := (Module.Basis.mem_submodule_iff' bN).mp hy
    have key : bM.equivFun y = ∑ i, (c i * a i) • (Pi.single (Fin.castLE hrm i) (1 : ℤ) : Fin n → ℤ) := by
      rw [hc]
      exact equivFun_sum_basis hrm hsnf c
    show bM.equivFun y j ∈ (if h : j.val < r then Submodule.span ℤ {a ⟨j.val, h⟩} else ⊥)
    rw [key, sum_singles_apply hrm a c j]
    by_cases hj : j.val < r
    · rw [dite_eq_left hj, dite_eq_left hj]
      exact Submodule.mem_span_singleton.mpr ⟨c ⟨j.val, hj⟩, by rw [smul_eq_mul]⟩
    · rw [dite_eq_right hj, dite_eq_right hj]
      exact Submodule.zero_mem _
  · intro hx
    -- Choose coefficients for the coordinates in the range of `castLE`.
    have hxi : ∀ i : Fin r,
        x (Fin.castLE hrm i) ∈ Submodule.span ℤ {a i} := by
      intro i
      have h := hx (Fin.castLE hrm i)
      rw [dite_eq_left (show (Fin.castLE hrm i).val < r from i.2)] at h
      have heq : a ⟨(Fin.castLE hrm i).val, i.2⟩ = a i := congrArg a (Fin.ext rfl)
      rwa [heq] at h
    choose c hc using fun i => (Submodule.mem_span_singleton.mp (hxi i))
    refine ⟨∑ i, c i • (bN i : Fin n → ℤ), ?_, ?_⟩
    · exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (bN i).2
    · show bM.equivFun (∑ i, c i • (bN i : Fin n → ℤ)) = x
      rw [equivFun_sum_basis hrm hsnf c]
      funext j
      rw [sum_singles_apply hrm a c j]
      by_cases hj : j.val < r
      · rw [dite_eq_left hj]
        have hcast : (Fin.castLE hrm ⟨j.val, hj⟩) = j := Fin.ext rfl
        have h1 : x j = c ⟨j.val, hj⟩ • a ⟨j.val, hj⟩ := by
          have h2 := hc ⟨j.val, hj⟩
          rw [hcast] at h2
          exact h2.symm
        rw [h1, smul_eq_mul]
      · rw [dite_eq_right hj]
        have hmem : x j ∈ (⊥ : Submodule ℤ ℤ) := by
          have h := hx j
          rwa [dite_eq_right hj] at h
        exact ((Submodule.mem_bot ℤ).mp hmem).symm

/-- The fundamental theorem of finitely generated abelian groups, invariant
factor form: every finitely generated abelian group is the product of a free
abelian group and a finite product of cyclic groups `ZMod (d i)` with
`1 < d i` and `d i ∣ d j` for `i ≤ j`. -/
theorem exists_invariant_factor_decomposition (A : Type*) [AddCommGroup A]
    [AddGroup.FG A] :
    ∃ (a k : ℕ) (d : Fin k → ℕ),
      (∀ i, 1 < d i) ∧
      (∀ i j : Fin k, i ≤ j → d i ∣ d j) ∧
      Nonempty (A ≃+ (Fin a →₀ ℤ) × ⨁ i : Fin k, ZMod (d i)) := by
  classical
  -- A presentation of `A` by a finite free abelian group.
  obtain ⟨n, s, hs⟩ := Module.Finite.exists_fin (R := ℤ) (M := A)
  let φ : (Fin n → ℤ) →ₗ[ℤ] A := Fintype.linearCombination ℤ s
  have hφ : Function.Surjective φ := by
    rw [← LinearMap.range_eq_top, Fintype.range_linearCombination, hs]
  -- Smith normal form of the kernel, with the divisibility chain.
  obtain ⟨r, m, hrm, bM, bN, a, hsnf, hne, hchain⟩ :=
    Submodule.exists_smith_normal_form_dvd_chain (LinearMap.ker φ)
  have hmn : n = m := by
    have h1 := Module.finrank_eq_card_basis bM
    rw [Module.finrank_pi, Fintype.card_fin, Fintype.card_fin] at h1
    exact h1
  subst hmn
  -- The diagonal submodules.
  set D : Fin n → Submodule ℤ ℤ :=
    fun j => if h : j.val < r then Submodule.span ℤ {a ⟨j.val, h⟩} else ⊥ with hD
  have hmap : Submodule.map (bM.equivFun : (Fin n → ℤ) →ₗ[ℤ] (Fin n → ℤ))
      (LinearMap.ker φ) = Submodule.pi Set.univ D :=
    map_basisEquivFun_eq_pi hrm hsnf
  -- The splitting equivalence `Fin r ⊕ Fin (n - r) ≃ Fin n`.
  let e' : Fin r ⊕ Fin (n - r) ≃ Fin n :=
    finSumFinEquiv.trans (finCongr (Nat.add_sub_cancel' hrm))
  have he'inl : ∀ i : Fin r, e' (Sum.inl i) = Fin.castLE hrm i := fun i => Fin.ext rfl
  have he'inr : ∀ t : Fin (n - r), (e' (Sum.inr t)).val = r + t.val := fun t => rfl
  -- Identifying the two families of quotient factors.
  have hD1 : ∀ i : Fin r, D (e' (Sum.inl i)) = Submodule.span ℤ {a i} := by
    intro i
    rw [he'inl]
    show (if h : (Fin.castLE hrm i).val < r then
        Submodule.span ℤ {a ⟨(Fin.castLE hrm i).val, h⟩} else ⊥) =
      Submodule.span ℤ {a i}
    rw [dite_eq_left (show (Fin.castLE hrm i).val < r from i.2)]
    rw [show (⟨(Fin.castLE hrm i).val, i.2⟩ : Fin r) = i from Fin.ext rfl]
  have hD2 : ∀ t : Fin (n - r), D (e' (Sum.inr t)) = ⊥ := by
    intro t
    show (if h : (e' (Sum.inr t)).val < r then
        Submodule.span ℤ {a ⟨(e' (Sum.inr t)).val, h⟩} else ⊥) = ⊥
    rw [dite_eq_right]
    rw [he'inr]
    omega
  -- The chain of equivalences.
  let ePres : A ≃+ ((Fin n → ℤ) ⧸ LinearMap.ker φ) :=
    (LinearMap.quotKerEquivOfSurjective φ hφ).symm.toAddEquiv
  let eQuot : ((Fin n → ℤ) ⧸ LinearMap.ker φ) ≃+ ((Fin n → ℤ) ⧸ Submodule.pi Set.univ D) :=
    (Submodule.Quotient.equiv _ _ bM.equivFun hmap).toAddEquiv
  let ePi : ((Fin n → ℤ) ⧸ Submodule.pi Set.univ D) ≃+ (Π j : Fin n, ℤ ⧸ D j) :=
    (Submodule.quotientPi D).toAddEquiv
  let eSplit := piQuotientSplit D e'
  let eFactors : (Π i : Fin r, ℤ ⧸ D (e' (Sum.inl i))) ×
        (Π t : Fin (n - r), ℤ ⧸ D (e' (Sum.inr t))) ≃+
      (Π i : Fin r, ZMod (a i).natAbs) × (Fin (n - r) → ℤ) :=
    (AddEquiv.piCongrRight fun i =>
      (Submodule.quotEquivOfEq _ _ (hD1 i)).toAddEquiv.trans
        ↑(Int.quotientSpanEquivZMod (a i))).prodCongr
      (AddEquiv.piCongrRight fun t =>
        (Submodule.quotEquivOfEq _ _ (hD2 t)).toAddEquiv.trans
          (Submodule.quotEquivOfEqBot (⊥ : Submodule ℤ ℤ) rfl).toAddEquiv)
  -- Drop the trivial factors `ZMod 1`.
  let S : Finset (Fin r) := Finset.univ.filter fun i => 1 < (a i).natAbs
  have hS : ∀ i ∉ S, (a i).natAbs = 1 := by
    intro i hi
    have hne := Int.natAbs_ne_zero.mpr (hne i)
    have hnot : ¬ 1 < (a i).natAbs := by
      intro hlt
      exact hi (Finset.mem_filter.mpr ⟨Finset.mem_univ i, hlt⟩)
    omega
  let eDrop := piCongrDropTrivial S hS
  -- Reindex by the increasing bijection `Finset.orderIsoOfFin`.
  let σ : Fin S.card ≃o ↥S := Finset.orderIsoOfFin S rfl
  let eReindex : (Π i : ↥S, ZMod (a i).natAbs) ≃+
      Π j : Fin S.card, ZMod (a (σ j : Fin r)).natAbs := piCongrOrderIsoOfFin S
  -- Assemble: `(Fin (n - r) →₀ ℤ) × ⨁ j : Fin S.card, ZMod (d j)`.
  let d : Fin S.card → ℕ := fun j => (a (σ j : Fin r)).natAbs
  have hd1 : ∀ j, 1 < d j := by
    intro j
    exact (Finset.mem_filter.mp (σ j).2).2
  have hdvd : ∀ j₁ j₂ : Fin S.card, j₁ ≤ j₂ → d j₁ ∣ d j₂ := by
    intro j₁ j₂ hjj
    have hle : (σ j₁ : Fin r) ≤ (σ j₂ : Fin r) := σ.monotone hjj
    exact Int.natAbs_dvd_natAbs.mpr (dvd_of_dvd_chain hchain hle)
  refine ⟨n - r, S.card, d, hd1, hdvd, ⟨?_⟩⟩
  exact (ePres.trans (eQuot.trans (ePi.trans (eSplit.trans
    (eFactors.trans ((eDrop.trans eReindex).prodCongr
      (Finsupp.linearEquivFunOnFinite ℤ ℤ (Fin (n - r))).symm.toAddEquiv)))))).trans
    (AddEquiv.prodComm.trans
      ((AddEquiv.refl _).prodCongr (DirectSum.addEquivProd _).symm))

/-- The finite case of the invariant-factor decomposition: a finite abelian
group is a product of cyclic groups `ZMod (d i)` with `1 < d i` and
`d i ∣ d j` for `i ≤ j`. -/
theorem exists_invariant_factor_decomposition_finite (A : Type*) [AddCommGroup A]
    [Finite A] :
    ∃ (k : ℕ) (d : Fin k → ℕ),
      (∀ i, 1 < d i) ∧ (∀ i j : Fin k, i ≤ j → d i ∣ d j) ∧
      Nonempty (A ≃+ ⨁ i : Fin k, ZMod (d i)) := by
  obtain ⟨a, k, d, hd1, hdvd, ⟨e⟩⟩ := exists_invariant_factor_decomposition A
  have ha0 : a = 0 := by
    by_contra ha
    have h0 : 0 < a := Nat.pos_of_ne_zero ha
    have hinf : Infinite (Fin a →₀ ℤ) :=
      Infinite.of_injective (fun n : ℤ => Finsupp.single ⟨0, h0⟩ n)
        (Finsupp.single_injective (⟨0, h0⟩ : Fin a))
    have hcard := Nat.card_congr e.toEquiv
    rw [Nat.card_prod, Nat.card_eq_zero.mpr (Or.inr hinf), Nat.zero_mul] at hcard
    have hpos : 0 < Nat.card A := Nat.card_pos
    omega
  subst ha0
  refine ⟨k, d, hd1, hdvd, ⟨?_⟩⟩
  exact e.trans ((AddEquiv.ofUnique.prodCongr (AddEquiv.refl _)).trans
    (AddEquiv.prodComm.trans
      { (Equiv.prodUnique (⨁ i : Fin k, ZMod (d i)) (PUnit.{1})) with
        map_add' := by intro x y; rfl }))
