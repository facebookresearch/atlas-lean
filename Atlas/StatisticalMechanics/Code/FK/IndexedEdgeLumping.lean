/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






import Code.FK.ActiveBoundaryEquiv

open Finset

namespace StatMech.FK

noncomputable section

variable {E A : Type*} [Fintype E] [DecidableEq E]
  [Fintype A] [DecidableEq A]


def indexedBernoulliWeight (p : Real) (eta : E → Bool) : Real :=
  ∏ e, if eta e then p else 1 - p


def indexedBundleSupport (f : E → A) (eta : E → Bool) : A → Bool :=
  fun a => decide (∃ e, f e = a ∧ eta e = true)


def indexedBundle (f : E → A) (a : A) : Finset E :=
  Finset.univ.filter (fun e => f e = a)


def indexedEffectiveParam (f : E → A) (p : Real) (a : A) : Real :=
  1 - (1 - p) ^ (indexedBundle f a).card

private def indexedFiberOr (f : E → A) (a : A)
    (eta : {e : E // f e = a} → Bool) : Bool :=
  decide (∃ e, eta e = true)

private def indexedFiberWeight (p : Real) {f : E → A} {a : A}
    (eta : {e : E // f e = a} → Bool) : Real :=
  ∏ e, if eta e then p else 1 - p

private theorem indexedFiberWeight_sum (p : Real) (f : E → A) (a : A) :
    ∑ eta : {e : E // f e = a} → Bool, indexedFiberWeight p eta = 1 := by
  unfold indexedFiberWeight
  rw [← Fintype.prod_sum (fun (_ : {e : E // f e = a}) (b : Bool) =>
    if b then p else 1 - p)]
  simp

private theorem indexedFiberWeight_allFalse (p : Real) (f : E → A) (a : A) :
    indexedFiberWeight p (fun _ : {e : E // f e = a} => false) =
      (1 - p) ^ (indexedBundle f a).card := by
  unfold indexedFiberWeight indexedBundle
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_subtype]
  rfl

private theorem indexedFiberMass_false (p : Real) (f : E → A) (a : A) :
    ∑ eta : {e : E // f e = a} → Bool,
      (if indexedFiberOr f a eta = false then indexedFiberWeight p eta else 0) =
        1 - indexedEffectiveParam f p a := by
  have hsingle : ∀ eta : {e : E // f e = a} → Bool,
      indexedFiberOr f a eta = false →
        eta = fun _ : {e : E // f e = a} => false := by
    intro eta heta
    funext e
    apply Bool.eq_false_iff.mpr
    intro he
    have hnot : ¬ ∃ u : {e : E // f e = a}, eta u = true := by
      simpa [indexedFiberOr] using heta
    exact hnot ⟨e, he⟩
  rw [Finset.sum_eq_single
    (fun _ : {e : E // f e = a} => false)]
  · rw [if_pos]
    · rw [indexedFiberWeight_allFalse]
      simp [indexedEffectiveParam]
    · simp [indexedFiberOr]
  · intro eta _ hne
    have hor : indexedFiberOr f a eta = true := by
      cases h : indexedFiberOr f a eta
      · exact absurd (hsingle eta h) hne
      · rfl
    simp [hor]
  · simp

private theorem indexedFiberMass (p : Real) (f : E → A) (a : A) (b : Bool) :
    ∑ eta : {e : E // f e = a} → Bool,
      (if indexedFiberOr f a eta = b then indexedFiberWeight p eta else 0) =
        if b then indexedEffectiveParam f p a else
          1 - indexedEffectiveParam f p a := by
  cases b
  · simpa using indexedFiberMass_false p f a
  · have hsplit :
        (∑ eta : {e : E // f e = a} → Bool,
          (if indexedFiberOr f a eta = true then indexedFiberWeight p eta else 0)) +
        (∑ eta : {e : E // f e = a} → Bool,
          (if indexedFiberOr f a eta = false then indexedFiberWeight p eta else 0)) = 1 := by
      rw [← Finset.sum_add_distrib]
      calc
        ∑ eta : {e : E // f e = a} → Bool,
            ((if indexedFiberOr f a eta = true then indexedFiberWeight p eta else 0) +
              if indexedFiberOr f a eta = false then indexedFiberWeight p eta else 0) =
            ∑ eta, indexedFiberWeight p eta := by
              apply Finset.sum_congr rfl
              intro eta _
              cases indexedFiberOr f a eta <;> simp
        _ = 1 := indexedFiberWeight_sum p f a
    have hfalse := indexedFiberMass_false p f a
    simp only [if_true]
    linarith

private abbrev indexedFiberConfigs (f : E → A) :=
  (a : A) → ({e : E // f e = a} → Bool)

private def indexedSplit (f : E → A) :
    (E → Bool) ≃ indexedFiberConfigs f :=
  Equiv.piCongrFiberwise (fun _ => Equiv.refl _)

@[simp] private theorem indexedSplit_symm_apply
    (f : E → A) (eta : indexedFiberConfigs f) (e : E) :
    (indexedSplit f).symm eta e = eta (f e) ⟨e, rfl⟩ := rfl

private theorem indexedBernoulliWeight_split
    (p : Real) (f : E → A) (eta : indexedFiberConfigs f) :
    indexedBernoulliWeight p ((indexedSplit f).symm eta) =
      ∏ a, indexedFiberWeight p (eta a) := by
  unfold indexedBernoulliWeight indexedFiberWeight
  calc
    (∏ e : E, if (indexedSplit f).symm eta e then p else 1 - p) =
        ∏ z : (a : A) × {e : E // f e = a},
          if (indexedSplit f).symm eta z.2.1 then p else 1 - p := by
      apply Fintype.prod_equiv (Equiv.sigmaFiberEquiv f).symm
      intro e
      simp
    _ = ∏ a : A, ∏ e : {e : E // f e = a},
          if (indexedSplit f).symm eta e.1 then p else 1 - p := by
      rw [Fintype.prod_sigma]
    _ = ∏ a : A, ∏ e : {e : E // f e = a},
          if eta a e then p else 1 - p := by
      apply Finset.prod_congr rfl
      intro a _
      apply Finset.prod_congr rfl
      intro e _
      obtain ⟨e, he⟩ := e
      subst a
      simp

private theorem indexedBundleSupport_split
    (f : E → A) (eta : indexedFiberConfigs f) :
    indexedBundleSupport f ((indexedSplit f).symm eta) =
      fun a => indexedFiberOr f a (eta a) := by
  funext a
  simp only [indexedBundleSupport, indexedFiberOr]
  rw [decide_eq_decide]
  constructor
  · rintro ⟨e, he, hopen⟩
    subst a
    exact ⟨⟨e, rfl⟩, by simpa using hopen⟩
  · rintro ⟨e, hopen⟩
    obtain ⟨e, he⟩ := e
    subst a
    exact ⟨e, rfl, by simpa using hopen⟩




theorem sum_indexedBernoulliWeight_bundleSupport
    (p : Real) (f : E → A) (F : (A → Bool) → Real) :
    ∑ eta : E → Bool,
        indexedBernoulliWeight p eta * F (indexedBundleSupport f eta) =
      ∑ rho : A → Bool,
        (∏ a, if rho a then indexedEffectiveParam f p a
          else 1 - indexedEffectiveParam f p a) * F rho := by
  rw [← Equiv.sum_comp (indexedSplit f).symm]
  simp_rw [indexedBernoulliWeight_split,
    indexedBundleSupport_split]
  change (∑ eta : (a : A) → ({e : E // f e = a} → Bool),
      (∏ a, indexedFiberWeight p (eta a)) *
        F (fun a => indexedFiberOr f a (eta a))) = _
  rw [show (∑ eta : (a : A) → ({e : E // f e = a} → Bool),
      (∏ a, indexedFiberWeight p (eta a)) *
        F (fun a => indexedFiberOr f a (eta a))) =
      ∑ rho : A → Bool, ∑ eta : (a : A) → ({e : E // f e = a} → Bool),
        (∏ a, if indexedFiberOr f a (eta a) = rho a then
          indexedFiberWeight p (eta a) else 0) * F rho by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro eta _
    rw [Finset.sum_eq_single (fun a => indexedFiberOr f a (eta a))]
    · simp
    · intro rho _ hrho
      have hne : ∃ a, indexedFiberOr f a (eta a) ≠ rho a :=
        Function.ne_iff.mp hrho.symm
      obtain ⟨a, ha⟩ := hne
      have hzero :
          (∏ a, if indexedFiberOr f a (eta a) = rho a then
            indexedFiberWeight p (eta a) else 0) = 0 := by
        apply Finset.prod_eq_zero (Finset.mem_univ a)
        rw [if_neg ha]
      rw [hzero, zero_mul]
    · simp
  ]
  apply Finset.sum_congr rfl
  intro rho _
  rw [← Finset.sum_mul]
  rw [← Fintype.prod_sum (fun a
    (eta : {e : E // f e = a} → Bool) =>
      if indexedFiberOr f a eta = rho a then indexedFiberWeight p eta else 0)]
  congr 1
  apply Finset.prod_congr rfl
  intro a _
  exact indexedFiberMass p f a (rho a)




theorem sum_indexedBernoulliWeight_restrictActive_bundleSupport
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (p : Real) (f : E → Sym2 V)
    (F : ConfigSpace G.edgeSet → Real) :
    ∑ eta : E → Bool,
        indexedBernoulliWeight p eta *
          F (restrictActive G (indexedBundleSupport f eta)) =
      ∑ rho : ConfigSpace G.edgeSet,
        (∏ a, if rho a then indexedEffectiveParam f p a.1
          else 1 - indexedEffectiveParam f p a.1) * F rho := by
  rw [sum_indexedBernoulliWeight_bundleSupport p f
    (fun omega => F (restrictActive G omega))]
  rw [← Equiv.sum_comp (activeSplitEquiv G).symm,
    Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro rho _
  have hrestrict : ∀ xi : ConfigSpace {e : Sym2 V // e ∉ G.edgeSet},
      restrictActive G ((activeSplitEquiv G).symm (rho, xi)) = rho :=
    fun xi => restrictActive_activeSplitEquiv_symm G rho xi
  have hfactor : ∀ xi : ConfigSpace {e : Sym2 V // e ∉ G.edgeSet},
      (∏ a : Sym2 V,
        if ((activeSplitEquiv G).symm (rho, xi)) a then
          indexedEffectiveParam f p a else
          1 - indexedEffectiveParam f p a) =
      (∏ a : G.edgeSet,
        if rho a then indexedEffectiveParam f p a.1
          else 1 - indexedEffectiveParam f p a.1) *
      (∏ a : {e : Sym2 V // e ∉ G.edgeSet},
        if xi a then indexedEffectiveParam f p a.1
          else 1 - indexedEffectiveParam f p a.1) := by
    intro xi
    let w : Sym2 V → Real := fun a =>
      if ((activeSplitEquiv G).symm (rho, xi)) a then
        indexedEffectiveParam f p a else
        1 - indexedEffectiveParam f p a
    calc
      ∏ a : Sym2 V, w a =
          ∏ z : G.edgeSet ⊕ {e : Sym2 V // e ∉ G.edgeSet},
            w (Equiv.sumCompl (fun e : Sym2 V => e ∈ G.edgeSet) z) := by
        apply Fintype.prod_equiv
          (Equiv.sumCompl (fun e : Sym2 V => e ∈ G.edgeSet)).symm
        intro a
        simp
      _ = (∏ a : G.edgeSet,
            w (Equiv.sumCompl (fun e : Sym2 V => e ∈ G.edgeSet)
              (Sum.inl a))) *
          ∏ a : {e : Sym2 V // e ∉ G.edgeSet},
            w (Equiv.sumCompl (fun e : Sym2 V => e ∈ G.edgeSet)
              (Sum.inr a)) := by
        rw [Fintype.prod_sum_type]
      _ = _ := by
        apply congrArg₂ (fun x y : Real => x * y)
        · apply Finset.prod_congr rfl
          intro a _
          simp [w, activeSplitEquiv,
            Equiv.piEquivPiSubtypeProd_symm_apply, a.2]
        · apply Finset.prod_congr rfl
          intro a _
          simp [w, activeSplitEquiv,
            Equiv.piEquivPiSubtypeProd_symm_apply, a.2]
  rw [Finset.sum_congr rfl (fun xi _ => by
    rw [hfactor xi, hrestrict xi])]
  have hinactive :
      (∑ xi : ConfigSpace {e : Sym2 V // e ∉ G.edgeSet},
        ∏ a, if xi a then indexedEffectiveParam f p a.1
          else 1 - indexedEffectiveParam f p a.1) = 1 := by
    rw [← Fintype.prod_sum (fun
      (a : {e : Sym2 V // e ∉ G.edgeSet}) (b : Bool) =>
        if b then indexedEffectiveParam f p a.1
          else 1 - indexedEffectiveParam f p a.1)]
    simp
  calc
    ∑ xi : ConfigSpace {e : Sym2 V // e ∉ G.edgeSet},
        ((∏ a, if rho a then indexedEffectiveParam f p a.1
            else 1 - indexedEffectiveParam f p a.1) *
          (∏ a, if xi a then indexedEffectiveParam f p a.1
            else 1 - indexedEffectiveParam f p a.1)) * F rho =
        ((∏ a, if rho a then indexedEffectiveParam f p a.1
            else 1 - indexedEffectiveParam f p a.1) * F rho) *
          (∑ xi : ConfigSpace {e : Sym2 V // e ∉ G.edgeSet},
            ∏ a, if xi a then indexedEffectiveParam f p a.1
              else 1 - indexedEffectiveParam f p a.1) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro xi _
      ring
    _ = _ := by rw [hinactive, mul_one]

end

end StatMech.FK
