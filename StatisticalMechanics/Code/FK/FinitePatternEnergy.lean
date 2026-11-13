/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






import Code.FK.CircuitLowerBound
import Code.FK.FKDisjointBoxDomainMarkov
import Code.Lattice.EulerFaces2

open MeasureTheory Finset

namespace StatMech
namespace FK

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]



variable (C : SimpleGraph V) [DecidableRel C.Adj]



theorem numClustersBC_setOpen_bounds (e : Sym2 V) (omega : ConfigSpace (Sym2 V)) :
    numClustersBC G C (setOpen e omega) ≤ numClustersBC G C (setClosed e omega) ∧
      numClustersBC G C (setClosed e omega) ≤
        numClustersBC G C (setOpen e omega) + 1 := by
  classical
  by_cases he : e ∈ G.edgeFinset
  · obtain ⟨a, b, hab, rfl⟩ : ∃ a b, G.Adj a b ∧ e = s(a, b) := by
      rw [SimpleGraph.mem_edgeFinset] at he
      induction e with
      | h a b => exact ⟨a, b, he, rfl⟩
    let H : SimpleGraph V := openSub G (setClosed s(a, b) omega) ⊔ C
    have hopen : openSub G (setOpen s(a, b) omega) ⊔ C =
        H ⊔ SimpleGraph.edge a b := by
      ext x y
      simp only [H, SimpleGraph.sup_adj, openSub_adj, SimpleGraph.edge_adj]
      constructor
      · rintro (⟨hxy, hopen⟩ | hC)
        · by_cases hxyab : s(x, y) = s(a, b)
          · rw [Sym2.eq_iff] at hxyab
            rcases hxyab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
            · exact Or.inr ⟨Or.inl ⟨rfl, rfl⟩, hab.ne⟩
            · exact Or.inr ⟨Or.inr ⟨rfl, rfl⟩, hab.ne.symm⟩
          · have hopen' := hopen
            rw [setOpen_of_ne hxyab] at hopen'
            rw [setClosed_of_ne hxyab]
            exact Or.inl (Or.inl ⟨hxy, hopen'⟩)
        · exact Or.inl (Or.inr hC)
      · rintro ((⟨hxy, hclosed⟩ | hC) | hedge)
        · exact Or.inl ⟨hxy, by
            by_cases hxyab : s(x, y) = s(a, b)
            · rw [hxyab]
              simp
            · rw [setClosed_of_ne hxyab] at hclosed
              rw [setOpen_of_ne hxyab]
              exact hclosed⟩
        · exact Or.inr hC
        · rcases hedge.1 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · exact Or.inl ⟨hab, by simp⟩
          · exact Or.inl ⟨hab.symm, by rw [Sym2.eq_swap]; simp⟩
    by_cases hr : H.Reachable a b
    · have hc := StatMech.Lattice.card_components_sup_edge_of_reachable H a b hr
      rw [numClustersBC, numClustersBC, hopen]
      change Nat.card (H ⊔ SimpleGraph.edge a b).ConnectedComponent ≤
          Nat.card H.ConnectedComponent ∧
        Nat.card H.ConnectedComponent ≤
          Nat.card (H ⊔ SimpleGraph.edge a b).ConnectedComponent + 1
      omega
    · have hc := StatMech.Lattice.card_components_sup_edge_of_not_reachable H a b hr
      rw [numClustersBC, numClustersBC, hopen]
      change Nat.card (H ⊔ SimpleGraph.edge a b).ConnectedComponent ≤
          Nat.card H.ConnectedComponent ∧
        Nat.card H.ConnectedComponent ≤
          Nat.card (H ⊔ SimpleGraph.edge a b).ConnectedComponent + 1
      omega
  · have hopen := openSub_setOpen_eq_setClosed_of_notMem G he omega
    have hc : numClustersBC G C (setOpen e omega) =
        numClustersBC G C (setClosed e omega) := by
      unfold numClustersBC
      rw [hopen]
    omega


theorem bcWeight_lo {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q)
    {e : Sym2 V} (he : e ∈ G.edgeFinset) (omega : ConfigSpace (Sym2 V)) :
    (1 - p) * bcWeight G C p q (setOpen e omega) ≤
      p * bcWeight G C p q (setClosed e omega) := by
  unfold bcWeight
  rw [edgeProduct_setOpen G p he, edgeProduct_setClosed G p he]
  set R := edgeRest G p e omega
  set k1 := numClustersBC G C (setOpen e omega)
  set k0 := numClustersBC G C (setClosed e omega)
  have hRpos : 0 < R := edgeRest_pos G hp hp1 e omega
  have hpow : q ^ k1 ≤ q ^ k0 :=
    pow_le_pow_right₀ hq (numClustersBC_setOpen_bounds G C e omega).1
  have hfac : (0 : ℝ) ≤ R * p * (1 - p) := by positivity
  nlinarith [mul_le_mul_of_nonneg_left hpow hfac]


theorem bcWeight_hi {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q)
    {e : Sym2 V} (he : e ∈ G.edgeFinset) (omega : ConfigSpace (Sym2 V)) :
    p * bcWeight G C p q (setClosed e omega) ≤
      q * (1 - p) * bcWeight G C p q (setOpen e omega) := by
  unfold bcWeight
  rw [edgeProduct_setOpen G p he, edgeProduct_setClosed G p he]
  set R := edgeRest G p e omega
  set k1 := numClustersBC G C (setOpen e omega)
  set k0 := numClustersBC G C (setClosed e omega)
  have hRpos : 0 < R := edgeRest_pos G hp hp1 e omega
  have hpow : q ^ k0 ≤ q ^ (k1 + 1) :=
    pow_le_pow_right₀ hq (numClustersBC_setOpen_bounds G C e omega).2
  rw [pow_succ] at hpow
  have hfac : (0 : ℝ) ≤ R * p * (1 - p) := by positivity
  nlinarith [mul_le_mul_of_nonneg_left hpow hfac]


theorem bcWeight_setOpen_ge {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q)
    (e : Sym2 V) (omega : ConfigSpace (Sym2 V)) :
    cFE p q * (bcWeight G C p q (setOpen e omega) +
        bcWeight G C p q (setClosed e omega)) ≤
      bcWeight G C p q (setOpen e omega) := by
  have hq0 : 0 < q := zero_lt_one.trans_le hq
  by_cases he : e ∈ G.edgeFinset
  · set W1 := bcWeight G C p q (setOpen e omega)
    set W0 := bcWeight G C p q (setClosed e omega)
    have hW1pos : 0 < W1 := bcWeight_pos G C hp hp1 hq0 _
    have hW0pos : 0 < W0 := bcWeight_pos G C hp hp1 hq0 _
    have hhi : p * W0 ≤ q * (1 - p) * W1 := bcWeight_hi G C hp hp1 hq he omega
    have hden : 0 < p + q * (1 - p) := by nlinarith
    have hkey : (p / (p + q * (1 - p))) * (W1 + W0) ≤ W1 := by
      rw [div_mul_eq_mul_div, div_le_iff₀ hden]
      nlinarith
    have hcfe : cFE p q ≤ p / (p + q * (1 - p)) := min_le_left _ _
    have hsum : 0 ≤ W1 + W0 := by positivity
    exact (mul_le_mul_of_nonneg_right hcfe hsum).trans hkey
  · have hep : edgeProduct G p (setOpen e omega) =
        edgeProduct G p (setClosed e omega) := by
      unfold edgeProduct
      apply Finset.prod_congr rfl
      intro e' he'
      have hne : e' ≠ e := fun h => he (h ▸ he')
      rw [setOpen_of_ne hne, setClosed_of_ne hne]
    have hk : numClustersBC G C (setOpen e omega) =
        numClustersBC G C (setClosed e omega) := by
      unfold numClustersBC
      rw [openSub_setOpen_eq_setClosed_of_notMem G he omega]
    have hweq : bcWeight G C p q (setOpen e omega) =
        bcWeight G C p q (setClosed e omega) := by
      unfold bcWeight
      rw [hep, hk]
    have hcfe : cFE p q ≤ 1 / 2 := cFE_le_half hp hp1 hq
    have hW1pos : 0 < bcWeight G C p q (setOpen e omega) :=
      bcWeight_pos G C hp hp1 hq0 _
    rw [← hweq]
    nlinarith [mul_le_mul_of_nonneg_right hcfe
      (by positivity : 0 ≤ bcWeight G C p q (setOpen e omega) +
        bcWeight G C p q (setOpen e omega))]


theorem bcWeight_setClosed_ge {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q)
    (e : Sym2 V) (omega : ConfigSpace (Sym2 V)) :
    cFE p q * (bcWeight G C p q (setOpen e omega) +
        bcWeight G C p q (setClosed e omega)) ≤
      bcWeight G C p q (setClosed e omega) := by
  have hq0 : 0 < q := zero_lt_one.trans_le hq
  by_cases he : e ∈ G.edgeFinset
  · have hW1pos : 0 < bcWeight G C p q (setOpen e omega) :=
      bcWeight_pos G C hp hp1 hq0 _
    have hW0pos : 0 < bcWeight G C p q (setClosed e omega) :=
      bcWeight_pos G C hp hp1 hq0 _
    have hlo : (1 - p) * bcWeight G C p q (setOpen e omega) ≤
        p * bcWeight G C p q (setClosed e omega) :=
      bcWeight_lo G C hp hp1 hq he omega
    have hcfe : cFE p q ≤ 1 - p := min_le_right _ _
    have hkey : (1 - p) * (bcWeight G C p q (setOpen e omega) +
          bcWeight G C p q (setClosed e omega)) ≤
        bcWeight G C p q (setClosed e omega) := by
      nlinarith
    have hsum : 0 ≤ bcWeight G C p q (setOpen e omega) +
        bcWeight G C p q (setClosed e omega) := by positivity
    exact (mul_le_mul_of_nonneg_right hcfe hsum).trans hkey
  · have hep : edgeProduct G p (setOpen e omega) =
        edgeProduct G p (setClosed e omega) := by
      unfold edgeProduct
      apply Finset.prod_congr rfl
      intro e' he'
      have hne : e' ≠ e := fun h => he (h ▸ he')
      rw [setOpen_of_ne hne, setClosed_of_ne hne]
    have hk : numClustersBC G C (setOpen e omega) =
        numClustersBC G C (setClosed e omega) := by
      unfold numClustersBC
      rw [openSub_setOpen_eq_setClosed_of_notMem G he omega]
    have hweq : bcWeight G C p q (setOpen e omega) =
        bcWeight G C p q (setClosed e omega) := by
      unfold bcWeight
      rw [hep, hk]
    have hcfe : cFE p q ≤ 1 / 2 := cFE_le_half hp hp1 hq
    have hW0pos : 0 < bcWeight G C p q (setClosed e omega) :=
      bcWeight_pos G C hp hp1 hq0 _
    rw [hweq]
    nlinarith [mul_le_mul_of_nonneg_right hcfe
      (by positivity : 0 ≤ bcWeight G C p q (setClosed e omega) +
        bcWeight G C p q (setClosed e omega))]

variable {C}


theorem fkWeight_setOpen_ge {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q)
    (e : Sym2 V) (omega : ConfigSpace (Sym2 V)) :
    cFE p q * (fkWeight G p q (setOpen e omega) + fkWeight G p q (setClosed e omega)) ≤
      fkWeight G p q (setOpen e omega) := by
  have hq0 : 0 < q := zero_lt_one.trans_le hq
  have hsum : 0 < fkWeight G p q (setOpen e omega) +
      fkWeight G p q (setClosed e omega) := by
    exact add_pos (fkWeight_pos G hp hp1 hq0 _) (fkWeight_pos G hp hp1 hq0 _)
  have hfe := (finite_energy G hp hp1 hq e omega).1
  rw [condOpen_eq_weightRatio G hp hp1 hq0] at hfe
  rwa [le_div_iff₀ hsum] at hfe



noncomputable def setPattern (I : Finset (Sym2 V)) (eta : ConfigSpace ↥I)
    (psi : ConfigSpace (Sym2 V)) : ConfigSpace (Sym2 V) :=
  fun e => if he : e ∈ I then eta ⟨e, he⟩ else psi e

omit [Fintype V] in
@[simp] theorem setPattern_of_mem {I : Finset (Sym2 V)} (eta : ConfigSpace ↥I)
    {e : Sym2 V} (he : e ∈ I) (psi : ConfigSpace (Sym2 V)) :
    setPattern I eta psi e = eta ⟨e, he⟩ := by
  simp [setPattern, he]

omit [Fintype V] in
theorem setPattern_of_not_mem {I : Finset (Sym2 V)} (eta : ConfigSpace ↥I)
    {e : Sym2 V} (he : e ∉ I) (psi : ConfigSpace (Sym2 V)) :
    setPattern I eta psi e = psi e := by
  simp [setPattern, he]

omit [Fintype V] in
theorem setPattern_empty (eta : ConfigSpace ↥(∅ : Finset (Sym2 V)))
    (psi : ConfigSpace (Sym2 V)) : setPattern ∅ eta psi = psi := by
  funext e
  simp [setPattern]

omit [Fintype V] in
theorem setPattern_setClosed {I : Finset (Sym2 V)} (eta : ConfigSpace ↥I)
    {e : Sym2 V} (he : e ∉ I) (psi : ConfigSpace (Sym2 V)) :
    setPattern I eta (setClosed e psi) = setClosed e (setPattern I eta psi) := by
  funext x
  by_cases hxI : x ∈ I
  · have hxe : x ≠ e := fun h => he (h ▸ hxI)
    rw [setPattern_of_mem eta hxI, setClosed_of_ne hxe,
      setPattern_of_mem eta hxI]
  · by_cases hxe : x = e
    · subst x
      simp [setPattern, he]
    · rw [setPattern_of_not_mem eta hxI, setClosed_of_ne hxe,
        setClosed_of_ne hxe, setPattern_of_not_mem eta hxI]

omit [Fintype V] in
theorem setPattern_setOpen {I : Finset (Sym2 V)} (eta : ConfigSpace ↥I)
    {e : Sym2 V} (he : e ∉ I) (psi : ConfigSpace (Sym2 V)) :
    setPattern I eta (setOpen e psi) = setOpen e (setPattern I eta psi) := by
  funext x
  by_cases hxI : x ∈ I
  · have hxe : x ≠ e := fun h => he (h ▸ hxI)
    rw [setPattern_of_mem eta hxI, setOpen_of_ne hxe,
      setPattern_of_mem eta hxI]
  · by_cases hxe : x = e
    · subst x
      simp [setPattern, he]
    · rw [setPattern_of_not_mem eta hxI, setOpen_of_ne hxe,
        setOpen_of_ne hxe, setPattern_of_not_mem eta hxI]



variable (C : SimpleGraph V) [DecidableRel C.Adj]


theorem inducedBcZ_insert (p q : ℝ) {e : Sym2 V} {I : Finset (Sym2 V)}
    (he : e ∉ I) (psi : ConfigSpace (Sym2 V)) :
    inducedBcZ G C p q (insert e I) psi =
      inducedBcZ G C p q I (setClosed e psi) +
        inducedBcZ G C p q I (setOpen e psi) := by
  classical
  unfold inducedBcZ condFibre AgreesOff
  rw [← Finset.sum_filter_add_sum_filter_not _ (fun sigma => sigma e = false)]
  congr 1
  · apply Finset.sum_congr ?_ (fun _ _ => rfl)
    ext sigma
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨hfree, h0⟩
      intro e' he'
      by_cases hee : e' = e
      · subst e'
        rw [h0, setClosed_self]
      · rw [setClosed_of_ne hee]
        exact hfree e' (by simp [Finset.mem_insert, hee, he'])
    · intro hfree
      refine ⟨fun e' he' => ?_, ?_⟩
      · have hne : e' ≠ e := fun h => he' (h ▸ Finset.mem_insert_self e I)
        have h := hfree e' (fun hc => he' (Finset.mem_insert_of_mem hc))
        rwa [setClosed_of_ne hne] at h
      · have h := hfree e he
        rwa [setClosed_self] at h
  · apply Finset.sum_congr ?_ (fun _ _ => rfl)
    ext sigma
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Bool.not_eq_false]
    constructor
    · rintro ⟨hfree, h1⟩
      intro e' he'
      by_cases hee : e' = e
      · subst e'
        rw [h1, setOpen_self]
      · rw [setOpen_of_ne hee]
        exact hfree e' (by simp [Finset.mem_insert, hee, he'])
    · intro hfree
      refine ⟨fun e' he' => ?_, ?_⟩
      · have hne : e' ≠ e := fun h => he' (h ▸ Finset.mem_insert_self e I)
        have h := hfree e' (fun hc => he' (Finset.mem_insert_of_mem hc))
        rwa [setOpen_of_ne hne] at h
      · have h := hfree e he
        rwa [setOpen_self] at h


theorem inducedBcZ_empty (p q : ℝ) (psi : ConfigSpace (Sym2 V)) :
    inducedBcZ G C p q ∅ psi = bcWeight G C p q psi := by
  classical
  unfold inducedBcZ condFibre
  have hf : Finset.univ.filter (AgreesOff ∅ psi) = {psi} := by
    ext sigma
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    constructor
    · intro h
      funext e
      exact h e (Finset.notMem_empty e)
    · intro h
      subst sigma
      exact fun _ _ => rfl
  rw [hf]
  simp



theorem cFE_pow_mul_inducedBcZ_le_setPattern
    {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q)
    (I : Finset (Sym2 V)) (eta : ConfigSpace ↥I) (psi : ConfigSpace (Sym2 V)) :
    cFE p q ^ I.card * inducedBcZ G C p q I psi ≤
      bcWeight G C p q (setPattern I eta psi) := by
  classical
  induction I using Finset.induction generalizing psi with
  | empty =>
      rw [Finset.card_empty, pow_zero, one_mul, inducedBcZ_empty]
      rw [setPattern_empty]
  | @insert e I he ih =>
      let etaI : ConfigSpace ↥I := fun x => eta ⟨x, Finset.mem_insert_of_mem x.2⟩
      let rho := setPattern I etaI psi
      have hclosed : setPattern I etaI (setClosed e psi) = setClosed e rho := by
        simpa [rho] using setPattern_setClosed etaI he psi
      have hopen : setPattern I etaI (setOpen e psi) = setOpen e rho := by
        simpa [rho] using setPattern_setOpen etaI he psi
      have ihc := ih etaI (setClosed e psi)
      have iho := ih etaI (setOpen e psi)
      have htarget : setPattern (insert e I) eta psi =
          if eta ⟨e, Finset.mem_insert_self e I⟩ then setOpen e rho else setClosed e rho := by
        funext x
        by_cases heta : eta ⟨e, Finset.mem_insert_self e I⟩ = true
        · simp only [heta, if_true]
          by_cases hx : x = e
          · subst x
            simp [setPattern, rho, he, heta]
          · by_cases hxI : x ∈ I
            · rw [setOpen_of_ne hx]
              simp [setPattern, rho, hxI, hx, etaI]
            · rw [setOpen_of_ne hx]
              simp [setPattern, rho, hxI, hx, etaI]
        · have heta0 : eta ⟨e, Finset.mem_insert_self e I⟩ = false :=
            Bool.eq_false_of_not_eq_true heta
          simp only [heta0, Bool.false_eq_true, if_false]
          by_cases hx : x = e
          · subst x
            simp [setPattern, rho, he, heta0]
          · by_cases hxI : x ∈ I
            · rw [setClosed_of_ne hx]
              simp [setPattern, rho, hxI, hx, etaI]
            · rw [setClosed_of_ne hx]
              simp [setPattern, rho, hxI, hx, etaI]
      rw [Finset.card_insert_of_notMem he, pow_succ,
        inducedBcZ_insert G C p q he, htarget]
      have hc : 0 ≤ cFE p q := (cFE_pos hp hp1 hq).le
      have hsum : cFE p q ^ I.card *
            (inducedBcZ G C p q I (setClosed e psi) +
              inducedBcZ G C p q I (setOpen e psi)) ≤
          bcWeight G C p q (setClosed e rho) +
            bcWeight G C p q (setOpen e rho) := by
        calc
          cFE p q ^ I.card *
              (inducedBcZ G C p q I (setClosed e psi) +
                inducedBcZ G C p q I (setOpen e psi)) =
              cFE p q ^ I.card * inducedBcZ G C p q I (setClosed e psi) +
                cFE p q ^ I.card * inducedBcZ G C p q I (setOpen e psi) := by ring
          _ ≤ bcWeight G C p q (setPattern I etaI (setClosed e psi)) +
                bcWeight G C p q (setPattern I etaI (setOpen e psi)) :=
            add_le_add ihc iho
          _ = bcWeight G C p q (setClosed e rho) +
                bcWeight G C p q (setOpen e rho) := by rw [hclosed, hopen]
      calc
        cFE p q ^ I.card * cFE p q *
            (inducedBcZ G C p q I (setClosed e psi) +
              inducedBcZ G C p q I (setOpen e psi)) =
            cFE p q * (cFE p q ^ I.card *
              (inducedBcZ G C p q I (setClosed e psi) +
                inducedBcZ G C p q I (setOpen e psi))) := by ring
        _ ≤ cFE p q * (bcWeight G C p q (setClosed e rho) +
              bcWeight G C p q (setOpen e rho)) :=
          mul_le_mul_of_nonneg_left hsum hc
        _ = cFE p q * (bcWeight G C p q (setOpen e rho) +
              bcWeight G C p q (setClosed e rho)) := by ring
        _ ≤ (if eta ⟨e, Finset.mem_insert_self e I⟩ then
              bcWeight G C p q (setOpen e rho) else
              bcWeight G C p q (setClosed e rho)) := by
          split
          · exact bcWeight_setOpen_ge G C hp hp1 hq e rho
          · exact bcWeight_setClosed_ge G C hp hp1 hq e rho
        _ = bcWeight G C p q
            (if eta ⟨e, Finset.mem_insert_self e I⟩ then setOpen e rho
              else setClosed e rho) := by split <;> rfl

variable {C}



theorem cFE_pow_mul_agreeWeightSum_le_setPattern
    {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q)
    (I : Finset (Sym2 V)) (eta : ConfigSpace ↥I) (psi : ConfigSpace (Sym2 V)) :
    cFE p q ^ I.card * agreeWeightSum G p q I psi ≤
      fkWeight G p q (setPattern I eta psi) := by
  classical
  induction I using Finset.induction generalizing psi with
  | empty =>
      rw [Finset.card_empty, pow_zero, one_mul, agreeWeightSum_empty]
      rw [setPattern_empty]
  | @insert e I he ih =>
      let etaI : ConfigSpace ↥I := fun x => eta ⟨x, Finset.mem_insert_of_mem x.2⟩
      let rho := setPattern I etaI psi
      have hclosed : setPattern I etaI (setClosed e psi) = setClosed e rho := by
        simpa [rho] using setPattern_setClosed etaI he psi
      have hopen : setPattern I etaI (setOpen e psi) = setOpen e rho := by
        simpa [rho] using setPattern_setOpen etaI he psi
      have ihc := ih etaI (setClosed e psi)
      have iho := ih etaI (setOpen e psi)
      have htarget : setPattern (insert e I) eta psi =
          if eta ⟨e, Finset.mem_insert_self e I⟩ then setOpen e rho else setClosed e rho := by
        funext x
        by_cases heta : eta ⟨e, Finset.mem_insert_self e I⟩ = true
        · simp only [heta, if_true]
          by_cases hx : x = e
          · subst x
            simp [setPattern, rho, he, heta]
          · by_cases hxI : x ∈ I
            · rw [setOpen_of_ne hx]
              simp [setPattern, rho, hxI, hx, etaI]
            · rw [setOpen_of_ne hx]
              simp [setPattern, rho, hxI, hx, etaI]
        · have heta0 : eta ⟨e, Finset.mem_insert_self e I⟩ = false := by
            exact Bool.eq_false_of_not_eq_true heta
          simp only [heta0, Bool.false_eq_true, if_false]
          by_cases hx : x = e
          · subst x
            simp [setPattern, rho, he, heta0]
          · by_cases hxI : x ∈ I
            · rw [setClosed_of_ne hx]
              simp [setPattern, rho, hxI, hx, etaI]
            · rw [setClosed_of_ne hx]
              simp [setPattern, rho, hxI, hx, etaI]
      rw [Finset.card_insert_of_notMem he, pow_succ,
        agreeWeightSum_insert G p q he, htarget]
      have hc : 0 ≤ cFE p q := (cFE_pos hp hp1 hq).le
      have hsum : cFE p q ^ I.card *
            (agreeWeightSum G p q I (setClosed e psi) +
              agreeWeightSum G p q I (setOpen e psi)) ≤
          fkWeight G p q (setClosed e rho) + fkWeight G p q (setOpen e rho) := by
        calc
          cFE p q ^ I.card *
              (agreeWeightSum G p q I (setClosed e psi) +
                agreeWeightSum G p q I (setOpen e psi)) =
              cFE p q ^ I.card * agreeWeightSum G p q I (setClosed e psi) +
                cFE p q ^ I.card * agreeWeightSum G p q I (setOpen e psi) := by ring
          _ ≤ fkWeight G p q (setPattern I etaI (setClosed e psi)) +
                fkWeight G p q (setPattern I etaI (setOpen e psi)) :=
            add_le_add ihc iho
          _ = fkWeight G p q (setClosed e rho) + fkWeight G p q (setOpen e rho) := by
            rw [hclosed, hopen]
      calc
        cFE p q ^ I.card * cFE p q *
            (agreeWeightSum G p q I (setClosed e psi) +
              agreeWeightSum G p q I (setOpen e psi)) =
            cFE p q * (cFE p q ^ I.card *
              (agreeWeightSum G p q I (setClosed e psi) +
                agreeWeightSum G p q I (setOpen e psi))) := by ring
        _ ≤ cFE p q *
            (fkWeight G p q (setClosed e rho) + fkWeight G p q (setOpen e rho)) :=
          mul_le_mul_of_nonneg_left hsum hc
        _ = cFE p q *
            (fkWeight G p q (setOpen e rho) + fkWeight G p q (setClosed e rho)) := by ring
        _ ≤ (if eta ⟨e, Finset.mem_insert_self e I⟩ then
              fkWeight G p q (setOpen e rho) else fkWeight G p q (setClosed e rho)) := by
          split
          · exact fkWeight_setOpen_ge G hp hp1 hq e rho
          · exact fkWeight_setClosed_ge G hp hp1 hq e rho
        _ = fkWeight G p q
            (if eta ⟨e, Finset.mem_insert_self e I⟩ then setOpen e rho else setClosed e rho) := by
          split <;> rfl




def patternEvent (I : Finset (Sym2 V)) (eta : ConfigSpace ↥I) :
    Set (ConfigSpace (Sym2 V)) :=
  {omega | I.restrict omega = eta}

omit [Fintype V] in
theorem setPattern_mem_patternEvent (I : Finset (Sym2 V)) (eta : ConfigSpace ↥I)
    (psi : ConfigSpace (Sym2 V)) : setPattern I eta psi ∈ patternEvent I eta := by
  funext e
  simp [Finset.restrict, setPattern]

omit [Fintype V] in
theorem agreesOff_setPattern (I : Finset (Sym2 V)) (eta : ConfigSpace ↥I)
    (psi : ConfigSpace (Sym2 V)) : AgreesOff I psi (setPattern I eta psi) := by
  intro e he
  exact setPattern_of_not_mem eta he psi

omit [Fintype V] in
theorem eq_setPattern_of_agreesOff_of_mem_pattern
    {I : Finset (Sym2 V)} {eta : ConfigSpace ↥I}
    {psi omega : ConfigSpace (Sym2 V)}
    (hoff : AgreesOff I psi omega) (hpat : omega ∈ patternEvent I eta) :
    omega = setPattern I eta psi := by
  funext e
  by_cases he : e ∈ I
  · have hcoord := congrFun hpat ⟨e, he⟩
    simpa [patternEvent, Finset.restrict, setPattern, he] using hcoord
  · rw [setPattern_of_not_mem eta he psi]
    exact hoff e he

omit [Fintype V] in

theorem setPattern_eq_self_of_mem_pattern
    {I : Finset (Sym2 V)} {eta : ConfigSpace ↥I}
    {omega : ConfigSpace (Sym2 V)} (hpat : omega ∈ patternEvent I eta) :
    setPattern I eta omega = omega := by
  symm
  exact eq_setPattern_of_agreesOff_of_mem_pattern (agreesOff_self I omega) hpat

omit [Fintype V] in


theorem dependsOnOutside_preimage_setPattern
    (I : Finset (Sym2 V)) (eta : ConfigSpace ↥I)
    (A : Set (ConfigSpace (Sym2 V))) :
    DependsOnOutside I (setPattern I eta ⁻¹' A) := by
  intro psi rho hoff
  have heq : setPattern I eta psi = setPattern I eta rho := by
    funext e
    by_cases he : e ∈ I
    · rw [setPattern_of_mem eta he, setPattern_of_mem eta he]
    · rw [setPattern_of_not_mem eta he, setPattern_of_not_mem eta he]
      exact (hoff e he).symm
  simp only [Set.mem_preimage]
  rw [heq]



theorem cFE_pow_le_condBcProb_pattern
    (C : SimpleGraph V) [DecidableRel C.Adj]
    {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q)
    (I : Finset (Sym2 V)) (eta : ConfigSpace ↥I) (psi : ConfigSpace (Sym2 V)) :
    cFE p q ^ I.card ≤
      ∑ omega, (patternEvent I eta).indicator (fun _ => (1 : ℝ)) omega *
        condBcProb G C p q I psi omega := by
  classical
  let target := setPattern I eta psi
  have htOff : AgreesOff I psi target := agreesOff_setPattern I eta psi
  have htPat : target ∈ patternEvent I eta := setPattern_mem_patternEvent I eta psi
  have hsingle :
      (∑ omega, (patternEvent I eta).indicator (fun _ => (1 : ℝ)) omega *
        condBcProb G C p q I psi omega) = condBcProb G C p q I psi target := by
    have hind : (patternEvent I eta).indicator (fun _ => (1 : ℝ)) target = 1 :=
      Set.indicator_of_mem htPat _
    calc
      (∑ omega, (patternEvent I eta).indicator (fun _ => (1 : ℝ)) omega *
        condBcProb G C p q I psi omega) =
          (patternEvent I eta).indicator (fun _ => (1 : ℝ)) target *
            condBcProb G C p q I psi target := by
        apply Finset.sum_eq_single target
        · intro omega _ hne
          by_cases hoff : AgreesOff I psi omega
          · have hnpat : omega ∉ patternEvent I eta := by
              intro hpat
              exact hne (eq_setPattern_of_agreesOff_of_mem_pattern hoff hpat)
            rw [Set.indicator_of_notMem hnpat, zero_mul]
          · unfold condBcProb
            rw [if_neg hoff, mul_zero]
        · simp
      _ = condBcProb G C p q I psi target := by rw [hind, one_mul]
  rw [hsingle]
  unfold condBcProb
  rw [if_pos htOff, le_div_iff₀
    (inducedBcZ_pos G C hp hp1 (zero_lt_one.trans_le hq) I psi)]
  simpa [target] using cFE_pow_mul_inducedBcZ_le_setPattern G C hp hp1 hq I eta psi



theorem cFE_pow_mul_condFibreMass_le_pattern
    {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q)
    (I : Finset (Sym2 V)) (eta : ConfigSpace ↥I) (psi : ConfigSpace (Sym2 V)) :
    cFE p q ^ I.card * (∑ omega ∈ condFibre I psi, fkProb G p q omega) ≤
      fkProb G p q (setPattern I eta psi) := by
  have hZ : 0 < fkZ G p q := fkZ_pos G hp hp1 (zero_lt_one.trans_le hq)
  have hweights :
      (∑ omega ∈ condFibre I psi, fkWeight G p q omega) =
        agreeWeightSum G p q I psi := by
    apply Finset.sum_congr
    · ext omega
      simp only [mem_condFibre, Finset.mem_filter, Finset.mem_univ, true_and,
        AgreesOff]
    · intro omega _
      rfl
  unfold fkProb
  rw [← Finset.sum_div, ← mul_div_assoc, hweights]
  exact div_le_div_of_nonneg_right
    (cFE_pow_mul_agreeWeightSum_le_setPattern G hp hp1 hq I eta psi) hZ.le



theorem cFE_pow_le_condFkProb_pattern
    {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q)
    (I : Finset (Sym2 V)) (eta : ConfigSpace ↥I) (psi : ConfigSpace (Sym2 V)) :
    cFE p q ^ I.card ≤
      ∑ omega ∈ condFibre I psi, (patternEvent I eta).indicator (fun _ => (1 : ℝ)) omega *
        condFkProb G p q I psi omega := by
  classical
  let target := setPattern I eta psi
  have htF : target ∈ condFibre I psi := by
    rw [mem_condFibre]
    exact agreesOff_setPattern I eta psi
  have htP : target ∈ patternEvent I eta := setPattern_mem_patternEvent I eta psi
  have hmass : 0 < ∑ omega ∈ condFibre I psi, fkProb G p q omega := by
    exact Finset.sum_pos (fun omega _ => fkProb_pos G hp hp1
      (zero_lt_one.trans_le hq) omega) ⟨target, htF⟩
  have hsingle :
      (∑ omega ∈ condFibre I psi,
        (patternEvent I eta).indicator (fun _ => (1 : ℝ)) omega *
        condFkProb G p q I psi omega) = condFkProb G p q I psi target := by
    have hind : (patternEvent I eta).indicator (fun _ => (1 : ℝ)) target = 1 :=
      Set.indicator_of_mem htP _
    calc
      (∑ omega ∈ condFibre I psi,
        (patternEvent I eta).indicator (fun _ => (1 : ℝ)) omega *
          condFkProb G p q I psi omega) =
          (patternEvent I eta).indicator (fun _ => (1 : ℝ)) target *
            condFkProb G p q I psi target := by
        apply Finset.sum_eq_single target
        · intro omega hoff hne
          rw [mem_condFibre] at hoff
          have hnpat : omega ∉ patternEvent I eta := by
            intro hpat
            exact hne (eq_setPattern_of_agreesOff_of_mem_pattern hoff hpat)
          rw [Set.indicator_of_notMem hnpat, zero_mul]
        · exact fun hnot => (hnot htF).elim
      _ = condFkProb G p q I psi target := by rw [hind, one_mul]
  rw [hsingle]
  unfold condFkProb
  rw [le_div_iff₀ hmass]
  simpa [target] using cFE_pow_mul_condFibreMass_le_pattern G hp hp1 hq I eta psi





theorem fkProb_eq_fibreMass_mul_condFkProb_general
    {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q)
    (I : Finset (Sym2 V)) (omega : ConfigSpace (Sym2 V)) :
    fkProb G p q omega =
      (∑ rho ∈ condFibre I omega, fkProb G p q rho) *
        condFkProb G p q I omega omega := by
  have hpos : 0 < ∑ rho ∈ condFibre I omega, fkProb G p q rho :=
    Finset.sum_pos (fun rho _ => fkProb_pos G hp hp1 hq rho)
      ⟨omega, self_mem_condFibre I omega⟩
  unfold condFkProb
  field_simp


theorem fkProb_fibre_decompose_general
    {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q)
    (I : Finset (Sym2 V)) (B : Set (ConfigSpace (Sym2 V))) :
    (∑ omega, B.indicator (fun _ => (1 : ℝ)) omega * fkProb G p q omega) =
      ∑ psi ∈ fibreReps I,
        (∑ sigma ∈ condFibre I psi, fkProb G p q sigma) *
          (∑ rho ∈ condFibre I psi,
            B.indicator (fun _ => (1 : ℝ)) rho * condFkProb G p q I psi rho) := by
  classical
  rw [← Finset.sum_fiberwise_of_maps_to (g := projOff I) (t := fibreReps I)
    (fun omega _ => Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, projOff_idem I omega⟩)]
  apply Finset.sum_congr rfl
  intro psi hpsi
  rw [fibreReps, Finset.mem_filter] at hpsi
  rw [show (Finset.univ.filter (fun rho => projOff I rho = psi)) = condFibre I psi from
    filter_projOff_eq_condFibre I psi hpsi.2]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro rho hrho
  rw [mem_condFibre] at hrho
  have hfac := fkProb_eq_fibreMass_mul_condFkProb_general G hp hp1 hq I rho
  have hfib : condFibre I rho = condFibre I psi := by
    exact condFibre_congr_dom' (agreesOff_symm hrho)
  rw [hfib] at hfac
  have hcond : condFkProb G p q I rho rho = condFkProb G p q I psi rho := by
    unfold condFkProb
    rw [hfib]
  rw [hfac, hcond]
  ring



theorem condFkProb_sum_outside
    {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q)
    {I : Finset (Sym2 V)} {B : Set (ConfigSpace (Sym2 V))}
    (hB : DependsOnOutside I B) (psi : ConfigSpace (Sym2 V)) :
    (∑ rho ∈ condFibre I psi,
      B.indicator (fun _ => (1 : ℝ)) rho * condFkProb G p q I psi rho) =
      B.indicator (fun _ => (1 : ℝ)) psi := by
  have hconst : ∀ rho ∈ condFibre I psi,
      B.indicator (fun _ => (1 : ℝ)) rho = B.indicator (fun _ => (1 : ℝ)) psi := by
    intro rho hrho
    rw [mem_condFibre] at hrho
    exact indicator_const_on_fibre hB hrho
  calc
    (∑ rho ∈ condFibre I psi,
      B.indicator (fun _ => (1 : ℝ)) rho * condFkProb G p q I psi rho) =
        B.indicator (fun _ => (1 : ℝ)) psi *
          ∑ rho ∈ condFibre I psi, condFkProb G p q I psi rho := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun rho hrho => by rw [hconst rho hrho])
    _ = B.indicator (fun _ => (1 : ℝ)) psi := by
      rw [condFkProb_sum_eq_one G hp hp1 hq I psi, mul_one]


theorem condFkProb_cross_outside
    {p q : ℝ} {I : Finset (Sym2 V)}
    {A B : Set (ConfigSpace (Sym2 V))} (hB : DependsOnOutside I B)
    (psi : ConfigSpace (Sym2 V)) :
    (∑ rho ∈ condFibre I psi,
      (A ∩ B).indicator (fun _ => (1 : ℝ)) rho * condFkProb G p q I psi rho) =
      B.indicator (fun _ => (1 : ℝ)) psi *
        (∑ rho ∈ condFibre I psi,
          A.indicator (fun _ => (1 : ℝ)) rho * condFkProb G p q I psi rho) := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro rho hrho
  rw [mem_condFibre] at hrho
  have hBeq : psi ∈ B ↔ rho ∈ B := hB psi rho hrho
  by_cases hA : rho ∈ A <;> by_cases hBrho : rho ∈ B <;>
    simp [Set.indicator, hA, hBrho, hBeq, Set.mem_inter_iff]




theorem cFE_pow_mul_event_le_pattern_inter
    {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q)
    (I : Finset (Sym2 V)) (eta : ConfigSpace ↥I)
    (B : Set (ConfigSpace (Sym2 V))) (hB : DependsOnOutside I B) :
    cFE p q ^ I.card *
        (∑ omega, B.indicator (fun _ => (1 : ℝ)) omega * fkProb G p q omega) ≤
      ∑ omega, (patternEvent I eta ∩ B).indicator (fun _ => (1 : ℝ)) omega *
        fkProb G p q omega := by
  rw [fkProb_fibre_decompose_general G hp hp1 (zero_lt_one.trans_le hq) I B,
    fkProb_fibre_decompose_general G hp hp1 (zero_lt_one.trans_le hq) I
      (patternEvent I eta ∩ B), Finset.mul_sum]
  apply Finset.sum_le_sum
  intro psi hpsi
  have hfm : 0 ≤ ∑ sigma ∈ condFibre I psi, fkProb G p q sigma :=
    Finset.sum_nonneg (fun sigma _ => fkProb_nonneg G hp hp1
      (zero_lt_one.trans_le hq) sigma)
  rw [condFkProb_sum_outside G hp hp1 (zero_lt_one.trans_le hq) hB psi,
    condFkProb_cross_outside G hB psi]
  have hpat := cFE_pow_le_condFkProb_pattern G hp hp1 hq I eta psi
  by_cases hpsiB : psi ∈ B
  · rw [Set.indicator_of_mem hpsiB]
    nlinarith [mul_le_mul_of_nonneg_left hpat hfm]
  · rw [Set.indicator_of_notMem hpsiB]
    simp




theorem cFE_pow_mul_bcEvent_le_pattern_inter
    (C : SimpleGraph V) [DecidableRel C.Adj]
    {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q)
    (I : Finset (Sym2 V)) (eta : ConfigSpace ↥I)
    (B : Set (ConfigSpace (Sym2 V))) (hB : DependsOnOutside I B) :
    cFE p q ^ I.card *
        (∑ omega, B.indicator (fun _ => (1 : ℝ)) omega * bcProb G C p q omega) ≤
      ∑ omega, (patternEvent I eta ∩ B).indicator (fun _ => (1 : ℝ)) omega *
        bcProb G C p q omega := by
  classical
  rw [bcProb_fibre_decompose G C hp hp1 (zero_lt_one.trans_le hq) I B,
    bcProb_fibre_decompose G C hp hp1 (zero_lt_one.trans_le hq) I
      (patternEvent I eta ∩ B), Finset.mul_sum]
  apply Finset.sum_le_sum
  intro psi hpsi
  rw [fibreReps, Finset.mem_filter] at hpsi
  have hfm : 0 ≤ ∑ sigma ∈ condFibre I psi, bcProb G C p q sigma :=
    Finset.sum_nonneg (fun sigma _ =>
      bcProb_nonneg G C hp hp1 (zero_lt_one.trans_le hq) sigma)
  rw [condBcProb_sum_outside G C hp hp1 (zero_lt_one.trans_le hq) hB hpsi.2,
    condBcProb_cross_outside G C hB]
  have hpat := cFE_pow_le_condBcProb_pattern G C hp hp1 hq I eta psi
  by_cases hpsiB : psi ∈ B
  · rw [Set.indicator_of_mem hpsiB]
    nlinarith [mul_le_mul_of_nonneg_left hpat hfm]
  · rw [Set.indicator_of_notMem hpsiB]
    simp





theorem cFE_pow_mul_bcPreimage_le_event
    (C : SimpleGraph V) [DecidableRel C.Adj]
    {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q)
    (I : Finset (Sym2 V)) (eta : ConfigSpace ↥I)
    (A : Set (ConfigSpace (Sym2 V))) :
    cFE p q ^ I.card *
        (∑ omega, (setPattern I eta ⁻¹' A).indicator (fun _ => (1 : ℝ)) omega *
          bcProb G C p q omega) ≤
      ∑ omega, A.indicator (fun _ => (1 : ℝ)) omega * bcProb G C p q omega := by
  let B := setPattern I eta ⁻¹' A
  have hins : patternEvent I eta ∩ B ⊆ A := by
    rintro omega ⟨hpat, hB⟩
    change setPattern I eta omega ∈ A at hB
    rwa [setPattern_eq_self_of_mem_pattern hpat] at hB
  refine (cFE_pow_mul_bcEvent_le_pattern_inter G C hp hp1 hq I eta B
    (dependsOnOutside_preimage_setPattern I eta A)).trans ?_
  apply Finset.sum_le_sum
  intro omega _
  by_cases hmem : omega ∈ patternEvent I eta ∩ B
  · rw [Set.indicator_of_mem hmem, Set.indicator_of_mem (hins hmem)]
  · rw [Set.indicator_of_notMem hmem]
    rw [zero_mul]
    exact mul_nonneg (Set.indicator_nonneg (fun _ _ => zero_le_one) omega)
      (bcProb_nonneg G C hp hp1 (zero_lt_one.trans_le hq) omega)

end FK
end StatMech
