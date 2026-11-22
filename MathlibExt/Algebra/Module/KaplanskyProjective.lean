/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.RingTheory.LocalRing.Defs
public import Mathlib.Algebra.Module.Projective
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Ring

@[expose] public section

namespace MathlibExt.Kaplansky

/-- Projection operator from the projectivity splitting, restricted to an index set `J`. -/
private noncomputable def kapProj {R : Type*} {M : Type*} [CommRing R] [AddCommGroup M]
    [Module R M] (s : M →ₗ[R] (M →₀ R)) (J : Set M) : M →ₗ[R] M :=
  (Finsupp.linearCombination R (J.indicator fun x => x)) ∘ₗ s

-- N1. direct summands of projectives are projective
private theorem kap_projective_of_retract {R : Type*} {M : Type*} [Ring R]
    [AddCommGroup M] [Module R M] [Module.Projective R M]
    (N : Submodule R M) (f : M →ₗ[R] M)
    (hmem : ∀ x, f x ∈ N) (hid : ∀ x : ↥N, f (x : M) = (x : M)) :
    Module.Projective R ↥N := by
  apply Module.Projective.of_split (i := N.subtype) (s := f.codRestrict N hmem)
  ext x
  simp only [LinearMap.comp_apply, Submodule.subtype_apply, LinearMap.codRestrict_apply,
    LinearMap.id_apply]
  exact hid x

-- N4. matrices congruent to 1 mod the maximal ideal are invertible
private theorem kap_isUnit_det_of_sub_one {R : Type*} [CommRing R] [IsLocalRing R]
    {κ : Type*} [Fintype κ] [DecidableEq κ] (A : Matrix κ κ R)
    (h : ∀ i j, A i j - (1 : Matrix κ κ R) i j ∈ IsLocalRing.maximalIdeal R) :
    IsUnit A.det := by
  rw [← IsLocalRing.residue_ne_zero_iff_isUnit]
  have hmap : (IsLocalRing.residue R).mapMatrix A = 1 := by
    ext i j
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply]
    have hmem := h i j
    rw [Matrix.one_apply] at hmem ⊢
    by_cases hij : i = j <;> simp only [hij, ↓reduceIte] at hmem ⊢
    · have hres := (IsLocalRing.residue_eq_zero_iff _).mpr hmem
      rw [map_sub, map_one] at hres
      exact sub_eq_zero.mp hres
    · have hres := (IsLocalRing.residue_eq_zero_iff _).mpr hmem
      rw [map_sub, map_zero, sub_zero] at hres
      exact hres
  have hdet : (IsLocalRing.residue R) A.det =
      (1 : Matrix κ κ (IsLocalRing.ResidueField R)).det := by
    rw [← hmap, RingHom.map_det]
  rw [hdet, Matrix.det_one]
  exact one_ne_zero

-- N7. refining a direct-sum decomposition inside a summand
private theorem kap_isCompl_sup_map {R : Type*} {M : Type*} [Ring R]
    [AddCommGroup M] [Module R M]
    (A D : Submodule R M) (h : IsCompl A D)
    (B E : Submodule R ↥D) (hBE : IsCompl B E) :
    IsCompl (A ⊔ B.map D.subtype) (E.map D.subtype) := by
  have hdisj : Disjoint (B.map D.subtype) (E.map D.subtype) := by
    rw [Submodule.disjoint_def]
    intro x hx1 hx2
    obtain ⟨y, hyB, hyx⟩ := Submodule.mem_map.mp hx1
    obtain ⟨z, hzE, hzx⟩ := Submodule.mem_map.mp hx2
    have hyz : y = z := Subtype.val_injective (hyx.trans hzx.symm)
    have hinf : y ∈ B ⊓ E := ⟨hyB, hyz ▸ hzE⟩
    rw [hBE.inf_eq_bot, Submodule.mem_bot] at hinf
    rw [← hyx, hinf, map_zero]
  have hsup : B.map D.subtype ⊔ E.map D.subtype = D := by
    have h2 : (B ⊔ E).map D.subtype = B.map D.subtype ⊔ E.map D.subtype :=
      Submodule.map_sup _ _ _
    rw [hBE.sup_eq_top, Submodule.map_subtype_top] at h2
    exact h2.symm
  have hdisj2 : Disjoint (A ⊔ B.map D.subtype) (E.map D.subtype) := by
    rw [Submodule.disjoint_def]
    intro x hx1 hx2
    obtain ⟨a, haA, b, hbB, hab⟩ := Submodule.mem_sup.mp hx1
    obtain ⟨y, hyB, hyb⟩ := Submodule.mem_map.mp hbB
    obtain ⟨z, hzE, hzx⟩ := Submodule.mem_map.mp hx2
    have hsub : (D.subtype (z - y) : M) = a := by
      rw [map_sub, hzx, ← hab, hyb]
      abel
    have haD : a ∈ D := hsub ▸ (z - y).property
    have ha0 : a = 0 := by
      have hmem : a ∈ A ⊓ D := ⟨haA, haD⟩
      rw [h.inf_eq_bot, Submodule.mem_bot] at hmem
      exact hmem
    have hzz : (D.subtype y : M) = D.subtype z := by
      rw [hyb, hzx, ← hab, ha0, zero_add]
    have hyz : y = z := Subtype.val_injective hzz
    have hinf : y ∈ B ⊓ E := ⟨hyB, hyz ▸ hzE⟩
    rw [hBE.inf_eq_bot, Submodule.mem_bot] at hinf
    rw [← hab, ha0, ← hyb, hinf, map_zero, zero_add]
  have hsup2 : A ⊔ B.map D.subtype ⊔ E.map D.subtype = ⊤ := by
    calc A ⊔ B.map D.subtype ⊔ E.map D.subtype
        = A ⊔ (B.map D.subtype ⊔ E.map D.subtype) := by rw [sup_assoc]
      _ = A ⊔ D := by rw [hsup]
      _ = ⊤ := h.sup_eq_top
  exact IsCompl.mk hdisj2 (codisjoint_iff.mpr hsup2)

-- N12. every point lies in a countable closed set
private theorem kap_exists_countable_closed {R : Type*} {M : Type*} [CommRing R]
    [AddCommGroup M] [Module R M]
    (s : M →ₗ[R] (M →₀ R)) (m : M) :
    ∃ J₁ : Set M, J₁.Countable ∧ m ∈ J₁ ∧ ∀ p ∈ J₁, ↑(s p).support ⊆ J₁ := by
  classical
  let step : Set M → Set M := fun T => T ∪ ⋃ p ∈ T, ↑(s p).support
  have hstep : ∀ T : Set M, T.Finite → (step T).Finite := by
    intro T hT
    exact hT.union (hT.biUnion (fun p _ => (s p).support.finite_toSet))
  have hfin : ∀ n : ℕ, ((step^[n]) {m}).Finite := by
    intro n
    induction n with
    | zero => exact Set.finite_singleton m
    | succ n ih =>
      rw [Function.iterate_succ_apply']
      exact hstep _ ih
  refine ⟨⋃ n, (step^[n]) {m}, Set.countable_iUnion (fun n => (hfin n).countable), ?_, ?_⟩
  · exact Set.mem_iUnion.mpr ⟨0, Set.mem_singleton m⟩
  · intro p hp
    rw [Set.mem_iUnion] at hp
    obtain ⟨n, hn⟩ := hp
    have hsub : ↑(s p).support ⊆ (step^[n.succ]) {m} := by
      rw [Function.iterate_succ_apply']
      intro q hq
      change q ∈ ((step^[n]) {m} ∪ ⋃ p ∈ (step^[n]) {m}, ↑(s p).support)
      exact Or.inr (Set.mem_biUnion hn hq)
    exact hsub.trans (Set.subset_iUnion (fun n => (step^[n]) {m}) n.succ)

-- N2. content-ideal facts for an element of a projective module
private theorem kap_content_ideal_facts {R : Type*} {M : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] [Module.Projective R M]
    (s : M →ₗ[R] (M →₀ R)) (hs : Finsupp.linearCombination R id ∘ₗ s = LinearMap.id)
    (x : M) :
    (LinearMap.range (Module.Dual.eval R M x)).FG ∧
    (∀ m : M, s x m ∈ LinearMap.range (Module.Dual.eval R M x)) ∧
    x = ∑ m ∈ (s x).support, (s x m) • m := by
  have hcomp : (Finsupp.linearCombination R id ∘ₗ s) x = x := by
    have h := LinearMap.congr_fun hs x
    simpa only [LinearMap.id_apply] using h
  have hc : x = ∑ m ∈ (s x).support, (s x m) • m := by
    have h2 : Finsupp.linearCombination R id (s x) =
        ∑ m ∈ (s x).support, (s x m) • m := by
      rw [Finsupp.linearCombination_apply]
      rfl
    rw [← h2]
    exact hcomp.symm
  have hb : ∀ m : M, s x m ∈ LinearMap.range (Module.Dual.eval R M x) := by
    intro m
    exact ⟨(Finsupp.lapply m) ∘ₗ s, rfl⟩
  refine ⟨?_, hb, hc⟩
  have hspan : LinearMap.range (Module.Dual.eval R M x) =
      Submodule.span R ((fun m => s x m) '' ↑(s x).support) := by
    apply le_antisymm
    · intro y hy
      obtain ⟨φ, rfl⟩ := hy
      simp only [Module.Dual.eval_apply]
      have hexp : φ x = ∑ m ∈ (s x).support, (s x m) * φ m := by
        conv_lhs => rw [hc]
        rw [map_sum]
        refine Finset.sum_congr rfl (fun m _ => ?_)
        rw [map_smul, smul_eq_mul]
      rw [hexp]
      refine Submodule.sum_mem _ (fun m hm => ?_)
      rw [mul_comm, ← smul_eq_mul]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨m, Finset.mem_coe.mpr hm, rfl⟩)
    · rw [Submodule.span_le]
      rintro y ⟨m, hm, rfl⟩
      exact hb m
  rw [hspan]
  exact Submodule.fg_span ((Finset.finite_toSet _).image _)

-- N3. minimal generating sets over a local ring have unit-consequence relations in 𝔪
private theorem kap_exists_minimal_span {R : Type*} [CommRing R] [IsLocalRing R]
    {M' : Type*} [AddCommGroup M'] [Module R M']
    (N : Submodule R M') (hN : N.FG) :
    ∃ S : Finset M', Submodule.span R (↑S : Set M') = N ∧
      ∀ r : M' → R, (∑ a ∈ S, r a • a = 0) → ∀ a ∈ S, r a ∈ IsLocalRing.maximalIdeal R := by
  classical
  obtain ⟨S0, hsspan⟩ := hN
  have hex : ∃ n, ∃ S : Finset M', S.card = n ∧ Submodule.span R (↑S : Set M') = N :=
    ⟨S0.card, S0, rfl, hsspan⟩
  obtain ⟨S, hScard, hSspan⟩ := Nat.find_spec hex
  refine ⟨S, hSspan, fun r hr => ?_⟩
  intro a ha
  by_contra hcon
  obtain ⟨u, hu⟩ := IsLocalRing.notMem_maximalIdeal.mp hcon
  have hsplit : ((u : Rˣ) : R) • a + ∑ x ∈ S.erase a, r x • x = 0 := by
    have h := Finset.add_sum_erase S (fun x => r x • x) ha
    rw [hr, ← hu] at h
    exact h
  have h1 : ((u : Rˣ) : R) • a = -(∑ x ∈ S.erase a, r x • x) :=
    eq_neg_of_add_eq_zero_left hsplit
  have h3 : ((u⁻¹ : Rˣ) : R) • ((u : Rˣ) : R) • a = a := by
    rw [← mul_smul, u.inv_mul, one_smul]
  have hkk : a = -(((u⁻¹ : Rˣ) : R) • (∑ x ∈ S.erase a, r x • x)) := by
    have h2 := congrArg (((u⁻¹ : Rˣ) : R) • ·) h1
    simp only [smul_neg] at h2
    rwa [h3] at h2
  have hmem : -(((u⁻¹ : Rˣ) : R) • (∑ x ∈ S.erase a, r x • x)) ∈
      Submodule.span R (↑(S.erase a) : Set M') := by
    apply Submodule.neg_mem
    apply Submodule.smul_mem
    apply Submodule.sum_mem
    intro b hb
    apply Submodule.smul_mem
    exact Submodule.subset_span (Finset.mem_coe.mpr hb)
  have hkmem : a ∈ Submodule.span R (↑(S.erase a) : Set M') := by
    rw [← hkk] at hmem
    exact hmem
  have hspan : Submodule.span R (↑(S.erase a) : Set M') = N := by
    apply le_antisymm
    · calc Submodule.span R (↑(S.erase a) : Set M') ≤ Submodule.span R ↑S :=
            Submodule.span_mono (Finset.coe_subset.mpr (Finset.erase_subset _ _))
        _ = N := hSspan
    · rw [← hSspan, Submodule.span_le]
      intro y hy
      by_cases hyk : y = a
      · rw [hyk]; exact hkmem
      · apply Submodule.subset_span
        rw [Finset.mem_coe, Finset.mem_erase]
        exact ⟨hyk, Finset.mem_coe.mp hy⟩
  have hcard : (S.erase a).card < S.card := Finset.card_erase_lt_of_mem ha
  have hle : Nat.find hex ≤ (S.erase a).card :=
    Nat.find_min' hex ⟨S.erase a, rfl, hspan⟩
  omega

-- N5. an invertible pairing mod 𝔪 splits off a free summand
private theorem kap_free_summand_of_pairing {R : Type*} [CommRing R] [IsLocalRing R]
    {M : Type*} [AddCommGroup M] [Module R M]
    {κ : Type*} [Finite κ] [DecidableEq κ]
    (z : κ → M) (ψ : κ → Module.Dual R M)
    (h : ∀ j k, ψ k (z j) - (if j = k then 1 else 0) ∈ IsLocalRing.maximalIdeal R) :
    LinearIndependent R z ∧
    ∃ D : Submodule R M, IsCompl (Submodule.span R (Set.range z)) D := by
  classical
  have : Fintype κ := Fintype.ofFinite κ
  let A : Matrix κ κ R := Matrix.of fun k j => ψ k (z j)
  have hA : ∀ i j, A i j - (1 : Matrix κ κ R) i j ∈ IsLocalRing.maximalIdeal R := by
    intro i j
    change ψ i (z j) - (1 : Matrix κ κ R) i j ∈ IsLocalRing.maximalIdeal R
    rw [Matrix.one_apply]
    have h2 := h j i
    have hif : (if j = i then (1 : R) else (0 : R)) = (if i = j then 1 else 0) := by
      by_cases hij : i = j
      · subst hij; rfl
      · have h1 : ¬ (j = i) := Ne.symm hij
        simp only [hij, h1, ↓reduceIte]
    rwa [hif] at h2
  have hdet : IsUnit A.det := kap_isUnit_det_of_sub_one A hA
  have hinv : ∀ c : κ → R, Matrix.mulVec A⁻¹ (Matrix.mulVec A c) = c := by
    intro c
    rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hdet, Matrix.one_mulVec]
  have hcomp : ∀ c : κ → R,
      LinearMap.pi ψ (Fintype.linearCombination R z c) = Matrix.mulVec A c := by
    intro c
    funext k
    rw [LinearMap.pi_apply, Fintype.linearCombination_apply, map_sum]
    change (∑ j, ψ k (c j • z j)) = Matrix.mulVec A c k
    have hmul : Matrix.mulVec A c k = ∑ j, A k j * c j := rfl
    rw [hmul]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    have hAkj : A k j = ψ k (z j) := rfl
    rw [map_smul, smul_eq_mul, mul_comm, hAkj]
  have hLI : LinearIndependent R z := by
    rw [Fintype.linearIndependent_iff]
    intro c hc0 i
    have hAc : Matrix.mulVec A c = 0 := by
      have hY0 : Fintype.linearCombination R z c = 0 := by
        rw [Fintype.linearCombination_apply]
        exact hc0
      rw [← hcomp c, hY0, map_zero]
    have h0 := hinv c
    rw [hAc, Matrix.mulVec_zero] at h0
    rw [← h0]
    rfl
  refine ⟨hLI, ?_⟩
  have hB : ∀ c : κ → R, Matrix.mulVecLin A⁻¹ (Matrix.mulVec A c) = c := by
    intro c
    rw [Matrix.mulVecLin_apply]
    exact hinv c
  have hEfix : ∀ c : κ → R,
      (Fintype.linearCombination R z ∘ₗ Matrix.mulVecLin A⁻¹ ∘ₗ LinearMap.pi ψ)
        (Fintype.linearCombination R z c) = Fintype.linearCombination R z c := by
    intro c
    rw [LinearMap.comp_apply, LinearMap.comp_apply, hcomp c, hB c]
  have hEmem : ∀ x, (Fintype.linearCombination R z ∘ₗ Matrix.mulVecLin A⁻¹ ∘ₗ
      LinearMap.pi ψ) x ∈ Submodule.span R (Set.range z) := by
    intro x
    rw [← Fintype.range_linearCombination R z]
    refine ⟨Matrix.mulVecLin A⁻¹ (LinearMap.pi ψ x), ?_⟩
    rw [LinearMap.comp_apply, LinearMap.comp_apply]
  have hEid : ∀ w ∈ Submodule.span R (Set.range z),
      (Fintype.linearCombination R z ∘ₗ Matrix.mulVecLin A⁻¹ ∘ₗ LinearMap.pi ψ) w = w := by
    intro w hw
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun R).mp hw
    have hYc : Fintype.linearCombination R z c = w := by
      rw [Fintype.linearCombination_apply]
      exact hc
    rw [← hYc]
    exact hEfix c
  have hproj : ∀ x : ↥(Submodule.span R (Set.range z)),
      (Fintype.linearCombination R z ∘ₗ Matrix.mulVecLin A⁻¹ ∘ₗ LinearMap.pi ψ).codRestrict
        _ hEmem ↑x = x := by
    intro x
    rw [Subtype.ext_iff]
    simp only [LinearMap.codRestrict_apply]
    exact hEid _ x.property
  exact ⟨_, LinearMap.isCompl_of_proj hproj⟩

-- N6. Kaplansky's element lemma: every element lies in a finitely generated free summand
private theorem kap_exists_free_summand_mem {R : Type*} [CommRing R] [IsLocalRing R]
    {M : Type*} [AddCommGroup M] [Module R M] [Module.Projective R M]
    (x : M) :
    ∃ u : Set M, LinearIndepOn R id u ∧ (∃ D : Submodule R M, IsCompl (Submodule.span R u) D)
      ∧ x ∈ Submodule.span R u := by
  classical
  obtain ⟨s, hs⟩ := Module.projective_def'.mp (inferInstance : Module.Projective R M)
  obtain ⟨hFG, hb, hc⟩ := kap_content_ideal_facts s hs x
  obtain ⟨S, hSspan, hSmin⟩ := kap_exists_minimal_span _ hFG
  have hchoice : ∀ b : R, ∃ φ : Module.Dual R M, b ∈ (↑S : Set R) → φ x = b := by
    intro b
    by_cases hb : b ∈ (↑S : Set R)
    · have hamem : b ∈ LinearMap.range (Module.Dual.eval R M x) := by
        rw [← hSspan]
        exact Submodule.subset_span hb
      obtain ⟨φ, hφ⟩ := hamem
      exact ⟨φ, fun _ => by rwa [Module.Dual.eval_apply] at hφ⟩
    · exact ⟨0, fun h => absurd h hb⟩
  choose ψ hψ using hchoice
  have hcoeff : ∀ m : M, ∃ d : R → R, m ∈ (s x).support → ∑ a ∈ S, d a * a = s x m := by
    intro m
    by_cases hm : m ∈ (s x).support
    · have hmem : s x m ∈ Submodule.span R (↑S : Set R) := by
        have h2 := hb m
        rw [← hSspan] at h2
        exact h2
      obtain ⟨d, _, hd⟩ := (Submodule.mem_span_finset).mp hmem
      exact ⟨d, fun _ => by simpa only [smul_eq_mul] using hd⟩
    · exact ⟨fun _ => 0, fun h => absurd h hm⟩
  choose d hd using hcoeff
  have hre : x = ∑ a ∈ S, a • (∑ m ∈ (s x).support, d m a • m) := by
    conv_lhs => rw [hc]
    trans ∑ m ∈ (s x).support, ∑ a ∈ S, (d m a * a) • m
    · refine Finset.sum_congr rfl (fun m hm => ?_)
      rw [← hd m hm, Finset.sum_smul]
    · rw [Finset.sum_comm]
      refine Finset.sum_congr rfl (fun a _ => ?_)
      rw [Finset.smul_sum]
      refine Finset.sum_congr rfl (fun m _ => ?_)
      rw [mul_comm (d m a) a, ← mul_smul]
  have hexpand : ∀ b : R, ψ b x = ∑ a ∈ S, a * ψ b (∑ m ∈ (s x).support, d m a • m) := by
    intro b
    conv_lhs => rw [hre]
    rw [map_sum]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [map_smul, smul_eq_mul]
  have hdiff : ∀ k : ↥S,
      ∑ a ∈ S, ((ψ k.val (∑ m ∈ (s x).support, d m a • m) -
        (if a = k.val then 1 else 0)) * a) = 0 := by
    intro k
    have hk : k.val ∈ S := k.property
    have e1 := hexpand k.val
    have e2 : k.val = ∑ a ∈ S, (if a = k.val then 1 else 0) * a := by
      have hsum := Finset.sum_ite_eq' S k.val (fun a => a)
      simp only [hk, ↓reduceIte] at hsum
      rw [← hsum]
      refine Finset.sum_congr rfl (fun a _ => ?_)
      by_cases haj : a = k.val <;> simp [haj]
    have e3 : ψ k.val x = k.val := hψ k.val (Finset.mem_coe.mpr hk)
    have h4 : ∑ a ∈ S, (a * ψ k.val (∑ m ∈ (s x).support, d m a • m) -
        (if a = k.val then 1 else 0) * a) = 0 := by
      rw [Finset.sum_sub_distrib, ← e1, ← e2, e3, sub_self]
    calc ∑ a ∈ S, ((ψ k.val (∑ m ∈ (s x).support, d m a • m) -
          (if a = k.val then 1 else 0)) * a)
        = ∑ a ∈ S, (a * ψ k.val (∑ m ∈ (s x).support, d m a • m) -
          (if a = k.val then 1 else 0) * a) := by
            refine Finset.sum_congr rfl (fun a _ => ?_)
            ring
      _ = 0 := h4
  have hmem2 : ∀ j k : ↥S, (fun b : ↥S => ψ b.val) k
      ((fun a : ↥S => ∑ m ∈ (s x).support, d m a.val • m) j) -
      (if j = k then 1 else 0) ∈ IsLocalRing.maximalIdeal R := by
    intro j k
    change ψ k.val (∑ m ∈ (s x).support, d m j.val • m) -
      (if j = k then 1 else 0) ∈ IsLocalRing.maximalIdeal R
    have hif : (if j = k then (1 : R) else 0) = (if j.val = k.val then 1 else 0) := by
      by_cases hjk : j = k
      · subst hjk
        simp
      · have h1 : j.val ≠ k.val := by
          intro hcon
          exact hjk (Subtype.val_injective hcon)
        simp only [hjk, h1, ↓reduceIte]
    rw [hif]
    have hr := hSmin
      (fun a => ψ k.val (∑ m ∈ (s x).support, d m a • m) - (if a = k.val then 1 else 0))
      (by simpa only [smul_eq_mul] using hdiff k) j.val j.property
    exact hr
  obtain ⟨hLI, D, hD⟩ := kap_free_summand_of_pairing (κ := ↥S)
    (fun a : ↥S => ∑ m ∈ (s x).support, d m a.val • m) (fun b : ↥S => ψ b.val) hmem2
  refine ⟨Set.range (fun a : ↥S => ∑ m ∈ (s x).support, d m a.val • m),
    hLI.linearIndepOn_id, ⟨D, hD⟩, ?_⟩
  have hmem : ∀ a ∈ S, a • (∑ m ∈ (s x).support, d m a • m) ∈
      Submodule.span R (Set.range (fun a : ↥S => ∑ m ∈ (s x).support, d m a.val • m)) := by
    intro a ha
    apply Submodule.smul_mem
    apply Submodule.subset_span
    exact ⟨⟨a, ha⟩, rfl⟩
  have hsum := Submodule.sum_mem _ hmem
  rw [← hre] at hsum
  exact hsum

-- N10. basic facts about the Kaplansky projection operator
private theorem kap_kapProj_facts {R : Type*} {M : Type*} [CommRing R]
    [AddCommGroup M] [Module R M]
    (s : M →ₗ[R] (M →₀ R)) (hs : Finsupp.linearCombination R id ∘ₗ s = LinearMap.id)
    (J : Set M) :
    (∀ x, kapProj s J x ∈ Submodule.span R J) ∧
    ((∀ p ∈ J, ↑(s p).support ⊆ J) → ∀ x ∈ Submodule.span R J, kapProj s J x = x) := by
  constructor
  · intro x
    have hle : Submodule.span R (Set.range (J.indicator fun x => x)) ≤
        Submodule.span R J := by
      apply Submodule.span_le.mpr
      rintro y ⟨m, rfl⟩
      by_cases hm : m ∈ J
      · rw [Set.indicator_of_mem hm]
        exact Submodule.subset_span hm
      · rw [Set.indicator_of_notMem hm]
        exact Submodule.zero_mem _
    apply hle
    change (Finsupp.linearCombination R (J.indicator fun x => x)) (s x) ∈ _
    have h1 : (Finsupp.linearCombination R (J.indicator fun x => x)) (s x) ∈
        LinearMap.range (Finsupp.linearCombination R (J.indicator fun x => x)) :=
      ⟨s x, rfl⟩
    rw [Finsupp.range_linearCombination] at h1
    exact h1
  · intro hclosed x hx
    set f : M →₀ R := s x with hf
    have hsupp' : ↑f.support ⊆ J := by
      have hcomap : Submodule.span R J ≤ Submodule.comap s (Finsupp.supported R R J) := by
        rw [Submodule.span_le]
        intro p hp
        exact (Finsupp.mem_supported R _).mpr (hclosed p hp)
      exact (Finsupp.mem_supported R _).mp (hcomap hx)
    have hxid : x = f.sum (fun i a => a • i) := by
      have h := LinearMap.congr_fun hs x
      simp only [LinearMap.comp_apply, LinearMap.id_apply] at h
      rw [Finsupp.linearCombination_apply] at h
      simpa only [id_eq] using h.symm
    change (Finsupp.linearCombination R (J.indicator fun x => x)) f = x
    rw [hxid, Finsupp.linearCombination_apply]
    change (∑ m ∈ f.support, (f m) • (J.indicator (fun x => x) m)) =
      (∑ m ∈ f.support, (f m) • m)
    refine Finset.sum_congr rfl (fun m hm => ?_)
    rw [Set.indicator_of_mem (hsupp' hm)]

-- N8. enlarge a free summand to absorb one more element
private theorem kap_extend_free_summand {R : Type*} [CommRing R] [IsLocalRing R]
    {M : Type*} [AddCommGroup M] [Module R M] [Module.Projective R M]
    (u : Set M) (hli : LinearIndepOn R id u) (D : Submodule R M)
    (hD : IsCompl (Submodule.span R u) D) (x : M) :
    ∃ u' : Set M, ∃ D' : Submodule R M, u ⊆ u' ∧ LinearIndepOn R id u' ∧
      IsCompl (Submodule.span R u') D' ∧ x ∈ Submodule.span R u' := by
  classical
  have : Module.Projective R ↥D :=
    kap_projective_of_retract D (Submodule.projection D (Submodule.span R u) hD.symm)
      (fun x => Submodule.projection_apply_mem hD.symm x)
      (fun x => Submodule.projection_apply_of_mem_left hD.symm x.property)
  obtain ⟨v, hvli, ⟨E, hE⟩, hy⟩ := kap_exists_free_summand_mem
    (R := R) (M := ↥D) (D.projectionOnto (Submodule.span R u) hD.symm x)
  have hli2 : LinearIndepOn R id (D.subtype '' v) := by
    have hker : Disjoint (Submodule.span R v) D.subtype.ker := by
      rw [Submodule.ker_subtype]
      exact disjoint_bot_right
    exact LinearIndepOn.image hvli hker
  have hdisj : Disjoint (Submodule.span R (id '' u))
      (Submodule.span R (id '' (D.subtype '' v))) := by
    rw [Set.image_id, Set.image_id]
    have hle : Submodule.span R (D.subtype '' v) ≤ D := by
      rw [Submodule.span_image]
      exact Submodule.map_subtype_le _ _
    exact hD.disjoint.mono_right hle
  have hliU : LinearIndepOn R id (u ∪ D.subtype '' v) :=
    LinearIndepOn.union hli hli2 hdisj
  have hcompl : IsCompl (Submodule.span R (u ∪ D.subtype '' v)) (E.map D.subtype) := by
    rw [Submodule.span_union, Submodule.span_image]
    exact kap_isCompl_sup_map _ _ hD _ _ hE
  have h1 : ((Submodule.span R u).projection D hD) x ∈
      Submodule.span R (u ∪ D.subtype '' v) := by
    apply Submodule.span_mono Set.subset_union_left
    exact Submodule.projection_apply_mem hD x
  have h2 : (D.projection (Submodule.span R u) hD.symm) x ∈
      Submodule.span R (u ∪ D.subtype '' v) := by
    have hmem : ((D.projection (Submodule.span R u) hD.symm) x : M) ∈
        (Submodule.span R v).map D.subtype := by
      have hval : (D.projection (Submodule.span R u) hD.symm) x =
          D.subtype (D.projectionOnto (Submodule.span R u) hD.symm x) :=
        (Submodule.coe_projectionOnto_apply _ _).symm
      rw [hval]
      exact Submodule.mem_map_of_mem hy
    have hle2 : (Submodule.span R v).map D.subtype ≤
        Submodule.span R (u ∪ D.subtype '' v) := by
      rw [← Submodule.span_image]
      exact Submodule.span_mono Set.subset_union_right
    exact hle2 hmem
  have hmemx : x ∈ Submodule.span R (u ∪ D.subtype '' v) := by
    have hdecomp := Submodule.projection_add_projection_eq_self hD x
    rw [← hdecomp]
    exact Submodule.add_mem _ h1 h2
  exact ⟨u ∪ D.subtype '' v, E.map D.subtype, Set.subset_union_left, hliU, hcompl, hmemx⟩

-- N9a. countably generated projective modules over a local ring are free
private theorem kap_free_of_projective_of_countable_span {R : Type*} [CommRing R] [IsLocalRing R]
    {M : Type*} [AddCommGroup M] [Module R M] [Module.Projective R M]
    (g : Set M) (hgcount : g.Countable) (hgspan : Submodule.span R g = ⊤) :
    Module.Free R M := by
  classical
  have hg0 : (insert (0 : M) g).Countable := by
    rw [← Set.singleton_union]
    exact (Set.finite_singleton 0).countable.union hgcount
  have hspan0 : Submodule.span R (insert (0 : M) g) = ⊤ := by
    rw [← hgspan]
    refine le_antisymm ?_ (Submodule.span_mono (Set.subset_insert 0 g))
    rw [Submodule.span_le]
    exact Set.insert_subset (Submodule.zero_mem _) Submodule.subset_span
  obtain ⟨f, hf⟩ := hg0.exists_eq_range (Set.insert_nonempty 0 g)
  have hspanf : Submodule.span R (Set.range f) = ⊤ := by
    rw [← hf]
    exact hspan0
  have hstep : ∀ p : Set M × Submodule R M, LinearIndepOn R id p.1 →
      IsCompl (Submodule.span R p.1) p.2 → ∀ x : M,
      ∃ p' : Set M × Submodule R M, p.1 ⊆ p'.1 ∧ LinearIndepOn R id p'.1 ∧
        IsCompl (Submodule.span R p'.1) p'.2 ∧ x ∈ Submodule.span R p'.1 := by
    rintro ⟨u, D⟩ hli hD x
    obtain ⟨u', D', hsub, hli', hD', hmem⟩ := kap_extend_free_summand u hli D hD x
    exact ⟨(u', D'), hsub, hli', hD', hmem⟩
  choose P' hPsub hPli hPcompl hPmem using hstep
  have h0li : LinearIndepOn R id (∅ : Set M) := linearIndepOn_empty R id
  have h0compl : IsCompl (Submodule.span R (∅ : Set M)) (⊤ : Submodule R M) := by
    rw [Submodule.span_empty]
    exact isCompl_bot_top
  let seq : ℕ → { p : Set M × Submodule R M //
      LinearIndepOn R id p.1 ∧ IsCompl (Submodule.span R p.1) p.2 } :=
    fun n => n.rec ⟨(∅, ⊤), h0li, h0compl⟩
      (fun n q => ⟨P' q.val q.property.1 q.property.2 (f n),
        hPli q.val q.property.1 q.property.2 (f n),
        hPcompl q.val q.property.1 q.property.2 (f n)⟩)
  have hmono : Monotone (fun n => (seq n).val.1) := by
    apply monotone_nat_of_le_succ
    intro n
    exact hPsub _ _ _ _
  have hLIU : LinearIndepOn R id (⋃ n, (seq n).val.1) :=
    linearIndepOn_iUnion_of_directed (Monotone.directed_le hmono) (fun n => (seq n).property.1)
  have hfn : ∀ n, f n ∈ Submodule.span R (⋃ n, (seq n).val.1) := by
    intro n
    have h1 : f n ∈ Submodule.span R ((seq (n + 1)).val.1) := hPmem _ _ _ _
    exact Submodule.span_mono (Set.subset_iUnion (fun n => (seq n).val.1) (n + 1)) h1
  have htop : Submodule.span R (⋃ n, (seq n).val.1) = ⊤ := by
    rw [eq_top_iff, ← hspanf, Submodule.span_le]
    rintro y ⟨n, rfl⟩
    exact hfn n
  have hspanU : ⊤ ≤ Submodule.span R
      (Set.range (Subtype.val : ↥(⋃ n, (seq n).val.1) → M)) := by
    rw [Subtype.range_coe]
    exact le_of_eq htop.symm
  exact Module.Free.of_basis (Module.Basis.mk hLIU.linearIndependent hspanU)

-- N9b. submodule form of the countable case
private theorem kap_exists_basis_of_countable_span {R : Type*} [CommRing R] [IsLocalRing R]
    {M : Type*} [AddCommGroup M] [Module R M]
    (N : Submodule R M) [Module.Projective R ↥N]
    (T : Set M) (hTcount : T.Countable) (hTspan : Submodule.span R T = N) :
    ∃ c : Set M, LinearIndepOn R id c ∧ Submodule.span R c = N := by
  classical
  subst hTspan
  have hfree : Module.Free R ↥(Submodule.span R T) :=
    kap_free_of_projective_of_countable_span (Subtype.val ⁻¹' T)
      (hTcount.preimage Subtype.val_injective)
      Submodule.span_span_coe_preimage
  have := hfree
  let b := Module.Free.chooseBasis R ↥(Submodule.span R T)
  refine ⟨Set.range ((Submodule.span R T).subtype ∘ ⇑b), ?_, ?_⟩
  · have hli : LinearIndependent R (⇑(Submodule.span R T).subtype ∘ ⇑b) :=
      LinearIndependent.map' b.linearIndependent _ (Submodule.ker_subtype _)
    exact hli.linearIndepOn_id
  · rw [Set.range_comp, Submodule.span_image, b.span_eq, Submodule.map_subtype_top]

-- N11. the complement of a closed span inside a larger closed span
private theorem kap_closed_complement_facts {R : Type*} {M : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] [Module.Projective R M]
    (s : M →ₗ[R] (M →₀ R)) (hs : Finsupp.linearCombination R id ∘ₗ s = LinearMap.id)
    (J J₁ : Set M) (hJ : ∀ p ∈ J, ↑(s p).support ⊆ J)
    (hJ₁ : ∀ p ∈ J₁, ↑(s p).support ⊆ J₁) :
    Disjoint (Submodule.span R J)
      (Submodule.span R (J ∪ J₁) ⊓ LinearMap.ker (kapProj s J)) ∧
    Submodule.span R J ⊔ (Submodule.span R (J ∪ J₁) ⊓ LinearMap.ker (kapProj s J)) =
      Submodule.span R (J ∪ J₁) ∧
    Module.Projective R ↥(Submodule.span R (J ∪ J₁) ⊓ LinearMap.ker (kapProj s J)) ∧
    (Submodule.span R (J ∪ J₁) ⊓ LinearMap.ker (kapProj s J)) =
      Submodule.span R (((LinearMap.id - kapProj s J : M →ₗ[R] M)) '' J₁) := by
  classical
  obtain ⟨hmemJ, hfixJ⟩ := kap_kapProj_facts s hs J
  obtain ⟨hmemJ', hfixJ'⟩ := kap_kapProj_facts s hs (J ∪ J₁)
  have hJ'closed : ∀ p ∈ J ∪ J₁, ↑(s p).support ⊆ J ∪ J₁ := by
    rintro p (hp | hp)
    · exact Set.Subset.trans (hJ p hp) Set.subset_union_left
    · exact Set.Subset.trans (hJ₁ p hp) Set.subset_union_right
  have hdisj : Disjoint (Submodule.span R J)
      (Submodule.span R (J ∪ J₁) ⊓ LinearMap.ker (kapProj s J)) := by
    rw [Submodule.disjoint_def]
    intro x hxJ hxC
    obtain ⟨-, hxker⟩ := Submodule.mem_inf.mp hxC
    have h0 : kapProj s J x = 0 := hxker
    have hfix := hfixJ hJ x hxJ
    rw [h0] at hfix
    exact hfix.symm
  have hsup : Submodule.span R J ⊔
      (Submodule.span R (J ∪ J₁) ⊓ LinearMap.ker (kapProj s J)) =
      Submodule.span R (J ∪ J₁) := by
    apply le_antisymm
    · refine sup_le (Submodule.span_mono Set.subset_union_left) inf_le_left
    · rw [Submodule.span_le]
      intro x hx
      have hπx : kapProj s J x ∈ Submodule.span R J := hmemJ x
      have hππ : kapProj s J (kapProj s J x) = kapProj s J x := hfixJ hJ _ (hmemJ x)
      have hker : x - kapProj s J x ∈ LinearMap.ker (kapProj s J) := by
        change kapProj s J (x - kapProj s J x) = 0
        rw [map_sub, hππ, sub_self]
      have hmem : x - kapProj s J x ∈
          Submodule.span R (J ∪ J₁) ⊓ LinearMap.ker (kapProj s J) :=
        ⟨Submodule.sub_mem _ (Submodule.subset_span hx)
          (Submodule.span_mono Set.subset_union_left (hmemJ x)), hker⟩
      have hsplit : kapProj s J x + (x - kapProj s J x) = x := add_sub_cancel _ _
      rw [← hsplit]
      exact Submodule.mem_sup.mpr ⟨_, hπx, _, hmem, rfl⟩
  have hCproj : Module.Projective R
      ↥(Submodule.span R (J ∪ J₁) ⊓ LinearMap.ker (kapProj s J)) := by
    apply kap_projective_of_retract _
        (((LinearMap.id - kapProj s J : M →ₗ[R] M)) ∘ₗ kapProj s (J ∪ J₁))
    · intro x
      refine Submodule.mem_inf.mpr ⟨?_, ?_⟩
      · change (((LinearMap.id - kapProj s J : M →ₗ[R] M)) ∘ₗ kapProj s (J ∪ J₁)) x ∈ _
        rw [LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.id_apply]
        exact Submodule.sub_mem _
          (hmemJ' x)
          (Submodule.span_mono Set.subset_union_left (hmemJ _))
      · change kapProj s J ((((LinearMap.id - kapProj s J : M →ₗ[R] M)) ∘ₗ kapProj s (J ∪ J₁)) x) =
          0
        rw [LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.id_apply, map_sub]
        have hpp : kapProj s J (kapProj s J (kapProj s (J ∪ J₁) x)) =
            kapProj s J (kapProj s (J ∪ J₁) x) := hfixJ hJ _ (hmemJ _)
        rw [hpp, sub_self]
    · intro x
      obtain ⟨hxspan, hxker⟩ := Submodule.mem_inf.mp x.property
      rw [LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.id_apply]
      have hfix : kapProj s (J ∪ J₁) (x : M) = (x : M) := hfixJ' hJ'closed _ hxspan
      have hker0 : kapProj s J (x : M) = 0 := hxker
      rw [hfix, hker0, sub_zero]
  have hCeq : (Submodule.span R (J ∪ J₁) ⊓ LinearMap.ker (kapProj s J)) =
      Submodule.span R (((LinearMap.id - kapProj s J : M →ₗ[R] M)) '' J₁) := by
    apply le_antisymm
    · intro x hx
      obtain ⟨hxspan, hxker⟩ := Submodule.mem_inf.mp hx
      have hxeq : ((LinearMap.id - kapProj s J : M →ₗ[R] M)) x = x := by
        rw [LinearMap.sub_apply, LinearMap.id_apply]
        have h0 : kapProj s J x = 0 := hxker
        rw [h0, sub_zero]
      have himg : ((LinearMap.id - kapProj s J : M →ₗ[R] M)) x ∈
          Submodule.span R (((LinearMap.id - kapProj s J : M →ₗ[R] M)) '' J₁) := by
        have hmap : ((LinearMap.id - kapProj s J : M →ₗ[R] M)) x ∈
            Submodule.map ((LinearMap.id - kapProj s J : M →ₗ[R] M)) (Submodule.span R (J ∪ J₁)) :=
          Submodule.mem_map_of_mem hxspan
        rw [Submodule.map_span, Set.image_union, Submodule.span_union] at hmap
        have hJbot : Submodule.span R (((LinearMap.id - kapProj s J : M →ₗ[R] M)) '' J) = ⊥ := by
          rw [Submodule.span_eq_bot]
          rintro y ⟨j, hjJ, rfl⟩
          change ((LinearMap.id - kapProj s J : M →ₗ[R] M)) j = 0
          rw [LinearMap.sub_apply, LinearMap.id_apply]
          have hjj : kapProj s J j = j := hfixJ hJ _ (Submodule.subset_span hjJ)
          rw [hjj, sub_self]
        rw [hJbot, bot_sup_eq] at hmap
        exact hmap
      rwa [hxeq] at himg
    · rw [Submodule.span_le]
      rintro y ⟨j, hjJ₁, rfl⟩
      refine Submodule.mem_inf.mpr ⟨?_, ?_⟩
      · rw [LinearMap.sub_apply, LinearMap.id_apply]
        exact Submodule.sub_mem _ (Submodule.subset_span (Set.mem_union_right _ hjJ₁))
          (Submodule.span_mono Set.subset_union_left (hmemJ _))
      · change kapProj s J (((LinearMap.id - kapProj s J : M →ₗ[R] M)) j) = 0
        rw [LinearMap.sub_apply, LinearMap.id_apply, map_sub]
        have hjj : kapProj s J (kapProj s J j) = kapProj s J j := hfixJ hJ _ (hmemJ j)
        rw [hjj, sub_self]
  exact ⟨hdisj, hsup, hCproj, hCeq⟩

-- N13. extend a closed pair to absorb one more point
private theorem kap_extend_closed_pair {R : Type*} [CommRing R] [IsLocalRing R]
    {M : Type*} [AddCommGroup M] [Module R M] [Module.Projective R M]
    (s : M →ₗ[R] (M →₀ R)) (hs : Finsupp.linearCombination R id ∘ₗ s = LinearMap.id)
    (J b : Set M) (hJ : ∀ p ∈ J, ↑(s p).support ⊆ J)
    (hb : LinearIndepOn R id b) (hbspan : Submodule.span R b = Submodule.span R J)
    (m : M) :
    ∃ J' : Set M, ∃ b' : Set M, (∀ p ∈ J', ↑(s p).support ⊆ J') ∧
      LinearIndepOn R id b' ∧ Submodule.span R b' = Submodule.span R J' ∧
      J ⊆ J' ∧ b ⊆ b' ∧ m ∈ J' := by
  classical
  obtain ⟨J₁, hJ₁count, hmJ₁, hJ₁closed⟩ := kap_exists_countable_closed s m
  have hJ'closed : ∀ p ∈ J ∪ J₁, ↑(s p).support ⊆ J ∪ J₁ := by
    rintro p (hp | hp)
    · exact Set.Subset.trans (hJ p hp) Set.subset_union_left
    · exact Set.Subset.trans (hJ₁closed p hp) Set.subset_union_right
  obtain ⟨hdisj, hsup, hCproj, hCeq⟩ := kap_closed_complement_facts s hs J J₁ hJ hJ₁closed
  have := hCproj
  obtain ⟨c, hcli, hcspan⟩ := kap_exists_basis_of_countable_span
    (Submodule.span R (J ∪ J₁) ⊓ LinearMap.ker (kapProj s J))
    (((LinearMap.id - kapProj s J : M →ₗ[R] M)) '' J₁)
    (hJ₁count.image _) (hCeq.symm)
  refine ⟨J ∪ J₁, b ∪ c, hJ'closed, ?_, ?_, fun x hx => Or.inl hx,
    fun x hx => Or.inl hx, Or.inr hmJ₁⟩
  · have hdisj2 : Disjoint (Submodule.span R (id '' b))
      (Submodule.span R (id '' c)) := by
      rw [Set.image_id, Set.image_id, hbspan, hcspan]
      exact hdisj
    exact LinearIndepOn.union hb hcli hdisj2
  · rw [Submodule.span_union, hbspan, hcspan]
    exact hsup

-- N14aux. Zorn assembly: the maximal closed pair spans everything
private theorem kap_projective_local_free_aux {R : Type*} {M : Type*} [CommRing R] [IsLocalRing R]
    [AddCommGroup M] [Module R M] [Module.Projective R M] :
    Module.Free R M := by
  classical
  obtain ⟨s, hs⟩ := Module.projective_def'.mp (inferInstance : Module.Projective R M)
  set P : Set (Set M × Set M) := { p | (∀ q ∈ p.1, ↑(s q).support ⊆ p.1) ∧
    LinearIndepOn R id p.2 ∧ Submodule.span R p.2 = Submodule.span R p.1 } with hPdef
  have hPmem : ∀ p : Set M × Set M, p ∈ P ↔ ((∀ q ∈ p.1, ↑(s q).support ⊆ p.1) ∧
      LinearIndepOn R id p.2 ∧ Submodule.span R p.2 = Submodule.span R p.1) :=
    fun p => Iff.rfl
  have hmem0 : (∅, ∅) ∈ P := by
    rw [hPmem]
    refine ⟨?_, linearIndepOn_empty R id, ?_⟩
    · intro q hq
      exact absurd hq (Set.notMem_empty q)
    · rfl
  have hbound : ∀ c ⊆ P, IsChain (fun x1 x2 => x1 ≤ x2) c → ∀ y ∈ c,
      ∃ ub ∈ P, ∀ z ∈ c, z ≤ ub := by
    intro c hcsub hchain y hy
    have hunion1 : ∀ (p : M) (h : p ∈ ⋃ q ∈ c, q.1), ∃ r ∈ c, p ∈ r.1 := by
      intro p hp
      rw [Set.mem_iUnion] at hp
      obtain ⟨r, hr⟩ := hp
      rw [Set.mem_iUnion] at hr
      obtain ⟨hmem, hpr⟩ := hr
      exact ⟨r, hmem, hpr⟩
    have hunion2 : ∀ (p : M) (h : p ∈ ⋃ q ∈ c, q.2), ∃ r ∈ c, p ∈ r.2 := by
      intro p hp
      rw [Set.mem_iUnion] at hp
      obtain ⟨r, hr⟩ := hp
      rw [Set.mem_iUnion] at hr
      obtain ⟨hmem, hpr⟩ := hr
      exact ⟨r, hmem, hpr⟩
    refine ⟨(⋃ p ∈ c, p.1, ⋃ p ∈ c, p.2), ?_, ?_⟩
    · rw [hPmem]
      refine ⟨?_, ?_, ?_⟩
      · intro p hp
        obtain ⟨q, hq, hpq⟩ := hunion1 p hp
        have hqP := (hPmem _).mp (hcsub hq)
        exact Set.Subset.trans (hqP.1 _ hpq) (Set.subset_biUnion_of_mem hq)
      · have hunion : (⋃ p ∈ c, p.2) = ⋃ q : ↥c, (q.val).2 := by
          ext p
          constructor
          · intro hp
            obtain ⟨r, hr, hpr⟩ := hunion2 p hp
            rw [Set.mem_iUnion]
            exact ⟨⟨r, hr⟩, hpr⟩
          · intro hp
            rw [Set.mem_iUnion] at hp
            obtain ⟨r, hr⟩ := hp
            exact Set.mem_biUnion r.property hr
        rw [hunion]
        refine linearIndepOn_iUnion_of_directed ?_ (fun q => ((hPmem _).mp (hcsub q.property)).2.1)
        intro q1 q2
        rcases hchain.total q1.property q2.property with h | h
        · exact ⟨q2, (Prod.mk_le_mk.mp h).2, le_rfl⟩
        · exact ⟨q1, le_rfl, (Prod.mk_le_mk.mp h).2⟩
      · apply le_antisymm
        · rw [Submodule.span_le]
          intro y hy2
          obtain ⟨p, hp, hyp⟩ := hunion2 y hy2
          have hpp := (hPmem _).mp (hcsub hp)
          have hmem : y ∈ Submodule.span R p.1 := hpp.2.2 ▸ Submodule.subset_span hyp
          exact Submodule.span_mono (Set.subset_biUnion_of_mem hp) hmem
        · rw [Submodule.span_le]
          intro y hy2
          obtain ⟨p, hp, hyp⟩ := hunion1 y hy2
          have hpp := (hPmem _).mp (hcsub hp)
          have hmem : y ∈ Submodule.span R p.2 := hpp.2.2.symm ▸ Submodule.subset_span hyp
          exact Submodule.span_mono (Set.subset_biUnion_of_mem hp) hmem
    · intro z hz
      exact ⟨Set.subset_biUnion_of_mem hz, Set.subset_biUnion_of_mem hz⟩
  obtain ⟨⟨J, b⟩, hleb, hmax⟩ := zorn_le_nonempty₀ P hbound (∅, ∅) hmem0
  have hJb := (hPmem _).mp hmax.prop
  have hJuniv : J = Set.univ := by
    rw [Set.eq_univ_iff_forall]
    intro m
    obtain ⟨J', b', hJ'closed, hLI', hspan', hJJ', hbb', hmJ'⟩ :=
      kap_extend_closed_pair s hs J b hJb.1 hJb.2.1 hJb.2.2 m
    have hmem' : (J', b') ∈ P := (hPmem _).mpr ⟨hJ'closed, hLI', hspan'⟩
    have hle : (J, b) ≤ (J', b') := Prod.mk_le_mk.mpr ⟨hJJ', hbb'⟩
    have hge := hmax.le_of_ge hmem' hle
    exact (Prod.mk_le_mk.mp hge).1 hmJ'
  have htop : Submodule.span R b = ⊤ := by
    rw [hJb.2.2, hJuniv, Submodule.span_univ]
  have hspanU : ⊤ ≤ Submodule.span R (Set.range (Subtype.val : ↥b → M)) := by
    rw [Subtype.range_coe]
    exact le_of_eq htop.symm
  exact Module.Free.of_basis (Module.Basis.mk hJb.2.1.linearIndependent hspanU)

end MathlibExt.Kaplansky

section
namespace MathlibExt.Algebra.Module.KaplanskyProjectiveWanted

/-!
# Kaplansky's theorem on projective modules over local rings

Proves the arbitrary-rank freeness of projective modules over commutative local rings.
-/

/--
**Kaplansky's theorem on projective modules over local rings.** Every projective module over a
commutative local ring is free.

Proves `Wanted` entry `kaplansky_projective_local_free`.

Source: I. Kaplansky, Projective Modules, Ann. Math. 68 (1958), 372-377, DOI 10.2307/1970252.
-/
theorem kaplansky_projective_local_free
    {R : Type*} {M : Type*} [CommRing R] [IsLocalRing R]
    [AddCommGroup M] [Module R M] [Module.Projective R M] :
    Module.Free R M := by
  exact MathlibExt.Kaplansky.kap_projective_local_free_aux

end MathlibExt.Algebra.Module.KaplanskyProjectiveWanted
end
