/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.AlgebraicGeometry.CanonicalKoszulDeterminants

import Mathlib.LinearAlgebra.Determinant

/-
The alternating-map comparison is adapted from
`Mathlib/LinearAlgebra/Determinant.lean` (leanprover-community/mathlib4,
revision fc4f59e577feb1a4956671bc04ac18aaaf8cd842):
Copyright (c) 2019 Johannes Hölzl. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
Authors: Johannes Hölzl, Patrick Massot, Casper Putz, Anne Baanen
-/

/-!
# Independence of actual acyclic torsion

The literal kernel-basis/lift torsion is independent of the adapted bases
in the original cochain degree order.

Sources: Knudsen--Mumford, *The projectivity of the moduli space of stable
curves I: preliminaries on 'det' and 'Div'*, Math. Scand. 39 (1976), 19--55,
Chapter I, pp. 21 and 31--34 (the determinant construction). The Lean proof
keeps its own fixed degree order.
-/

set_option autoImplicit false
@[expose] public noncomputable section

namespace WantedExt.AlgebraicGeometry.CanonicalKoszulDeterminants

open CategoryTheory CategoryTheory.Limits _root_.AlgebraicGeometry
open MathlibExt.AlgebraicGeometry
open BoundedProjectiveDeterminants GlobalBoundedDeterminantModels
open MathlibExt.AlgebraicGeometry.CanonicalKoszulDeterminants
open scoped TensorProduct

private theorem alternating_basis_change (R M N : Type*) [CommRing R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] (n : ℕ)
    (b : Module.Basis (Fin n) R M) (f : M [⋀^Fin n]→ₗ[R] N) (v : Fin n → M) :
    f v = b.det v • f b := by
  classical
  have h : f = b.det.smulRight (f b) := by
    apply b.ext_alternating
    intro i hi
    let σ : Equiv.Perm (Fin n) := Equiv.ofBijective i
      (Finite.injective_iff_bijective.mp hi)
    change f (b ∘ σ) = (b.det.smulRight (f b)) (b ∘ σ)
    simp [AlternatingMap.map_perm, Module.Basis.det_self]
  exact congrArg (fun g : M [⋀^Fin n]→ₗ[R] N => g v) h

private theorem wedge_basis_change (R M : Type*) [CommRing R]
    [AddCommGroup M] [Module R M] (n : ℕ)
    (b : Module.Basis (Fin n) R M) (v : Fin n → M) :
    ExteriorAlgebra.ιMulti R n v = b.det v • ExteriorAlgebra.ιMulti R n b := by
  exact alternating_basis_change R M (ExteriorAlgebra R M) n b
    (ExteriorAlgebra.ιMulti R n) v

private theorem exterior_basis_top (R M : Type*) [CommRing R]
    [AddCommGroup M] [Module R M] (n : ℕ) (b : Module.Basis (Fin n) R M) :
    b.ExteriorAlgebra Finset.univ = ExteriorAlgebra.ιMulti R n b := by
  rw [ExteriorAlgebra.basis_apply_ofCard b (Finset.card_fin n)]
  simp only [ExteriorAlgebra.ιMulti_family]
  congr 1
  funext i
  change b ((Finset.univ.orderEmbOfFin (Finset.card_fin n)) i) = b i
  exact congrArg b
    (StrictMono.apply_eq (Finset.orderEmbOfFin Finset.univ (Finset.card_fin n)).strictMono)

private theorem coordinate_wedge (R M : Type*) [CommRing R]
    [AddCommGroup M] [Module R M] (n : ℕ)
    (b : Module.Basis (Fin n) R M) (v : Fin n → M) :
    b.ExteriorAlgebra.coord Finset.univ (ExteriorAlgebra.ιMulti R n v) = b.det v := by
  rw [wedge_basis_change R M n b v, ← exterior_basis_top R M n b]
  simp

private theorem exterior_coordinate_of_degree_ne (R M : Type*) [CommRing R]
    [AddCommGroup M] [Module R M] (n k : ℕ) (b : Module.Basis (Fin n) R M)
    (x : ExteriorAlgebra R M) (hx : x ∈ ⋀[R]^k M) (hkn : k ≠ n) :
    b.ExteriorAlgebra.coord Finset.univ x = 0 := by
  classical
  simp only [Module.Basis.coord_apply, Module.Basis.ExteriorAlgebra,
    Module.Basis.repr_reindex]
  exact DirectSum.IsInternal.collectedBasis_repr_of_mem_ne
    (DirectSum.Decomposition.isInternal (fun d => ⋀[R]^d M)) b.exteriorPower
    (by simpa using hkn) hx

private theorem exterior_coordinate_basis_change (R M : Type*) [CommRing R]
    [AddCommGroup M] [Module R M] (n : ℕ)
    (b c : Module.Basis (Fin n) R M) :
    b.ExteriorAlgebra.coord Finset.univ =
      b.det c • c.ExteriorAlgebra.coord Finset.univ := by
  classical
  apply c.ExteriorAlgebra.ext
  intro s
  by_cases hs : s = Finset.univ
  · subst s
    rw [exterior_basis_top R M n c, coordinate_wedge R M n b c]
    simp [← exterior_basis_top R M n c]
  · have hsn : s.card ≠ n := by
      intro h
      apply hs
      exact Finset.eq_univ_of_card s (by simpa using h)
    have hm : c.ExteriorAlgebra s ∈ ⋀[R]^s.card M := by
      rw [ExteriorAlgebra.basis_apply_ofCard c rfl]
      exact (exteriorPower.ιMulti_family R s.card c (Set.powersetCard.ofCard rfl)).property
    rw [exterior_coordinate_of_degree_ne R M n s.card b _ hm hsn]
    simp [Module.Basis.coord_apply, Module.Basis.repr_self, hs]

private theorem adapted_basis_determinant (R K M Q : Type*) [CommRing R]
    [AddCommGroup K] [Module R K] [AddCommGroup M] [Module R M]
    [AddCommGroup Q] [Module R Q] (k l : ℕ)
    (g : K →ₗ[R] M) (f : M →ₗ[R] Q) (hfg : ∀ x, f (g x) = 0)
    (bk ck : Module.Basis (Fin k) R K) (bq cq : Module.Basis (Fin l) R Q)
    (bl cl : Fin l → M) (hbl : ∀ j, f (bl j) = bq j)
    (hcl : ∀ j, f (cl j) = cq j)
    (b c : Module.Basis (Fin k ⊕ Fin l) R M)
    (hb : ⇑b = Sum.elim (fun j => g (bk j)) bl)
    (hc : ⇑c = Sum.elim (fun j => g (ck j)) cl) :
    b.det c = bk.det ck * bq.det cq := by
  classical
  have hleft (i : Fin k) : (b.coord (Sum.inl i)).comp g = bk.coord i := by
    apply bk.ext
    intro j
    simp only [LinearMap.comp_apply]
    have hj : g (bk j) = b (Sum.inl j) := congrFun hb (Sum.inl j) |>.symm
    rw [hj]
    simp [Module.Basis.coord_apply, Finsupp.single_apply]
  have hright (i : Fin l) : (bq.coord i).comp f = b.coord (Sum.inr i) := by
    apply b.ext
    intro j
    simp only [LinearMap.comp_apply, Module.Basis.coord_apply, Module.Basis.repr_self]
    cases j with
    | inl j =>
      rw [congrFun hb (Sum.inl j)]
      simp [hfg]
    | inr j =>
      rw [congrFun hb (Sum.inr j)]
      simp [hbl, Finsupp.single_apply]
  let u : Matrix (Fin k) (Fin l) R := fun i j => b.coord (Sum.inl i) (cl j)
  have hmatrix : b.toMatrix c = Matrix.fromBlocks (bk.toMatrix ck) u 0
      (bq.toMatrix cq) := by
    ext i j
    cases i with
    | inl i =>
      cases j with
      | inl j =>
        change b.coord (Sum.inl i) (c (Sum.inl j)) = bk.coord i (ck j)
        rw [congrFun hc (Sum.inl j)]
        exact congrArg (fun q : K →ₗ[R] R => q (ck j)) (hleft i)
      | inr j =>
        change b.coord (Sum.inl i) (c (Sum.inr j)) = b.coord (Sum.inl i) (cl j)
        rw [congrFun hc (Sum.inr j)]
        rfl
    | inr i =>
      cases j with
      | inl j =>
        change b.coord (Sum.inr i) (c (Sum.inl j)) = 0
        rw [← hright i, LinearMap.comp_apply, congrFun hc (Sum.inl j)]
        simp [hfg]
      | inr j =>
        change b.coord (Sum.inr i) (c (Sum.inr j)) = bq.coord i (cq j)
        rw [← hright i, LinearMap.comp_apply, congrFun hc (Sum.inr j)]
        simpa only [Sum.elim_inr] using congrArg (bq.coord i) (hcl j)
  rw [Module.Basis.det_apply, hmatrix, Matrix.det_fromBlocks_zero₂₁]
  rfl

private theorem adapted_fin_determinant (R K M Q : Type*) [CommRing R]
    [AddCommGroup K] [Module R K] [AddCommGroup M] [Module R M]
    [AddCommGroup Q] [Module R Q] (k l : ℕ)
    (g : K →ₗ[R] M) (f : M →ₗ[R] Q) (hfg : ∀ x, f (g x) = 0)
    (bk ck : Module.Basis (Fin k) R K) (bq cq : Module.Basis (Fin l) R Q)
    (bl cl : Fin l → M) (hbl : ∀ j, f (bl j) = bq j)
    (hcl : ∀ j, f (cl j) = cq j)
    (b c : Module.Basis (Fin (k + l)) R M)
    (hb : ⇑b = Fin.append (fun j => g (bk j)) bl)
    (hc : ⇑c = Fin.append (fun j => g (ck j)) cl) :
    b.det c = bk.det ck * bq.det cq := by
  classical
  let b' := b.reindex finSumFinEquiv.symm
  let c' := c.reindex finSumFinEquiv.symm
  have hb' : ⇑b' = Sum.elim (fun j => g (bk j)) bl := by
    funext j
    cases j <;> simp [b', Module.Basis.reindex_apply, hb]
  have hc' : ⇑c' = Sum.elim (fun j => g (ck j)) cl := by
    funext j
    cases j <;> simp [c', Module.Basis.reindex_apply, hc]
  have h := adapted_basis_determinant R K M Q k l g f hfg bk ck bq cq bl cl
    hbl hcl b' c' hb' hc'
  simpa [b', c', Module.Basis.det_reindex, Module.Basis.coe_reindex,
    Function.comp_def] using h

private theorem term_determinant_factor (R : Type) [CommRing R]
    (C : BoundedProjectiveDeterminants.Complex R) (A : AdaptedBases R C)
    (kb : ∀ i : ℤ, Module.Basis (Fin (A.kernelRank i)) R
      (LinearMap.ker ((C.cochain.d i (i + 1)).hom)))
    (lift : ∀ i : ℤ, Fin (A.kernelRank (i + 1)) → C.cochain.X i)
    (hl : ∀ (i : ℤ) (j : Fin (A.kernelRank (i + 1))),
      (C.cochain.d i (i + 1)) (lift i j) = (kb (i + 1) j).val)
    (tb : ∀ i : ℤ, Module.Basis (Fin (A.kernelRank i + A.kernelRank (i + 1))) R
      (C.cochain.X i))
    (ht : ∀ i : ℤ, ⇑(tb i) = Fin.append (fun j => (kb i j).val) (lift i)) (i : ℤ) :
    (A.termBasis i).det (tb i) =
      (A.kernelBasis i).det (kb i) * (A.kernelBasis (i + 1)).det (kb (i + 1)) := by
  classical
  let f : C.cochain.X i →ₗ[R] LinearMap.ker ((C.cochain.d (i + 1) ((i + 1) + 1)).hom) :=
    ((C.cochain.d i (i + 1)).hom).codRestrict _ (by
      intro x
      change (C.cochain.d (i + 1) ((i + 1) + 1)) ((C.cochain.d i (i + 1)) x) = 0
      exact congrArg (fun q : C.cochain.X i ⟶ C.cochain.X ((i + 1) + 1) => q x)
        (C.cochain.d_comp_d i (i + 1) ((i + 1) + 1)))
  apply adapted_fin_determinant R _ _ _ _ _
    (LinearMap.ker ((C.cochain.d i (i + 1)).hom)).subtype f
    (fun x => Subtype.ext x.property) (A.kernelBasis i) (kb i)
    (A.kernelBasis (i + 1)) (kb (i + 1)) (A.lift i) (lift i)
    (fun j => Subtype.ext (A.lift_source i j)) (fun j => Subtype.ext (hl i j))
    (A.termBasis i) (tb i) (A.termBasis_source i) (ht i)

private theorem tensorVector_scale (R : Type) [CommRing R]
    (C : BoundedProjectiveDeterminants.Complex R) (A B : FreeBases R C)
    (u : ℤ → Rˣ) (h : ∀ i, termVector R C B i = (u i : R) • termVector R C A i)
    (is : List ℤ) :
    tensorVector R C B is = (((is.map u).prod : Rˣ) : R) • tensorVector R C A is := by
  induction is with
  | nil =>
    change (1 : R) = ((1 : Rˣ) : R) • (1 : R)
    simp
  | cons i is ih =>
    change termVector R C B i ⊗ₜ[R] tensorVector R C B is =
      (((u i) * (is.map u).prod : Rˣ) : R) •
        (termVector R C A i ⊗ₜ[R] tensorVector R C A is)
    rw [h i, ih]
    simp [TensorProduct.smul_tmul', TensorProduct.tmul_smul, smul_smul, mul_comm]

private theorem eqToIso_apply_cast (R : Type) [CommRing R] (M N : ModuleCat.{0} R)
    (h : M = N) (x : N) :
    (eqToIso h).toLinearEquiv (cast (congrArg (fun P : ModuleCat.{0} R => ↥P) h.symm) x) = x := by
  cases h
  rfl

private theorem termVector_scale (R : Type) [CommRing R]
    (C : BoundedProjectiveDeterminants.Complex R) (A B : FreeBases R C)
    (hr : A.rank = B.rank) (i : ℤ) :
    ∃ t : Rˣ, (t : R) =
      (A.basis i).det ((B.basis i).reindex (finCongr (congrFun hr i)).symm) ∧
      termVector R C B i = ((if Even i then t else t⁻¹ : Rˣ) : R) •
        termVector R C A i := by
  classical
  cases B with
  | mk rank basis mem =>
    dsimp only at hr
    subst rank
    let t := ((A.basis i).isUnit_det (basis i)).unit
    refine ⟨t, ?_, ?_⟩
    · simp [t]
    · by_cases hi : Even i
      · have hw : basisWedge R (basis i) (mem i) = (t : R) •
            basisWedge R (A.basis i) (A.wedge_mem i) := by
          apply Subtype.ext
          change ExteriorAlgebra.ιMulti R (A.rank i) (basis i) =
            (t : R) • ExteriorAlgebra.ιMulti R (A.rank i) (A.basis i)
          have ht : (t : R) = (A.basis i).det (basis i) :=
            ((A.basis i).isUnit_det (basis i)).unit_spec
          rw [ht]
          exact wedge_basis_change R _ _ _ _
        let he : term R C i = ModuleCat.of R
            (ProjectiveDeterminantModules.determinantModule R (C.cochain.X i)) := by
          simp [term, hi]
        let e := eqToIso he
        have heval (D : FreeBases R C) : e.toLinearEquiv (termVector R C D i) =
            basisWedge R (D.basis i) (D.wedge_mem i) := by
          simp only [termVector, dite_eq_left hi]
          exact eqToIso_apply_cast R _ _ he _
        apply e.toLinearEquiv.injective
        rw [map_smul]
        simp only [heval, ite_eq_left hi]
        exact hw
      · have hc : basisCoordinate R (basis i) = ((t⁻¹ : Rˣ) : R) •
            basisCoordinate R (A.basis i) := by
          apply LinearMap.ext
          intro x
          change (basis i).ExteriorAlgebra.coord Finset.univ x.val =
            ((t⁻¹ : Rˣ) : R) * (A.basis i).ExteriorAlgebra.coord Finset.univ x.val
          rw [Module.Basis.det_inv]
          exact congrArg (fun f : ExteriorAlgebra R (C.cochain.X i) →ₗ[R] R => f x.val)
            (exterior_coordinate_basis_change R _ _ (basis i) (A.basis i))
        let he : term R C i = ModuleCat.of R
            (Module.Dual R (ProjectiveDeterminantModules.determinantModule R (C.cochain.X i))) := by
          simp [term, hi]
        let e := eqToIso he
        have heval (D : FreeBases R C) : e.toLinearEquiv (termVector R C D i) =
            basisCoordinate R (D.basis i) := by
          simp only [termVector, dite_eq_right hi]
          exact eqToIso_apply_cast R _ _ he _
        apply e.toLinearEquiv.injective
        rw [map_smul]
        simp only [heval, ite_eq_right hi]
        exact hc

private theorem prod_coboundary (G : Type*) [CommGroup G] (s : Finset ℤ) (u : ℤ → G)
    (hz : ∀ i, i ∉ s → u i = 1 ∧ u (i + 1) = 1) :
    (∏ i ∈ s, u i * (u (i + 1))⁻¹) = 1 := by
  have hprod : (∏ i ∈ s, u (i + 1)) = ∏ i ∈ s, u i := by
    apply Finset.prod_bij_ne_one (fun i _ _ => i + 1)
    · intro i hi hn
      by_contra h
      exact hn (hz (i + 1) h).1
    · intro i hi hn j hj hm h
      exact add_right_cancel h
    · intro j hj hn
      have hmem : j - 1 ∈ s := by
        by_contra h
        have hzero := (hz (j - 1) h).2
        exact hn (by simpa using hzero)
      refine ⟨j - 1, hmem, ?_, by simp⟩
      simpa using hn
    · intro i hi hn
      rfl
  rw [Finset.prod_mul_distrib, Finset.prod_inv_distrib, hprod, mul_inv_cancel]

private theorem torsion_same_rank (R : Type) [CommRing R] [Nontrivial R]
    (C : BoundedProjectiveDeterminants.Complex R) (A B : AdaptedBases R C)
    (hr : A.kernelRank = B.kernelRank) : acyclicTorsion R C A = acyclicTorsion R C B := by
  classical
  cases B with
  | mk ac kr kb lift hl tb ht hw =>
    dsimp only at hr
    subst kr
    let F : FreeBases R C := ⟨fun i => A.kernelRank i + A.kernelRank (i + 1), tb, hw⟩
    let u : ℤ → Rˣ := fun i => ((A.kernelBasis i).isUnit_det (kb i)).unit
    have hu (i : ℤ) : (u i : R) = (A.kernelBasis i).det (kb i) :=
      ((A.kernelBasis i).isUnit_det (kb i)).unit_spec
    have hdet (i : ℤ) : (A.termBasis i).det (tb i) = ((u i * u (i + 1) : Rˣ) : R) := by
      simpa only [Units.val_mul, hu] using term_determinant_factor R C A kb lift hl tb ht i
    let v : ℤ → Rˣ := fun i => if Even i then u i else (u i)⁻¹
    let w : ℤ → Rˣ := fun i => v i * (v (i + 1))⁻¹
    have hwterm (i : ℤ) : termVector R C F i = (w i : R) • termVector R C A.asFree i := by
      obtain ⟨t, htv, hts⟩ := termVector_scale R C A.asFree F rfl i
      have htu : t = u i * u (i + 1) := by
        apply Units.ext
        have htval : (t : R) = (A.termBasis i).det (tb i) := by
          have he : (finCongr (congrFun (rfl : A.asFree.rank = F.rank) i)).symm =
              Equiv.refl (Fin (A.kernelRank i + A.kernelRank (i + 1))) := by
            apply Equiv.ext
            intro j
            apply Fin.ext
            rfl
          dsimp only [F, AdaptedBases.asFree] at htv he
          rw [he, Module.Basis.reindex_refl] at htv
          exact htv
        exact htval.trans (hdet i)
      have hparity : w i = if Even i then t else t⁻¹ := by
        rw [htu]
        by_cases hi : Even i
        · simp only [w, v, Int.even_add_one, hi, not_true_eq_false, ite_true, ite_false, inv_inv]
        · simp only [w, v, Int.even_add_one, hi, not_false_eq_true, ite_true, ite_false,
            mul_inv_rev]
          exact mul_comm _ _
      simpa only [hparity] using hts
    have hzero (i : ℤ) (hz : IsZero (C.cochain.X i)) : u i = 1 ∧ u (i + 1) = 1 := by
      let := ModuleCat.subsingleton_of_isZero hz
      have hrank : A.kernelRank i + A.kernelRank (i + 1) = 0 := by
        have h := Module.finrank_eq_card_basis (A.termBasis i)
        have hzrank : Module.finrank R (C.cochain.X i) = 0 :=
          Module.finrank_eq_zero_of_subsingleton R _
        simpa only [Fintype.card_fin, hzrank] using h.symm
      have hk : A.kernelRank i = 0 := Nat.eq_zero_of_add_eq_zero_right hrank
      have hl : A.kernelRank (i + 1) = 0 := Nat.eq_zero_of_add_eq_zero_left hrank
      constructor
      · apply Units.ext
        rw [hu]
        have : IsEmpty (Fin (A.kernelRank i)) := Fin.isEmpty_iff.mpr hk
        simp
      · apply Units.ext
        rw [hu]
        have : IsEmpty (Fin (A.kernelRank (i + 1))) := Fin.isEmpty_iff.mpr hl
        simp
    let s : Finset ℤ := (support_finite R C).toFinset
    have hz (i : ℤ) (hi : i ∉ s) : v i = 1 ∧ v (i + 1) = 1 := by
      have hzeroi : IsZero (C.cochain.X i) := by
        simpa only [s, Set.Finite.mem_toFinset, support, Set.mem_ofPred_eq, not_not] using hi
      obtain ⟨ha, hb⟩ := hzero i hzeroi
      simp [v, ha, hb]
    have hprod : ((degrees R C).map w).prod = 1 := by
      have hp := prod_coboundary Rˣ s v hz
      rw [degrees]
      exact ((Finset.sort_perm_toList s (· ≤ ·)).map w).prod_eq.trans
        ((Finset.prod_map_toList s w).trans hp)
    change tensorVector R C A.asFree (degrees R C) = tensorVector R C F (degrees R C)
    rw [tensorVector_scale R C A.asFree F w hwterm, hprod]
    simp

/-- Independence of the literal kernel-basis/lift torsion in the original degree order. -/
public theorem torsion_independent (R : Type) [CommRing R]
    (C : BoundedProjectiveDeterminants.Complex R) (A B : AdaptedBases R C) :
    acyclicTorsion R C A = acyclicTorsion R C B
    := by
  rcases subsingleton_or_nontrivial R with hR | hR
  · have : Subsingleton (determinantObject R C) := Module.subsingleton R _
    exact Subsingleton.elim _ _
  · have hr : A.kernelRank = B.kernelRank := by
      funext i
      have h := (Module.finrank_eq_card_basis (A.kernelBasis i)).symm.trans
        (Module.finrank_eq_card_basis (B.kernelBasis i))
      simpa using h
    exact torsion_same_rank R C A B hr

end WantedExt.AlgebraicGeometry.CanonicalKoszulDeterminants
