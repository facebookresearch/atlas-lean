/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.RepresentationTheory.AlgebraRepresentation.Basic

@[expose] public section

section
namespace MathlibExt.Algebra.Algebra.BurnsideMatrixWanted

/-!
# Burnside's theorem on matrix algebras

Records that an irreducible subalgebra of `M_n(k)` over an algebraically
closed field is the whole matrix algebra.
-/

/-- Irreducibility as matrices gives simplicity as a module (for `n ≠ 0`). -/
private theorem burnsideSimple {k : Type*} [Field k] {n : ℕ}
    (A : Subalgebra k (Matrix (Fin n) (Fin n) k))
    (h : ∀ W : Submodule k (Fin n → k),
      (∀ M ∈ A, ∀ v ∈ W, M.mulVec v ∈ W) → W = ⊥ ∨ W = ⊤)
    (hn : n ≠ 0) :
    IsSimpleModule ↥A (Fin n → k) := by
  have : Nontrivial (Fin n → k) :=
    ⟨⟨0, Function.update 0 ⟨0, Nat.pos_of_ne_zero hn⟩ 1, by
      intro hcon
      have h2 := congrFun hcon ⟨0, Nat.pos_of_ne_zero hn⟩
      simp at h2⟩⟩
  have : Nontrivial (Submodule ↥A (Fin n → k)) := ⟨⟨⊥, ⊤, by
    intro hcon
    obtain ⟨v, w, hvw⟩ := exists_pair_ne (Fin n → k)
    have hv : v ∈ (⊥ : Submodule ↥A (Fin n → k)) := by
      rw [hcon]
      exact Submodule.mem_top
    have hw : w ∈ (⊥ : Submodule ↥A (Fin n → k)) := by
      rw [hcon]
      exact Submodule.mem_top
    simp only [Submodule.mem_bot] at hv hw
    exact hvw (hv.trans hw.symm)⟩⟩
  rw [isSimpleModule_iff]
  refine ⟨fun U => ?_⟩
  let W : Submodule k (Fin n → k) :=
    { carrier := {v | v ∈ U}
      add_mem' := fun ha hb => U.add_mem ha hb
      zero_mem' := U.zero_mem
      smul_mem' := fun c v hv => by
        have e : c • v = (Algebra.algebraMap k ↥A c) • v := by
          have hs := IsScalarTower.smul_assoc c (1 : ↥A) v
          rw [Algebra.smul_def c (1 : ↥A), mul_one, one_smul] at hs
          exact hs.symm
        rw [e]
        exact U.smul_mem _ hv }
  have hinv : ∀ M ∈ A, ∀ v ∈ W, M.mulVec v ∈ W := by
    intro M hM v hv
    change (⟨M, hM⟩ : ↥A) • v ∈ U
    exact U.smul_mem _ hv
  rcases h W hinv with hW | hW
  · left
    apply SetLike.ext
    intro v
    rw [Submodule.mem_bot]
    constructor
    · intro hv
      have h2 : v ∈ W := hv
      rw [hW, Submodule.mem_bot] at h2
      exact h2
    · intro hv
      rw [hv]
      exact U.zero_mem
  · right
    apply SetLike.ext
    intro v
    constructor
    · intro _
      exact Submodule.mem_top
    · intro _
      have h2 : v ∈ W := by
        rw [hW]
        exact Submodule.mem_top
      exact h2

/-- The commutant of an irreducible subalgebra consists of scalars. -/
private theorem burnside_commutant {k : Type*} [Field k] [IsAlgClosed k] {n : ℕ}
    (A : Subalgebra k (Matrix (Fin n) (Fin n) k))
    (h : ∀ W : Submodule k (Fin n → k),
      (∀ M ∈ A, ∀ v ∈ W, M.mulVec v ∈ W) → W = ⊥ ∨ W = ⊤)
    (T : (Fin n → k) →ₗ[k] (Fin n → k))
    (hT : ∀ M ∈ A, ∀ v, T (M.mulVec v) = M.mulVec (T v)) :
    ∃ c : k, ∀ v, T v = c • v := by
  rcases eq_or_ne n 0 with rfl | hn
  · refine ⟨0, fun v => ?_⟩
    have hv0 : v = 0 := Subsingleton.elim v 0
    rw [hv0, map_zero, smul_zero]
  · have := burnsideSimple A h hn
    let T' : (Fin n → k) →ₗ[↥A] (Fin n → k) :=
      { toFun := T
        map_add' := T.map_add
        map_smul' := fun a v => by
          change T ((a.val).mulVec v) = (a.val).mulVec (T v)
          exact hT a.val a.property v }
    obtain ⟨c, hc⟩ := (IsSimpleModule.algebraMap_end_bijective_of_isAlgClosed k).2 T'
    refine ⟨c, fun v => ?_⟩
    have e2 : (algebraMap k (Module.End ↥A (Fin n → k)) c) v = T v := by
      rw [hc]
      rfl
    simpa [Algebra.algebraMap_eq_smul_one] using e2.symm


/-- Jacobson density (special case): an irreducible subalgebra hits arbitrary
values on linearly independent vectors. -/
private theorem burnside_dense {k : Type*} [Field k] [IsAlgClosed k] {n : ℕ}
    (A : Subalgebra k (Matrix (Fin n) (Fin n) k))
    (h : ∀ W : Submodule k (Fin n → k),
      (∀ M ∈ A, ∀ v ∈ W, M.mulVec v ∈ W) → W = ⊥ ∨ W = ⊤)
    (m : ℕ) :
    ∀ (x y : Fin m → (Fin n → k)),
      LinearIndependent k x → ∃ M ∈ A, ∀ i, M.mulVec (x i) = y i := by
  induction m with
  | zero =>
    intro x y _
    exact ⟨1, A.one_mem, fun i => (Nat.not_lt_zero _ i.isLt).elim⟩
  | succ m IH =>
    intro x y hx
    classical
    set x' : Fin m → (Fin n → k) := x ∘ Fin.castSucc with hx'def
    set xl : Fin n → k := x (Fin.last m) with hxldef
    have hx' : LinearIndependent k x' := by
      rw [hx'def]
      exact hx.comp Fin.castSucc (Fin.castSucc_injective m)
    have hit : ∀ z : Fin m → (Fin n → k), ∃ a : ↥A,
        ∀ j, (a.val).mulVec (x' j) = z j := by
      intro z
      obtain ⟨M, hM, hhit⟩ := IH x' z hx'
      exact ⟨⟨M, hM⟩, hhit⟩
    choose F hF using hit
    let f : (Fin m → (Fin n → k)) → (Fin n → k) := fun z => (F z).val.mulVec xl
    let J : Submodule k ↥A :=
      { carrier := {a | ∀ j, (a.val).mulVec (x' j) = 0}
        add_mem' := by
          intro a b ha hb
          change ∀ j, (((a + b : ↥A).val)).mulVec (x' j) = 0
          intro j
          rw [Subalgebra.coe_add, Matrix.add_mulVec, ha j, hb j, add_zero]
        zero_mem' := by
          change ∀ j, (((0 : ↥A).val)).mulVec (x' j) = 0
          intro j
          rw [Subalgebra.coe_zero, Matrix.zero_mulVec]
        smul_mem' := by
          intro c a ha
          change ∀ j, (((c • a : ↥A).val)).mulVec (x' j) = 0
          intro j
          rw [Subalgebra.coe_smul, Matrix.smul_mulVec, ha j, smul_zero] }
    let L : ↥A →ₗ[k] (Fin n → k) :=
      { toFun := fun a => (a.val).mulVec xl
        map_add' := fun a b => by
          change (((a + b : ↥A).val)).mulVec xl =
            (a.val).mulVec xl + (b.val).mulVec xl
          rw [Subalgebra.coe_add, Matrix.add_mulVec]
        map_smul' := fun c a => by
          change ((((c • a : ↥A))).val).mulVec xl = c • (a.val).mulVec xl
          rw [Subalgebra.coe_smul, Matrix.smul_mulVec] }
    let S : Submodule k (Fin n → k) := Submodule.map L J
    have hS : ∀ M ∈ A, ∀ v ∈ S, M.mulVec v ∈ S := by
      intro M hM v hv
      have hv' : v ∈ Submodule.map L J := hv
      obtain ⟨a, ha, rfl⟩ := Submodule.mem_map.mp hv'
      have hmemJ : (⟨M, hM⟩ : ↥A) * a ∈ J := by
        change ∀ j, (((⟨M, hM⟩ : ↥A) * a).val).mulVec (x' j) = 0
        intro j
        rw [Subalgebra.coe_mul, ← Matrix.mulVec_mulVec, ha j, Matrix.mulVec_zero]
      have hmap : L ((⟨M, hM⟩ : ↥A) * a) = M.mulVec (L a) := by
        change (((⟨M, hM⟩ : ↥A) * a).val).mulVec xl =
          (⟨M, hM⟩ : ↥A).val.mulVec ((a.val).mulVec xl)
        rw [Subalgebra.coe_mul, ← Matrix.mulVec_mulVec]
      have goal'' : M.mulVec (L a) ∈ Submodule.map L J :=
        Submodule.mem_map.mpr ⟨(⟨M, hM⟩ : ↥A) * a, hmemJ, hmap⟩
      have goal' : M.mulVec (L a) ∈ S := goal''
      exact goal'
    rcases h S hS with hSbot | hStop
    · -- `S = ⊥`: derive a contradiction via scalar slices.
      have vanish : ∀ N : ↥A, (∀ j, (N.val).mulVec (x' j) = 0) →
          (N.val).mulVec xl = 0 := by
        intro N hN
        have hmem : L N ∈ S := Submodule.mem_map.mpr ⟨N, hN, rfl⟩
        rw [hSbot, Submodule.mem_bot] at hmem
        change (N.val).mulVec xl = 0
        exact hmem
      have fkey : ∀ (M : ↥A) (z : Fin m → (Fin n → k)),
          (∀ j, (M.val).mulVec (x' j) = z j) → (M.val).mulVec xl = f z := by
        intro M z hMz
        have hsub : ∀ j, (((M - F z : ↥A).val)).mulVec (x' j) = 0 := by
          intro j
          rw [Subalgebra.coe_sub, Matrix.sub_mulVec, hMz j, hF z j, sub_self]
        have hv2 := vanish (M - F z) hsub
        rw [Subalgebra.coe_sub, Matrix.sub_mulVec] at hv2
        have hcon : (M.val).mulVec xl = (F z).val.mulVec xl := sub_eq_zero.mp hv2
        exact hcon
      let F' : (Fin m → (Fin n → k)) →ₗ[k] (Fin n → k) :=
        { toFun := f
          map_add' := fun z₁ z₂ => by
            have e := fkey (F z₁ + F z₂) (z₁ + z₂) (fun j => by
              simp only [Subalgebra.coe_add, Matrix.add_mulVec, hF _ j,
                Pi.add_apply])
            have e2 : ((F z₁ + F z₂ : ↥A).val).mulVec xl = f z₁ + f z₂ := by
              rw [Subalgebra.coe_add, Matrix.add_mulVec]
            exact e.symm.trans e2
          map_smul' := fun c z => by
            have e := fkey (c • (F z)) (c • z) (fun j => by
              simp only [Subalgebra.coe_smul, Matrix.smul_mulVec, hF _ j,
                Pi.smul_apply])
            have e2 : ((((c • F z : ↥A))).val).mulVec xl = c • f z := by
              rw [Subalgebra.coe_smul, Matrix.smul_mulVec]
            exact e.symm.trans e2 }
      let G : Fin m → (Fin n → k) →ₗ[k] (Fin n → k) := fun j =>
        { toFun := fun w => F' (Function.update (0 : Fin m → (Fin n → k)) j w)
          map_add' := fun a b => by
            change F' (Function.update (0 : Fin m → (Fin n → k)) j (a + b)) =
              F' (Function.update (0 : Fin m → (Fin n → k)) j a) + F'
                  (Function.update (0 : Fin m → (Fin n → k)) j b)
            have hupd : Function.update (0 : Fin m → (Fin n → k)) j (a + b) =
                Function.update (0 : Fin m → (Fin n → k)) j a + Function.update
                    (0 : Fin m → (Fin n → k)) j b := by
              funext i'
              by_cases hij : i' = j
              · simp only [hij, Function.update_self, Pi.add_apply]
              · have hne : i' ≠ j := hij
                simp only [Function.update_of_ne hne, Pi.add_apply, Pi.zero_apply,
                  add_zero]
            rw [hupd, map_add]
          map_smul' := fun c w => by
            change F' (Function.update (0 : Fin m → (Fin n → k)) j (c • w)) = c • F'
                (Function.update (0 : Fin m → (Fin n → k)) j w)
            have hupd : Function.update (0 : Fin m → (Fin n → k)) j (c • w) =
                c • Function.update (0 : Fin m → (Fin n → k)) j w := by
              funext i'
              by_cases hij : i' = j
              · simp only [hij, Function.update_self, Pi.smul_apply]
              · have hne : i' ≠ j := hij
                simp only [Function.update_of_ne hne, Pi.smul_apply, Pi.zero_apply,
                  smul_zero]
            rw [hupd, map_smul] }
      have Gcomm : ∀ (j : Fin m) (M : ↥A) (v : Fin n → k),
          G j ((M.val).mulVec v) = (M.val).mulVec (G j v) := by
        intro j M v
        have hhit : ∀ j', ((M * F (Function.update (0 : Fin m → (Fin n → k)) j v)).val).mulVec
            (x' j') =
            (fun i' => (M.val).mulVec (Function.update (0 : Fin m → (Fin n → k)) j v i')) j' := by
          intro j'
          change ((M * F (Function.update (0 : Fin m → (Fin n → k)) j v)).val).mulVec (x' j') =
            (M.val).mulVec (Function.update (0 : Fin m → (Fin n → k)) j v j')
          rw [Subalgebra.coe_mul, ← Matrix.mulVec_mulVec, hF _ j']
        have e2 : (fun i' => (M.val).mulVec (Function.update (0 : Fin m → (Fin n → k)) j v i')) =
            Function.update (0 : Fin m → (Fin n → k)) j ((M.val).mulVec v) := by
          funext i'
          by_cases hij : i' = j
          · simp only [hij, Function.update_self]
          · have hne : i' ≠ j := hij
            simp only [Function.update_of_ne hne, Pi.zero_apply,
              Matrix.mulVec_zero]
        have e := fkey (M * F (Function.update (0 : Fin m → (Fin n → k)) j v)) _ hhit
        rw [e2] at e
        rw [Subalgebra.coe_mul, ← Matrix.mulVec_mulVec] at e
        exact e.symm
      have ht_all : ∀ j, ∃ c : k, ∀ v, G j v = c • v := fun j =>
        burnside_commutant A h (G j) (fun M hM v => Gcomm j ⟨M, hM⟩ v)
      choose t ht using ht_all
      have hdecomp : x' =
          ∑ j, Function.update (0 : Fin m → (Fin n → k)) j (x' j) := by
        funext i'
        have h1 : (∑ j, Function.update (0 : Fin m → (Fin n → k)) j (x' j)) i'
            = ∑ j, Function.update (0 : Fin m → (Fin n → k)) j (x' j) i' :=
              Finset.sum_apply _ _ _
        have h2 : ∑ j, Function.update (0 : Fin m → (Fin n → k)) j (x' j) i'
            = Function.update (0 : Fin m → (Fin n → k)) i' (x' i') i' :=
              Finset.sum_eq_single i'
                (fun b _ hb => Function.update_of_ne hb.symm _ _)
                (fun hcon => absurd (Finset.mem_univ i') hcon)
        have h3 : Function.update (0 : Fin m → (Fin n → k)) i' (x' i') i'
            = x' i' := Function.update_self _ _ _
        rw [h1, h2, h3]
      have e1 : F' x' = ∑ j, t j • x' j := by
        conv_lhs => rw [hdecomp]
        rw [map_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        exact ht j (x' j)
      have e0 : f x' = xl := by
        have e := fkey 1 x' (fun j => by
          simp only [Subalgebra.coe_one, Matrix.one_mulVec])
        simpa only [Subalgebra.coe_one, Matrix.one_mulVec] using e.symm
      have hxl : xl = ∑ j, t j • x' j := by
        have hF'x' : F' x' = xl := e0
        rw [← e1]
        exact hF'x'.symm
      let l' : Fin (m + 1) →₀ k :=
        Finsupp.single (Fin.last m) 1 - ∑ j, Finsupp.single (Fin.castSucc j) (t j)
      have htotal : Finsupp.linearCombination k x l' = 0 := by
        change Finsupp.linearCombination k x
            (Finsupp.single (Fin.last m) 1 -
              ∑ j, Finsupp.single (Fin.castSucc j) (t j)) = 0
        rw [map_sub, Finsupp.linearCombination_single, map_sum]
        simp only [Finsupp.linearCombination_single]
        rw [one_smul, sub_eq_zero]
        exact hxl
      have hval : l' (Fin.last m) = 1 := by
        change ((Finsupp.single (Fin.last m) 1 -
            ∑ j, Finsupp.single (Fin.castSucc j) (t j) : Fin (m + 1) →₀ k))
            (Fin.last m) = 1
        rw [Finsupp.sub_apply, Finsupp.single_eq_same]
        have hsum : (∑ j, Finsupp.single (Fin.castSucc j) (t j)) (Fin.last m)
            = 0 := by
          rw [Finsupp.finsetSum_apply]
          exact Finset.sum_eq_zero
            (fun j _ => Finsupp.single_eq_of_ne (Fin.castSucc_ne_last j).symm)
        rw [hsum, sub_zero]
      have hne : l' ≠ 0 := by
        intro hcon
        rw [hcon] at hval
        simp at hval
      have hcontra := linearIndependent_iff.mp hx l' htotal
      exact (hne hcontra).elim
    · -- `S = ⊤`: extend a partial hitter to all `m + 1` points.
      set c₀ : ↥A := F (fun j => y (Fin.castSucc j)) with hc₀def
      have hhit0 : ∀ j, (c₀.val).mulVec (x' j) = y (Fin.castSucc j) := by
        intro j
        rw [hc₀def]
        exact hF _ j
      have hr : y (Fin.last m) - (c₀.val).mulVec xl ∈ S := by
        rw [hStop]
        exact Submodule.mem_top
      have hr' : y (Fin.last m) - (c₀.val).mulVec xl ∈ Submodule.map L J := hr
      obtain ⟨d, hdJ, hdL⟩ := Submodule.mem_map.mp hr'
      have hdJ' : ∀ j, (d.val).mulVec (x' j) = 0 := hdJ
      have hdL' : (d.val).mulVec xl
          = y (Fin.last m) - (c₀.val).mulVec xl := hdL
      refine ⟨((c₀ + d : ↥A).val), ((c₀ + d : ↥A).property), ?_⟩
      intro i
      refine Fin.lastCases
        (motive := fun i => ((c₀ + d : ↥A).val).mulVec (x i) = y i) ?_ ?_ i
      · change ((c₀ + d : ↥A).val).mulVec xl = y (Fin.last m)
        rw [Subalgebra.coe_add, Matrix.add_mulVec, hdL', add_sub_cancel]
      · intro j
        change ((c₀ + d : ↥A).val).mulVec (x' j) = y (Fin.castSucc j)
        rw [Subalgebra.coe_add, Matrix.add_mulVec, hhit0 j, hdJ' j, add_zero]

set_option linter.dupNamespace false in
/--
**Burnside's theorem on matrix algebras.** Let $k$ be an algebraically closed field, $n$ a natural
number, and $A$ a $k$-subalgebra of the algebra $M_n(k)$ of $n \times n$ matrices over $k$.
Suppose that the only subspaces $W$ of $k^n$ with $Mv \in W$ for all $M \in A$ and all $v \in W$
are $0$ and $k^n$. Then $A = M_n(k)$.

Proves `Wanted` entry `burnside_matrix`.

Source: W. Burnside, On the condition of reducibility of any group of linear substitutions, Proc.
London Math. Soc. 3 (1905), 430–434, DOI 10.1112/plms/s2-3.1.430; textbook in Lam, First Course in
Noncommutative Rings, Thm 1.2. Burnside's theorem on matrix algebras / Burnside density.
-/
theorem burnside_matrix
    {k : Type*} [Field k] [IsAlgClosed k]
    {n : ℕ}
    (A : Subalgebra k (Matrix (Fin n) (Fin n) k))
    (h : ∀ W : Submodule k (Fin n → k),
      (∀ M ∈ A, ∀ v ∈ W, M.mulVec v ∈ W) → W = ⊥ ∨ W = ⊤) :
    A = ⊤ := by
  suffices hmem : ∀ M : Matrix (Fin n) (Fin n) k, M ∈ A from
    eq_top_iff.mpr (fun M _ => hmem M)
  intro M
  let b := Pi.basisFun k (Fin n)
  obtain ⟨M', hM', hhit⟩ := burnside_dense A h n (fun i => b i) (fun i => M.mulVec (b i))
    b.linearIndependent
  have heq : M' = M := by
    have hlin : Matrix.toLin' M' = Matrix.toLin' M := by
      apply b.ext
      intro i
      rw [Matrix.toLin'_apply, Matrix.toLin'_apply]
      exact hhit i
    exact Matrix.toLin'.injective hlin
  rw [← heq]
  exact hM'

end MathlibExt.Algebra.Algebra.BurnsideMatrixWanted
