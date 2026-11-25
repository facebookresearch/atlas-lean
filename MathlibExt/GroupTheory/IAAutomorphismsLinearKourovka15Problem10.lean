/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.GroupTheory.Abelianization.Defs
public import Mathlib.GroupTheory.FreeGroup.Basic
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.GroupTheory.DivisibleHull
import Mathlib.GroupTheory.FreeAbelianGroup
import Mathlib.GroupTheory.FreeGroup.Center
import Mathlib.GroupTheory.FreeGroup.CyclicallyReduced
import Mathlib.GroupTheory.Perm.Closure
import Mathlib.GroupTheory.Perm.Fin
import Mathlib.GroupTheory.Solvable
import Mathlib.GroupTheory.Subgroup.Centralizer
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Eigenspace.Charpoly
import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
import Mathlib.LinearAlgebra.Eigenspace.Zero
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Group
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import MathlibExt.Algebra.Algebra.BurnsideMatrix

/-!
# Linearity of the IA-automorphism group of a free group (Kourovka Notebook Problem 15.10)

The theorem `iaAutLinear_refuted` rules out a faithful finite-dimensional representation of
the IA-automorphism group of a free group of rank at least three over any field.

Kourovka Notebook, Archive of Solved Problems, Problem 15.10 (Yu. I. Merzlyakov; V. G. Bardakov): is
the group of automorphisms of the free group `Fₙ` acting trivially on `Fₙ/[Fₙ, Fₙ]` linear for `n ≥
3`?

Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 15.10 (Yu. I.
Merzlyakov; V. G. Bardakov). UnsolvedMath record UM-00701098 (`KOU-15.10`), dataset
ulamai/UnsolvedMath v1.8.0.

Linear means a faithful representation in `GLₘ(K)` for some field `K` and some `m`; fields are taken
in `Type`, which suffices because `IA(Fₙ)` is finitely generated, so the entries of a faithful
representation generate a countable field. The target is stated for some `n ≥ 3`, so its refutation
covers every `n ≥ 3` (for `n = 2`, `IA(F₂) = Inn(F₂) ≅ F₂` is linear).
-/

@[expose] public section

namespace MathlibExt.GroupTheory.IAAutomorphismsLinearKourovka15Problem10Wanted

set_option linter.deprecated false in
/-- **IA-automorphisms of a free group.** For a natural number $n$, let $F_n$ be the free group on
$n$ generators. $\mathrm{IA}(F_n)$ is the subgroup of the automorphism group of $F_n$ consisting of
the automorphisms $\varphi$ that act trivially on the abelianization $F_n/[F_n, F_n]$, that is,
such that $\varphi(x)$ and $x$ have the same image in $F_n/[F_n, F_n]$ for every $x \in F_n$. -/
def iaAut (n : ℕ) : Subgroup (MulAut (FreeGroup (Fin n))) where
  carrier := {φ | ∀ x, Abelianization.of (φ x) = Abelianization.of x}
  one_mem' _ := rfl
  mul_mem' {φ ψ} hφ hψ x := (hφ (ψ x)).trans (hψ x)
  inv_mem' {φ} hφ x := by
    have h := hφ (φ⁻¹ x)
    simp only [MulAut.apply_inv_self] at h
    exact h.symm

/-- **Kourovka Problem 15.10 (statement): linearity of IA-automorphism groups of free groups.**
The statement that for some $n \ge 3$ the group $\mathrm{IA}(F_n)$ of automorphisms of the free
group $F_n$ on $n$ generators that act trivially on its abelianization $F_n/[F_n, F_n]$ is linear,
that is, there are a field $K$, a natural number $m$ and an injective group homomorphism
$\mathrm{IA}(F_n) \to \mathrm{GL}_m(K)$. -/
def iaAutLinear : Prop :=
  ∃ n : ℕ, 3 ≤ n ∧ ∃ (K : Type) (_ : Field K) (m : ℕ)
    (ρ : iaAut n →* Matrix.GeneralLinearGroup (Fin m) K), Function.Injective ρ

/- Shift one generator by a word in the derived group on two other generators. -/
section Automorphisms

private abbrev SourceGroup := commutator (FreeGroup (Fin 2))

private def oldIndex {n : ℕ} (hn : 3 ≤ n) (i : Fin 2) : Fin n :=
  ⟨i, by omega⟩

private def newIndex {n : ℕ} (hn : 3 ≤ n) : Fin n :=
  ⟨2, by omega⟩

private theorem oldIndex_ne {n : ℕ} (hn : 3 ≤ n) (i : Fin 2) :
    oldIndex hn i ≠ newIndex hn := by
  intro h
  have := congrArg Fin.val h
  change i.val = 2 at this
  omega

private abbrev inclusion {n : ℕ} (hn : 3 ≤ n) :
    FreeGroup (Fin 2) →* FreeGroup (Fin n) :=
  FreeGroup.map (oldIndex hn)

private def shiftHom {n : ℕ} (hn : 3 ≤ n) (w : FreeGroup (Fin n)) :
    FreeGroup (Fin n) →* FreeGroup (Fin n) :=
  FreeGroup.lift fun i => if i = newIndex hn then FreeGroup.of i * w else FreeGroup.of i

private theorem shiftHom_of {n : ℕ} (hn : 3 ≤ n) (w : FreeGroup (Fin n)) (i : Fin n) :
    shiftHom hn w (FreeGroup.of i) =
      if i = newIndex hn then FreeGroup.of i * w else FreeGroup.of i := by
  simp [shiftHom]

private theorem shiftHom_fixes {n : ℕ} (hn : 3 ≤ n) (w : FreeGroup (Fin n))
    (v : FreeGroup (Fin 2)) : shiftHom hn w (inclusion hn v) = inclusion hn v := by
  have h : (shiftHom hn w).comp (inclusion hn) = inclusion hn := by
    apply FreeGroup.ext_hom
    intro i
    simp [shiftHom_of, oldIndex_ne]
  exact DFunLike.congr_fun h v

private theorem shiftHom_comp {n : ℕ} (hn : 3 ≤ n) (v w : FreeGroup (Fin 2)) :
    (shiftHom hn (inclusion hn v)).comp (shiftHom hn (inclusion hn w)) =
      shiftHom hn (inclusion hn (v * w)) := by
  apply FreeGroup.ext_hom
  intro i
  by_cases hi : i = newIndex hn <;>
    simp [shiftHom_of, hi, shiftHom_fixes, mul_assoc]

private theorem shiftHom_one {n : ℕ} (hn : 3 ≤ n) :
    shiftHom hn 1 = MonoidHom.id (FreeGroup (Fin n)) := by
  apply FreeGroup.ext_hom
  intro i
  by_cases hi : i = newIndex hn <;> simp [shiftHom_of, hi]

private def shiftAut {n : ℕ} (hn : 3 ≤ n) (v : FreeGroup (Fin 2)) :
    MulAut (FreeGroup (Fin n)) :=
  { shiftHom hn (inclusion hn v) with
    invFun := shiftHom hn (inclusion hn v⁻¹)
    left_inv := fun x => by
      change shiftHom hn (inclusion hn v⁻¹) (shiftHom hn (inclusion hn v) x) = x
      have h := DFunLike.congr_fun (shiftHom_comp hn v⁻¹ v) x
      simpa only [MonoidHom.comp_apply, inv_mul_cancel, map_one, shiftHom_one,
        MonoidHom.id_apply] using h
    right_inv := fun x => by
      change shiftHom hn (inclusion hn v) (shiftHom hn (inclusion hn v⁻¹) x) = x
      have h := DFunLike.congr_fun (shiftHom_comp hn v v⁻¹) x
      simpa only [MonoidHom.comp_apply, mul_inv_cancel, map_one, shiftHom_one,
        MonoidHom.id_apply] using h }

private def inn {n : ℕ} : FreeGroup (Fin n) →* iaAut n where
  toFun g := ⟨MulAut.conj g, fun x => by
    simp [MulAut.conj_apply]⟩
  map_one' := Subtype.ext ((MulAut.conj (G := FreeGroup (Fin n))).map_one)
  map_mul' g h := Subtype.ext ((MulAut.conj (G := FreeGroup (Fin n))).map_mul g h)

private def shift {n : ℕ} (hn : 3 ≤ n) : SourceGroup →* iaAut n where
  toFun v := ⟨shiftAut hn v, by
    change ∀ x, Group.Abelianization.of (shiftHom hn (inclusion hn v) x) = Group.Abelianization.of x
    have hv : Group.Abelianization.of (v : FreeGroup (Fin 2)) = 1 :=
      Group.Abelianization.commutator_le_ker _ v.property
    have hv' : Group.Abelianization.of (inclusion hn v) = 1 := by
      rw [← Group.Abelianization.map_of, hv, map_one]
    have h : Group.Abelianization.of.comp (shiftHom hn (inclusion hn v)) =
        Group.Abelianization.of := by
      apply FreeGroup.ext_hom
      intro i
      by_cases hi : i = newIndex hn <;> simp [shiftHom_of, hi, hv']
    exact DFunLike.congr_fun h⟩
  map_one' := Subtype.ext <| DFunLike.ext _ _ fun x => by
    change shiftHom hn (inclusion hn 1) x = x
    simp [shiftHom_one]
  map_mul' v w := Subtype.ext <| DFunLike.ext _ _ fun x =>
    (DFunLike.congr_fun (shiftHom_comp hn v w) x).symm

private abbrev inner {n : ℕ} (hn : 3 ≤ n) : SourceGroup →* iaAut n :=
  inn.comp ((inclusion hn).comp (commutator (FreeGroup (Fin 2))).subtype)

private theorem inner_injective {n : ℕ} (hn : 3 ≤ n) : Function.Injective (inner hn) := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  rw [Subgroup.eq_bot_iff_forall]
  intro g hg
  let : Nontrivial (Fin n) := ⟨⟨oldIndex hn 0, newIndex hn, oldIndex_ne hn 0⟩⟩
  have hcenter : inclusion hn g ∈ Subgroup.center (FreeGroup (Fin n)) := by
    apply Subgroup.mem_center_iff.mpr
    intro x
    have h := DFunLike.congr_fun (congrArg Subtype.val (MonoidHom.mem_ker.mp hg)) x
    change inclusion hn g * x * (inclusion hn g)⁻¹ = x at h
    calc
      x * inclusion hn g =
          (inclusion hn g * x * (inclusion hn g)⁻¹) * inclusion hn g := by rw [h]
      _ = inclusion hn g * x := by group
  rw [FreeGroup.center_eq_bot_of_nontrivial, Subgroup.mem_bot] at hcenter
  apply Subtype.ext
  have hi : Function.Injective (oldIndex hn) := fun _ _ h =>
    Fin.ext (congrArg (fun i : Fin n => i.val) h)
  exact FreeGroup.map_injective hi (hcenter.trans (map_one (inclusion hn)).symm)

private theorem inner_shift_commute {n : ℕ} (hn : 3 ≤ n) (g h : SourceGroup) :
    Commute (inner hn g) (shift hn h) := by
  apply Subtype.ext
  apply DFunLike.ext
  intro x
  change inclusion hn g * shiftHom hn (inclusion hn h) x * (inclusion hn g)⁻¹ =
    shiftHom hn (inclusion hn h) (inclusion hn g * x * (inclusion hn g)⁻¹)
  simp only [map_mul, map_inv, shiftHom_fixes]

private theorem inner_mul_shift {n : ℕ} (hn : 3 ≤ n) (g : SourceGroup) :
    inn (FreeGroup.of (newIndex hn)) * (inner hn g * shift hn g) =
      shift hn g * inn (FreeGroup.of (newIndex hn)) := by
  apply Subtype.ext
  apply DFunLike.ext
  intro x
  set z := FreeGroup.of (newIndex hn)
  set v := inclusion hn g
  change z * (v * shiftHom hn v x * v⁻¹) * z⁻¹ = shiftHom hn v (z * x * z⁻¹)
  have hz : shiftHom hn v z = z * v := by simp [z, shiftHom_of]
  simp only [map_mul, map_inv, hz]
  group

end Automorphisms

/- A permutation that preserves each fiber product gives a uniform torsion bound. -/
section EigenvalueOrders

open scoped BigOperators

private theorem perm_sub_eq_zero {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : ι → ι) (σ : Equiv.Perm ι) (b : ι → ℚ)
    (h : ∀ j, ∑ i ∈ Finset.univ.filter (fun i => p i = j), (b (p (σ i)) - b (p i)) = 0)
    (i : ι) : b (p (σ i)) - b (p i) = 0 := by
  have horth : ∑ i, b (p i) * (b (p (σ i)) - b (p i)) = 0 := by
    rw [← Finset.sum_fiberwise Finset.univ p]
    apply Finset.sum_eq_zero
    intro j _
    trans ∑ i ∈ Finset.univ.filter (fun i => p i = j), b j * (b (p (σ i)) - b (p i))
    · apply Finset.sum_congr rfl
      intro k hk
      rw [(Finset.mem_filter.mp hk).2]
    · rw [← Finset.mul_sum, h j, mul_zero]
  have hperm : ∑ i, b (p (σ i)) ^ 2 = ∑ i, b (p i) ^ 2 :=
    Equiv.sum_comp σ (fun i => b (p i) ^ 2)
  have hsq : ∑ i, (b (p (σ i)) - b (p i)) ^ 2 = 0 := by
    calc
      _ = ∑ i, (b (p (σ i)) ^ 2 - b (p i) ^ 2 -
          2 * (b (p i) * (b (p (σ i)) - b (p i)))) := by
        apply Finset.sum_congr rfl
        intro j _
        ring
      _ = 0 := by rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
        hperm, sub_self, horth, mul_zero, sub_zero]
  exact sq_eq_zero_iff.mp <|
    (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => sq_nonneg _)).mp hsq i (Finset.mem_univ _)

private theorem exists_spectral_exponent (m : ℕ) :
    ∃ N : ℕ, 0 < N ∧
      ∀ {M : Type} [AddCommGroup M] (p : Fin m → Fin m) (σ : Equiv.Perm (Fin m))
        (b : Fin m → M),
        (∀ j, ∑ i ∈ Finset.univ.filter (fun i => p i = j), (b (p (σ i)) - b (p i)) = 0) →
        ∀ i, N • (b (p (σ i)) - b (p i)) = 0 := by
  classical
  let F := FreeAbelianGroup (Fin m)
  let v := @FreeAbelianGroup.of (Fin m)
  let r (p : Fin m → Fin m) (σ : Equiv.Perm (Fin m)) (j : Fin m) : F :=
    ∑ i ∈ Finset.univ.filter (fun i => p i = j), (v (p (σ i)) - v (p i))
  let H p σ := AddSubgroup.closure (Set.range (r p σ))
  let Q p σ := F ⧸ H p σ
  let e p σ : F →+ Q p σ := QuotientAddGroup.mk' (H p σ)
  let d p σ := DivisibleHull.coeAddMonoidHom (Q p σ)
  have htorsion (p : Fin m → Fin m) (σ : Equiv.Perm (Fin m)) (i : Fin m) :
      ∃ n : ℕ, 0 < n ∧ n • e p σ (v (p (σ i)) - v (p i)) = 0 := by
    have hr j : e p σ (r p σ j) = 0 :=
      AddMonoidHom.mem_ker.mp (by
        rw [QuotientAddGroup.ker_mk']
        exact AddSubgroup.subset_closure (Set.mem_range_self j))
    let B := Module.Basis.ofVectorSpace ℚ (DivisibleHull (Q p σ))
    have hz : d p σ (e p σ (v (p (σ i)) - v (p i))) = 0 := by
      apply B.forall_coord_eq_zero_iff.mp
      intro k
      let l := (B.coord k).toAddMonoidHom.comp ((d p σ).comp (e p σ))
      have hk j : l (r p σ j) = 0 := by simp [l, hr]
      change l (v (p (σ i)) - v (p i)) = 0
      rw [map_sub]
      apply perm_sub_eq_zero p σ (l ∘ v) _ i
      intro j
      simpa only [r, map_sum, map_sub, Function.comp_apply] using hk j
    change DivisibleHull.mk (e p σ (v (p (σ i)) - v (p i))) 1 = 0 at hz
    rw [← DivisibleHull.mk_zero 1, DivisibleHull.mk_eq_mk] at hz
    obtain ⟨u, hu⟩ := hz
    exact ⟨u.val, u.2, by simpa using hu⟩
  let T := (Fin m → Fin m) × Equiv.Perm (Fin m) × Fin m
  choose n hn hn0 using fun (t : T) => htorsion t.1 t.2.1 t.2.2
  let N := ∏ t : T, n t
  refine ⟨N, Finset.prod_pos (fun t _ => hn t), ?_⟩
  intro M _ p σ b hb i
  let f : F →+ M := FreeAbelianGroup.lift b
  have hf (j : Fin m) : f (v j) = b j := FreeAbelianGroup.lift_apply_of b j
  have hker : H p σ ≤ f.ker := by
    apply (AddSubgroup.closure_le _).mpr
    rintro _ ⟨j, rfl⟩
    apply AddMonoidHom.mem_ker.mpr
    simpa only [r, map_sum, map_sub, hf] using hb j
  let f' : Q p σ →+ M := QuotientAddGroup.lift (H p σ) f hker
  let t : T := (p, σ, i)
  obtain ⟨a, ha⟩ := Finset.dvd_prod_of_mem n (Finset.mem_univ t)
  change N = n t * a at ha
  have hzero := congrArg f' (hn0 t)
  rw [map_nsmul, map_zero] at hzero
  change n t • f (v (p (σ i)) - v (p i)) = 0 at hzero
  calc
    N • (b (p (σ i)) - b (p i)) =
        a • (n t • (b (p (σ i)) - b (p i))) := by
      rw [ha, Nat.mul_comm (n t) a]
      exact (smul_smul a (n t) _).symm
    _ = 0 := by
      simpa only [map_sub, hf, smul_zero] using congrArg (fun x : M => a • x) hzero

end EigenvalueOrders

/- Decompose first by the generalized eigenspaces of the shift, then by those of the
commuting inner automorphism. The determinant of the inner action on each shift
eigenspace is a character, so it is trivial on the commutator subgroup. -/
section GeneralizedEigenspaces

open Function Module Polynomial Set
open scoped BigOperators

variable {K : Type} [Field K]
variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V]

private theorem charpoly_internal {ι : Type} [DecidableEq ι] [Fintype ι] (p : ι → Submodule K V)
    (hp : DirectSum.IsInternal p) (f : End K V)
    (h : ∀ i, MapsTo f (p i) (p i)) :
    f.charpoly = ∏ i, (f.restrict (h i)).charpoly := by
  classical
  let b i := Module.finBasis K (p i)
  let B := hp.collectedBasis b
  let ι' := Σ i, Fin (finrank K (p i))
  let q : ι' → Fin (Fintype.card ι) := (Fintype.equivFin ι) ∘ Sigma.fst
  let M := LinearMap.toMatrix B B f
  have hentry (i j : ι') (hij : i.1 ≠ j.1) : M i j = 0 := by
    cases i with | mk i a =>
    cases j with | mk j c =>
    have hx := h j (hp.collectedBasis_mem b ⟨j, c⟩)
    dsimp [M, B]
    rw [LinearMap.toMatrix_apply]
    exact hp.collectedBasis_repr_of_mem_ne b hij.symm hx
  have hdiag (i : ι) (a c : Fin (finrank K (p i))) :
      M ⟨i, a⟩ ⟨i, c⟩ = LinearMap.toMatrix (b i) (b i) (f.restrict (h i)) a c := by
    simp only [M, LinearMap.toMatrix_apply]
    change B.repr (f (B ⟨i, c⟩)) ⟨i, a⟩ = _
    rw [hp.collectedBasis_repr_of_mem b (h i (hp.collectedBasis_mem b ⟨i, c⟩))]
    apply congrArg (fun x => (b i).repr x a)
    apply Subtype.ext
    change f (B ⟨i, c⟩) = f (b i c)
    simp [B]
  have htri : M.BlockTriangular q := fun i j hij =>
    hentry i j (fun he => (ne_of_gt hij) (congrArg (Fintype.equivFin ι) he))
  have hm : f.charpoly = M.charpoly := (LinearMap.charpoly_toMatrix f B).symm
  have hprod : (∏ j ∈ Finset.image q Finset.univ, (M.toSquareBlock q j).charpoly) =
      ∏ j, (M.toSquareBlock q j).charpoly := by
    apply Finset.prod_subset (Finset.subset_univ _)
    intro j _ hj
    have : IsEmpty {i : ι' // q i = j} := ⟨fun i => hj
      (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, i.property⟩)⟩
    exact Matrix.charpoly_isEmpty
  calc
    f.charpoly = M.charpoly := hm
    _ = _ := htri.charpoly
    _ = _ := hprod
    _ = _ := ?_
  rw [← (Fintype.equivFin ι).prod_comp (fun j => (M.toSquareBlock q j).charpoly)]
  apply Finset.prod_congr rfl
  intro i _
  let E : {t : ι' // q t = Fintype.equivFin ι i} ≃ Fin (finrank K (p i)) :=
    { toFun := fun t =>
        Fin.cast (congrArg (fun j => finrank K (p j)) ((Fintype.equivFin ι).injective t.2)) t.1.2
      invFun := fun a => ⟨⟨i, a⟩, rfl⟩
      left_inv := by
        rintro ⟨⟨j, a⟩, hj⟩
        obtain rfl : j = i := (Fintype.equivFin ι).injective hj
        rfl
      right_inv := fun _ => rfl }
  rw [← LinearMap.charpoly_toMatrix (f.restrict (h i)) (b i)]
  have he : M.toSquareBlock q (Fintype.equivFin ι i) =
      Matrix.reindex E.symm E.symm (LinearMap.toMatrix (b i) (b i) (f.restrict (h i))) := by
    ext x y : 1
    obtain ⟨a, rfl⟩ := E.symm.surjective x
    obtain ⟨c, rfl⟩ := E.symm.surjective y
    simpa [Matrix.toSquareBlock_def, E] using hdiag i a c
  rw [he, Matrix.charpoly_reindex]

private theorem isInternal_maxGenEigenspaces [IsAlgClosed K] [DecidableEq K] (f : End K V) :
    DirectSum.IsInternal (fun e : {a : K // f.HasEigenvalue a} => f.maxGenEigenspace e.1) := by
  apply DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
  · exact (f.independent_genEigenspace ⊤).comp Subtype.val_injective
  · apply top_unique
    rw [← f.iSup_maxGenEigenspace_eq_top]
    refine iSup_le fun a => ?_
    by_cases ha : f.HasEigenvalue a
    · exact le_iSup (fun e : {a : K // f.HasEigenvalue a} => f.maxGenEigenspace e.1) ⟨a, ha⟩
    · have hz : f.maxGenEigenspace a = ⊥ := by
        rw [f.maxGenEigenspace_eq_genEigenspace_finrank]
        exact not_ne_iff.mp fun h => ha (Module.End.hasEigenvalue_of_hasGenEigenvalue h)
      simp [hz]

private theorem charpoly_shifted {f : End K V} (a : K)
    (h : IsNilpotent (f - a • 1)) :
    f.charpoly = (X - C a) ^ finrank K V := by
  have he := h.charpoly_eq_X_pow_finrank
  rw [LinearMap.charpoly_sub_smul] at he
  have h' := congrArg (fun p : K[X] => p.comp (X - C a)) he
  simpa [Polynomial.comp_assoc] using h'

private theorem restrict_nilpotent_of_le_maxGenEigenspace (f : End K V) (a : K)
    (p : Submodule K V) (hp : p ≤ f.maxGenEigenspace a) (h : MapsTo f p p) :
    IsNilpotent (f.restrict h - a • 1) := by
  have hmap : MapsTo (f - a • (1 : End K V)) p p := fun x hx => by
    change f x - a • x ∈ p
    exact p.sub_mem (h hx) (p.smul_mem a hx)
  have hn := f.isNilpotent_restrict_genEigenspace_top a
  have ho : IsNilpotent ((f - a • (1 : End K V)).restrict hmap) :=
    Module.End.isNilpotent_restrict_of_le hp hn
  have he : (f - a • (1 : End K V)).restrict hmap = f.restrict h - a • 1 := by
    apply LinearMap.ext
    intro v
    apply Subtype.ext
    rfl
  exact he ▸ ho

omit [FiniteDimensional K V] in
private theorem shifted_mul_nilpotent {A B : End K V} (h : Commute A B) (a b : K)
    (ha : IsNilpotent (A - a • 1)) (hb : IsNilpotent (B - b • 1)) :
    IsNilpotent (A * B - (a * b) • 1) := by
  let X := A - a • (1 : End K V)
  let Y := B - b • (1 : End K V)
  have hX : Commute X B := h.sub_left ((Commute.one_left B).smul_left a)
  have hY : Commute X Y := hX.sub_right ((Commute.one_right X).smul_right b)
  have hBY : Commute B Y := (Commute.refl B).sub_right ((Commute.one_right B).smul_right b)
  have he : A * B - (a * b) • 1 = X * B + a • Y := by
    simp [X, Y, sub_mul, smul_sub, smul_smul]
  rw [he]
  exact ((hY.mul_left hBY).smul_right a).isNilpotent_add
    (hX.isNilpotent_mul_right ha) (hb.smul a)

private def restrictRepresentation {G : Type} [Group G]
    (A : G →* End K V) (p : Submodule K V) (h : ∀ x, MapsTo (A x) p p) :
    G →* End K p where
  toFun x := (A x).restrict (h x)
  map_one' := by ext v; simp [LinearMap.restrict_apply]
  map_mul' x y := by
    apply LinearMap.ext
    intro v
    apply Subtype.ext
    exact DFunLike.congr_fun (map_mul A x y) v.1

omit [FiniteDimensional K V] in
private theorem injective_representation_apply {G : Type} [Group G]
    (A : G →* End K V) (g : G) : Injective (A g) :=
  ((Module.End.isUnit_iff (A g)).mp ((Group.isUnit g).map A)).injective

omit [FiniteDimensional K V] in
private theorem eigenvalue_ne_zero {f : End K V} (hf : Injective f)
    {a : K} (ha : f.HasEigenvalue a) : a ≠ 0 := by
  rintro rfl
  obtain ⟨v, hv⟩ := ha.exists_hasEigenvector
  exact hv.2 (hf (by simpa using hv.apply_eq_smul))

private theorem roots_prod_linear {ι : Type} [Fintype ι] (f : ι → K) :
    (∏ i, (X - C (f i))).roots = Finset.univ.val.map f := by
  simpa only [Finset.prod, Multiset.map_map, Function.comp_def] using
    roots_multiset_prod_X_sub_C (Finset.univ.val.map f)

set_option maxHeartbeats 800000 in
-- Elaborating the block decompositions requires two levels of dependent bases.
private theorem exists_joint_spectra [IsAlgClosed K] [DecidableEq K] {G : Type} [Group G]
    (A : G →* End K V) (B : End K V) (hB : Injective B)
    (hcomm : ∀ x, Commute B (A x)) {g : G} (hg : g ∈ commutator G) :
    ∃ a b : Fin (finrank K V) → K,
      (∀ i, a i ≠ 0 ∧ b i ≠ 0) ∧
      (A g).charpoly = ∏ i, (X - C (a i)) ∧
      B.charpoly = ∏ i, (X - C (b i)) ∧
      (A g * B).charpoly = ∏ i, (X - C (a i * b i)) ∧
      ∀ t : K, ∏ i ∈ Finset.univ.filter (fun i => b i = t), a i = 1 := by
  classical
  let E := {b : K // B.HasEigenvalue b}
  let P (e : E) := B.maxGenEigenspace e.1
  let AP (e : E) : G →* End K (P e) :=
    restrictRepresentation A (P e)
      (fun x => Module.End.mapsTo_maxGenEigenspace_of_comm (hcomm x) e.1)
  let BP (e : E) : End K (P e) :=
    B.restrict (Module.End.mapsTo_maxGenEigenspace_of_comm (Commute.refl B) e.1)
  let F (e : E) := {a : K // (AP e g).HasEigenvalue a}
  let Q (e : E) (f : F e) := (AP e g).maxGenEigenspace f.1
  let I (e : E) := Σ f : F e, Fin (finrank K (Q e f))
  let J := Σ e : E, I e
  let aa (i : J) : K := i.2.1.1
  let bb (i : J) : K := i.1.1
  let : Fintype E := B.finite_hasEigenvalue.fintype
  let (e : E) : Fintype (F e) := (AP e g).finite_hasEigenvalue.fintype
  have houter : DirectSum.IsInternal P := isInternal_maxGenEigenspaces B
  have hinner (e : E) : DirectSum.IsInternal (Q e) := isInternal_maxGenEigenspaces (AP e g)
  let basisP (e : E) : Basis (I e) K (P e) :=
    (hinner e).collectedBasis (fun f => finBasis K (Q e f))
  let basisV : Basis J K V := houter.collectedBasis basisP
  let equiv : Fin (finrank K V) ≃ J :=
    (Fintype.equivFinOfCardEq (finrank_eq_card_basis basisV).symm).symm
  have hcommP (e : E) : Commute (AP e g) (BP e) := by
    apply LinearMap.ext
    intro v
    apply Subtype.ext
    exact DFunLike.congr_fun (hcomm g).symm.eq v.1
  have hnB (e : E) : IsNilpotent (BP e - e.1 • 1) :=
    restrict_nilpotent_of_le_maxGenEigenspace B e.1 (P e) le_rfl _
  have hstableA (e : E) (f : F e) : MapsTo (AP e g) (Q e f) (Q e f) :=
    Module.End.mapsTo_maxGenEigenspace_of_comm (Commute.refl (AP e g)) f.1
  have hstableB (e : E) (f : F e) : MapsTo (BP e) (Q e f) (Q e f) :=
    Module.End.mapsTo_maxGenEigenspace_of_comm (hcommP e) f.1
  let AQ (e : E) (f : F e) := (AP e g).restrict (hstableA e f)
  let BQ (e : E) (f : F e) := (BP e).restrict (hstableB e f)
  have hAQ (e : E) (f : F e) : IsNilpotent (AQ e f - f.1 • 1) :=
    restrict_nilpotent_of_le_maxGenEigenspace (AP e g) f.1 (Q e f) le_rfl _
  have hBQ (e : E) (f : F e) : IsNilpotent (BQ e f - e.1 • 1) := by
    have hs : MapsTo (BP e - e.1 • (1 : End K (P e))) (Q e f) (Q e f) := fun v hv => by
      change BP e v - e.1 • v ∈ Q e f
      exact (Q e f).sub_mem (hstableB e f hv) ((Q e f).smul_mem _ hv)
    have he : (BP e - e.1 • (1 : End K (P e))).restrict hs = BQ e f - e.1 • 1 := by
      apply LinearMap.ext
      intro v
      apply Subtype.ext
      rfl
    exact he ▸ Module.End.isNilpotent.restrict hs (hnB e)
  have cAQ (e : E) :
      (AP e g).charpoly = ∏ i : I e, (X - C (aa ⟨e, i⟩)) := by
    rw [charpoly_internal _ (hinner e) _ (hstableA e), Fintype.prod_sigma]
    apply Finset.prod_congr rfl
    intro f _
    change (AQ e f).charpoly = ∏ _ : Fin (finrank K (Q e f)), (X - C f.1)
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    exact charpoly_shifted f.1 (hAQ e f)
  have cBQ (e : E) :
      (BP e).charpoly = ∏ i : I e, (X - C (bb ⟨e, i⟩)) := by
    rw [charpoly_internal _ (hinner e) _ (hstableB e), Fintype.prod_sigma]
    apply Finset.prod_congr rfl
    intro f _
    change (BQ e f).charpoly = ∏ _ : Fin (finrank K (Q e f)), (X - C e.1)
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    exact charpoly_shifted e.1 (hBQ e f)
  have cABQ (e : E) :
      (AP e g * BP e).charpoly =
        ∏ i : I e, (X - C (aa ⟨e, i⟩ * bb ⟨e, i⟩)) := by
    rw [charpoly_internal _ (hinner e) _
      (fun f v hv => hstableA e f (x := BP e v) (hstableB e f hv)),
      Fintype.prod_sigma]
    apply Finset.prod_congr rfl
    intro f _
    have hcf : Commute (AQ e f) (BQ e f) := by
      apply LinearMap.ext
      intro v
      apply Subtype.ext
      exact DFunLike.congr_fun (hcommP e).eq v.1
    change (AQ e f * BQ e f).charpoly =
      ∏ _ : Fin (finrank K (Q e f)), (X - C (f.1 * e.1))
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    exact charpoly_shifted (f.1 * e.1) (shifted_mul_nilpotent hcf _ _ (hAQ e f) (hBQ e f))
  have dc (e : E) : ∏ i : I e, aa ⟨e, i⟩ = 1 := by
    let detRep : G →* K := (LinearMap.det : End K (P e) →* K).comp (AP e)
    have hdu : detRep.toHomUnits g = 1 :=
      MonoidHom.mem_ker.mp (Group.Abelianization.commutator_le_ker detRep.toHomUnits hg)
    have hd : (AP e g).det = 1 := congrArg Units.val hdu
    have hroots : (AP e g).charpoly.roots = Finset.univ.val.map (fun i : I e => aa ⟨e, i⟩) := by
      rw [cAQ e]
      exact roots_prod_linear (fun i : I e => aa ⟨e, i⟩)
    rw [Module.End.det_eq_prod_roots_charpoly_of_splits (IsAlgClosed.splits _), hroots] at hd
    simpa only [Finset.prod] using hd
  have afiber (t : K) : ∏ i ∈ Finset.univ.filter (fun i : J => bb i = t), aa i = 1 := by
    rw [Finset.prod_filter, Fintype.prod_sigma]
    apply Finset.prod_eq_one
    intro e _
    by_cases he : e.1 = t <;> simp [bb, he, dc]
  refine ⟨aa ∘ equiv, bb ∘ equiv, fun i => ⟨?_, ?_⟩, ?_, ?_, ?_, ?_⟩
  · exact eigenvalue_ne_zero (injective_representation_apply (AP (equiv i).1) g) (equiv i).2.1.2
  · exact eigenvalue_ne_zero hB (equiv i).1.2
  · simp only [Function.comp_apply]
    rw [equiv.prod_comp (fun i => X - C (aa i)), Fintype.prod_sigma,
      charpoly_internal _ houter _
        (fun e => Module.End.mapsTo_maxGenEigenspace_of_comm (hcomm g) e.1)]
    exact Finset.prod_congr rfl (fun e _ => cAQ e)
  · simp only [Function.comp_apply]
    rw [equiv.prod_comp (fun i => X - C (bb i)), Fintype.prod_sigma,
      charpoly_internal _ houter _
        (fun e => Module.End.mapsTo_maxGenEigenspace_of_comm (Commute.refl B) e.1)]
    exact Finset.prod_congr rfl (fun e _ => cBQ e)
  · simp only [Function.comp_apply]
    rw [equiv.prod_comp (fun i => X - C (aa i * bb i)), Fintype.prod_sigma,
      charpoly_internal _ houter _ (fun e v hv =>
        Module.End.mapsTo_maxGenEigenspace_of_comm (hcomm g) e.1 (x := B v)
          (Module.End.mapsTo_maxGenEigenspace_of_comm (Commute.refl B) e.1 hv))]
    exact Finset.prod_congr rfl (fun e _ => cABQ e)
  · intro t
    simpa only [Finset.prod_filter, Function.comp_apply,
      equiv.prod_comp (fun i => if bb i = t then aa i else 1)] using afiber t

end GeneralizedEigenspaces

/- The conjugacy relation identifies the two multisets of eigenvalues. -/
section UnipotentPowers

open Function Module Polynomial Set
open scoped BigOperators

private theorem perm_of_multiset_eq {ι L : Type} [Fintype ι] {a b : ι → L}
    (h : Finset.univ.val.map a = Finset.univ.val.map b) :
    ∃ σ : Equiv.Perm ι, ∀ i, b (σ i) = a i := by
  classical
  have hcounts (x : L) : Fintype.card {i // a i = x} = Fintype.card {i // b i = x} := by
    simpa only [Fintype.card_subtype, Multiset.count_map, Multiset.countP_eq_card_filter,
      ← Finset.filter_val, Finset.card, eq_comm (a := x)] using congrArg (Multiset.count x) h
  let e (x : L) := Fintype.equivOfCardEq (hcounts x)
  exact ⟨Equiv.ofFiberEquiv e, Equiv.ofFiberEquiv_map e⟩

private theorem exists_unipotent_power {K : Type} [Field K] [IsAlgClosed K]
    {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    {G : Type} [Group G] (A B : G →* End K V)
    (hcomm : ∀ x y, Commute (B y) (A x))
    (hchar : ∀ g, (A g * B g).charpoly = (B g).charpoly) :
    ∃ N : ℕ, 0 < N ∧ ∀ g ∈ commutator G, IsNilpotent (A g ^ N - 1) := by
  classical
  obtain ⟨N, hN, hexp⟩ := exists_spectral_exponent (finrank K V)
  refine ⟨N, hN, ?_⟩
  intro g hg
  obtain ⟨a, b, hnz, ha, hb, hab, hdet⟩ :=
    exists_joint_spectra A (B g) (injective_representation_apply B g) (fun x => hcomm x g) hg
  have hmul : Finset.univ.val.map (fun i => a i * b i) = Finset.univ.val.map b := by
    calc
      _ = (A g * B g).charpoly.roots := by
        rw [hab]
        exact (roots_prod_linear (fun i => a i * b i)).symm
      _ = (B g).charpoly.roots := congrArg Polynomial.roots (hchar g)
      _ = _ := by
        rw [hb]
        exact roots_prod_linear b
  obtain ⟨σ, hσ⟩ := perm_of_multiset_eq hmul
  let A' (i : Fin (finrank K V)) : Kˣ := Units.mk0 (a i) (hnz i).1
  let B' (i : Fin (finrank K V)) : Kˣ := Units.mk0 (b i) (hnz i).2
  let p (i : Fin (finrank K V)) := Classical.choose
    (show ∃ j, b j = b i from ⟨i, rfl⟩)
  have hp (i : Fin (finrank K V)) : b (p i) = b i :=
    Classical.choose_spec (show ∃ j, b j = b i from ⟨i, rfl⟩)
  have hpp (i j : Fin (finrank K V)) (h : b i = b j) : p i = p j := by
    unfold p
    congr 1
    funext x
    rw [h]
  have hdelta (i : Fin (finrank K V)) :
      B' (p (σ i)) / B' (p i) = A' i := by
    apply Units.ext
    rw [Units.val_div_eq_div_val, show (B' (p (σ i)) : K) = b (p (σ i)) from rfl,
      show (B' (p i) : K) = b (p i) from rfl, hp, hp, hσ, mul_div_cancel_right₀ _ (hnz i).2]
    rfl
  have hrel (j : Fin (finrank K V)) :
      ∑ i ∈ Finset.univ.filter (fun i => p i = j),
        (Additive.ofMul (B' (p (σ i))) - Additive.ofMul (B' (p i))) = 0 := by
    have hprod : ∏ i ∈ Finset.univ.filter (fun i => p i = j), A' i = 1 := by
      by_cases h : ∃ i, p i = j
      · obtain ⟨i, hi⟩ := h
        have hf : (fun k => p k = j) = (fun k => b k = b j) := by
          funext k
          apply propext
          constructor
          · intro hk
            rw [← hp k, hk]
          · intro hk
            exact (hpp k i (hk.trans (hi ▸ hp i))).trans hi
        have hfilter : Finset.univ.filter (fun k => p k = j) =
            Finset.univ.filter (fun k => b k = b j) := by
          ext k
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          exact Iff.of_eq (congrFun hf k)
        rw [hfilter]
        apply Units.ext
        simpa [A'] using hdet (b j)
      · push Not at h
        simp [h]
    change Additive.toMul (∑ i ∈ Finset.univ.filter (fun i => p i = j),
      (Additive.ofMul (B' (p (σ i))) - Additive.ofMul (B' (p i)))) = 1
    rw [toMul_sum]
    calc
      _ = ∏ i ∈ Finset.univ.filter (fun i => p i = j), A' i :=
        Finset.prod_congr rfl (fun i _ => hdelta i)
      _ = 1 := hprod
  have heig (i : Fin (finrank K V)) : a i ^ N = 1 := by
    have h := hexp p σ (fun j => Additive.ofMul (B' j)) hrel i
    change ((B' (p (σ i)) / B' (p i)) ^ N : Kˣ) = 1 at h
    rw [hdelta] at h
    exact congrArg Units.val h
  let P := (X ^ N - C (1 : K))
  have hd : (A g).charpoly ∣ P ^ finrank K V := by
    rw [ha]
    have hp : (∏ _ : Fin (finrank K V), P) = P ^ finrank K V := by
      rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    rw [← hp]
    apply Finset.prod_dvd_prod_of_dvd
    intro i _
    apply dvd_iff_isRoot.mpr
    simp [P, Polynomial.IsRoot, heig]
  refine ⟨finrank K V, ?_⟩
  obtain ⟨q, hq⟩ := hd
  have h := congrArg (aeval (A g)) hq
  simpa [P, LinearMap.aeval_self_charpoly] using h

end UnipotentPowers

/- Two nontrivial normal subgroups of a nonabelian free group have nontrivial intersection. -/
section NormalSubgroups

open scoped commutatorElement

private theorem free_rank_two_not_solvable : ¬ Group.IsSolvable (FreeGroup (Fin 2)) := by
  intro h
  let σ := finRotate 5
  let τ := Equiv.swap (0 : Fin 5) 1
  let f : Fin 2 → Equiv.Perm (Fin 5) := fun i => if i = 0 then σ else τ
  have hgen : Subgroup.closure ({σ, τ} : Set (Equiv.Perm (Fin 5))) = ⊤ :=
    Equiv.Perm.closure_cycle_adjacent_swap (isCycle_finRotate (n := 3))
      (support_finRotate (n := 3)) 0
  have hsurj : Function.Surjective (FreeGroup.lift f) := by
    apply MonoidHom.range_eq_top.mp
    rw [FreeGroup.range_lift_eq_closure]
    suffices Set.range f = {σ, τ} by rwa [this]
    ext x
    simp only [Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨i, rfl⟩
      fin_cases i <;> simp [f]
    · rintro (rfl | rfl)
      · exact ⟨0, rfl⟩
      · exact ⟨1, rfl⟩
  exact Equiv.Perm.not_isSolvable_fin_5 (Group.isSolvable_of_surjective hsurj)

private theorem abelian_normal_eq_bot {G : Type} [Group G] [IsFreeGroup G]
    [IsMulTorsionFree G] (hnoncomm : ¬ ∀ a b : G, Commute a b)
    (N : Subgroup G) [N.Normal] (hN : ∀ a ∈ N, ∀ b ∈ N, Commute a b) :
    N = ⊥ := by
  by_contra hne
  obtain ⟨⟨z, hzN⟩, hz0⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
  have hz : z ≠ 1 := fun h => hz0 (Subtype.ext h)
  let C := Subgroup.centralizer (N : Set G)
  have hC : C = Subgroup.centralizer ({z} : Set G) := by
    ext x
    simp only [Subgroup.mem_centralizer_iff, SetLike.mem_coe, Set.mem_singleton_iff,
      forall_eq, C]
    exact ⟨fun h => h z hzN, fun h y hy => (IsFreeGroup.commute_trans (hN y hy z hzN) h hz).eq⟩
  have hcyc : IsCyclic C := hC ▸ IsFreeGroup.isCyclic_centralizer hz
  obtain ⟨c, hc⟩ := hcyc
  have hzC : z ∈ C := fun y hy => (hN y hy z hzN).eq
  have hcn : (c : G) ≠ 1 := by
    intro he
    obtain ⟨n, hn⟩ := hc ⟨z, hzC⟩
    apply hz
    simpa [he] using (congrArg (fun x : C => (x : G)) hn).symm
  let hnormal : C.Normal := Subgroup.normal_centralizer
  have hcentral (x : G) : Commute x c.1 := by
    let x₁ : C := ⟨x * c.1 * x⁻¹, hnormal.conj_mem _ c.2 x⟩
    let x₂ : C := ⟨x⁻¹ * c.1 * x⁻¹⁻¹, hnormal.conj_mem _ c.2 x⁻¹⟩
    obtain ⟨n, hn⟩ := hc x₁
    obtain ⟨m, hm⟩ := hc x₂
    have h₁ : c.1 ^ n = x * c.1 * x⁻¹ := congrArg (fun y : C => (y : G)) hn
    have h₂ : c.1 ^ m = x⁻¹ * c.1 * x⁻¹⁻¹ := congrArg (fun y : C => (y : G)) hm
    have hpow : c.1 ^ (m * n) = c.1 := calc
      _ = (c.1 ^ m) ^ n := zpow_mul _ _ _
      _ = x⁻¹ * c.1 ^ n * x⁻¹⁻¹ := by rw [h₂]; exact (map_zpow (MulAut.conj x⁻¹) _ _).symm
      _ = _ := by rw [h₁]; group
    have hmn : m * n = 1 :=
      IsMulTorsionFree.zpow_right_injective hcn (hpow.trans (zpow_one _).symm)
    have hn' : n * n = 1 := by
      rcases Int.mul_eq_one_iff_eq_one_or_neg_one.mp hmn with h | h <;> simp [h.2]
    have hc2 : Commute (x * x) c.1 := by
      have hx : (x * x) * c.1 * (x * x)⁻¹ = c.1 := calc
        _ = x * (x * c.1 * x⁻¹) * x⁻¹ := by group
        _ = x * c.1 ^ n * x⁻¹ := by rw [h₁]
        _ = (x * c.1 * x⁻¹) ^ n := map_zpow (MulAut.conj x) _ _
        _ = _ := by rw [← h₁, ← zpow_mul, hn', zpow_one]
      exact mul_inv_eq_iff_eq_mul.mp hx
    by_cases hx : x = 1
    · simp [hx]
    · have hxx : x * x ≠ 1 := by simpa [← pow_two, sq_eq_one] using hx
      exact IsFreeGroup.commute_trans ((Commute.refl x).mul_right (Commute.refl x)) hc2 hxx
  exact hnoncomm fun a b => IsFreeGroup.commute_trans (hcentral a) (hcentral b).symm hcn

private theorem inf_normal_eq_bot {G : Type} [Group G] [IsFreeGroup G]
    [IsMulTorsionFree G] (hnoncomm : ¬ ∀ a b : G, Commute a b)
    (H L : Subgroup G) [H.Normal] [L.Normal] (h : H ⊓ L = ⊥) : H = ⊥ ∨ L = ⊥ := by
  by_cases hH : H = ⊥
  · exact Or.inl hH
  obtain ⟨⟨z, hzH⟩, hz0⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hH
  have hz : z ≠ 1 := fun h => hz0 (Subtype.ext h)
  have hc (y : G) (hy : y ∈ L) : Commute y z := by
    have hmem : ⁅z, y⁆ ∈ H ⊓ L :=
      Subgroup.commutator_le_inf H L (Subgroup.commutator_mem_commutator hzH hy)
    rw [h, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hmem
    exact hmem.symm
  exact Or.inr (abelian_normal_eq_bot hnoncomm L (fun a ha b hb =>
    IsFreeGroup.commute_trans (hc a ha) (hc b hb).symm hz))

end NormalSubgroups

/- An irreducible matrix group with finitely many traces is finite by Burnside’s theorem. -/
section FiniteTrace

open Function Module Polynomial Set
open scoped BigOperators

variable {K : Type} [Field K]
variable {V : Type} [AddCommGroup V] [Module K V]

private def preservingEnd (p : Submodule K V) : Subring (End K V) where
  carrier := {f | MapsTo f p p}
  one_mem' := fun _ h => h
  zero_mem' := fun _ _ => p.zero_mem
  add_mem' hf hg := fun _ h => p.add_mem (hf h) (hg h)
  neg_mem' hf := fun _ h => p.neg_mem (hf h)
  mul_mem' hf hg := fun _ h => hf (hg h)

private def restrictEnd (p : Submodule K V) : preservingEnd p →+* End K p where
  toFun f := f.1.restrict f.2
  map_one' := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl

private def quotientEnd (p : Submodule K V) : preservingEnd p →+* End K (V ⧸ p) where
  toFun f := p.mapQ p f.1 f.2
  map_one' := LinearMap.ext fun v => Submodule.Quotient.induction_on p v (fun _ => rfl)
  map_zero' := LinearMap.ext fun v => Submodule.Quotient.induction_on p v (fun _ => rfl)
  map_add' f g := LinearMap.ext fun v => Submodule.Quotient.induction_on p v (fun x => by
    change (Submodule.Quotient.mk (f.1 x + g.1 x) : V ⧸ p) =
      Submodule.Quotient.mk (f.1 x) + Submodule.Quotient.mk (g.1 x)
    exact Submodule.Quotient.mk_add _)
  map_mul' _ _ := LinearMap.ext fun v => Submodule.Quotient.induction_on p v (fun _ => rfl)

private theorem finite_range_trace [IsAlgClosed K] [FiniteDimensional K V] {G : Type} [Group G]
    (A : G →* End K V) {N : ℕ} (hN : N ≠ 0) (h : ∀ g, IsNilpotent (A g ^ N - 1)) :
    (Set.range fun g => LinearMap.trace K V (A g)).Finite := by
  classical
  let P := (X ^ N - C (1 : K))
  have hP : P ≠ 0 := by
    intro he
    have hd := congrArg Polynomial.natDegree he
    change (X ^ N - C (1 : K)).natDegree = (0 : K[X]).natDegree at hd
    rw [natDegree_X_pow_sub_C, natDegree_zero] at hd
    exact hN hd
  let R := {a : K // a ∈ P.roots}
  let : Fintype R := (Multiset.finite_toSet _).fintype
  let d := finrank K V
  let values : (Fin d → R) → K := fun f => ∑ i, (f i).1
  apply (Set.finite_range values).subset
  rintro _ ⟨g, rfl⟩
  let p := (A g).charpoly
  have hc : p.roots.card = d := by
    rw [(IsAlgClosed.splits p).natDegree_eq_card_roots.symm, LinearMap.charpoly_natDegree]
  have hf : ∀ a ∈ p.roots, a ∈ P.roots := by
    intro a ha
    rw [mem_roots hP]
    have hEig : (A g).HasEigenvalue a :=
      (Module.End.hasEigenvalue_iff_isRoot_charpoly _ _).mpr (isRoot_of_mem_roots ha)
    obtain ⟨v, hv⟩ := hEig.exists_hasEigenvector
    have hnil : (A g ^ N - 1).HasEigenvector (a ^ N - 1) v := by
      refine ⟨?_, hv.2⟩
      have hp := Module.End.HasEigenvector.pow_apply hv N
      simp only [Module.End.mem_eigenspace_iff, LinearMap.sub_apply,
        one_apply_eq_self, sub_smul, one_smul, hp]
    have hEig' := Module.End.hasEigenvalue_of_hasEigenvector hnil
    have hz := (Module.End.HasUnifEigenvalue.isNilpotent_of_isNilpotent (h g) hEig').eq_zero
    simpa [P, Polynomial.IsRoot] using hz
  obtain ⟨l, hl⟩ := Quotient.exists_rep p.roots
  have hcard : l.length = d := (congrArg Multiset.card hl).trans hc
  let e : Fin d ≃ Fin l.length := finCongr hcard.symm
  let vals (i : Fin d) : R :=
    ⟨l.get (e i), hf _ (by rw [← hl]; exact List.get_mem _ _)⟩
  refine ⟨vals, ?_⟩
  change values vals = LinearMap.trace K V (A g)
  rw [Module.End.trace_eq_sum_roots_charpoly_of_splits (IsAlgClosed.splits _), ← hl]
  change (∑ i : Fin d, l.get (e i)) = l.sum
  rw [e.sum_comp l.get, ← List.sum_ofFn, List.ofFn_get]

private theorem finite_of_irreducible_trace [IsAlgClosed K] [FiniteDimensional K V]
    {G : Type} [Group G] (A : G →* End K V) (hinj : Injective A)
    (htrace : (Set.range fun g => LinearMap.trace K V (A g)).Finite)
    (hirr : ∀ p : Submodule K V, (∀ g, MapsTo (A g) p p) → p = ⊥ ∨ p = ⊤) :
    Finite G := by
  classical
  let d := finrank K V
  let b := finBasis K V
  let T := LinearMap.toMatrixAlgEquiv b
  let M : G →* Matrix (Fin d) (Fin d) K := T.toMonoidHom.comp A
  let alg := Algebra.adjoin K (Set.range M)
  have hrange : Set.range M = (MonoidHom.mrange M : Set (Matrix (Fin d) (Fin d) K)) := rfl
  have hspan : alg.toSubmodule = Submodule.span K (Set.range M) := by
    rw [Algebra.adjoin_eq_span, hrange, Submonoid.closure_eq]
  have hirr' (W : Submodule K (Fin d → K))
      (hW : ∀ M' ∈ alg, ∀ v ∈ W, Matrix.mulVec M' v ∈ W) :
      W = ⊥ ∨ W = ⊤ := by
    have h := hirr (W.comap b.equivFun.toLinearMap) (fun g v hv => by
      have hs := hW (M g) (Algebra.subset_adjoin (Set.mem_range_self g)) (b.equivFun v) hv
      change (LinearMap.toMatrix b b (A g)).mulVec (b.repr v) ∈ W at hs
      change (b.repr (A g v) : Fin d → K) ∈ W
      rwa [LinearMap.toMatrix_mulVec_repr] at hs)
    exact h.imp
      (fun he => (Submodule.comap_injective_of_surjective b.equivFun.surjective)
        (he.trans ((LinearMap.ker_eq_bot.mpr b.equivFun.injective)).symm))
      (fun he => (Submodule.comap_injective_of_surjective b.equivFun.surjective)
        (he.trans (Submodule.comap_top _).symm))
  have htop := MathlibExt.Algebra.Algebra.BurnsideMatrixWanted.burnside_matrix alg hirr'
  have hall : Submodule.span K (Set.range M) = ⊤ := by rw [← hspan, htop]; rfl
  obtain ⟨s, hs, -, hsp, -⟩ := Submodule.exists_finset_span_eq_linearIndepOn K (Set.range M)
  let D := {x : K // x ∈ Set.range (fun g => LinearMap.trace K V (A g))}
  let : Fintype D := htrace.fintype
  have hm (g : G) (m : s) : (M g * (m : Matrix (Fin d) (Fin d) K)).trace ∈
      Set.range (fun g => LinearMap.trace K V (A g)) := by
    obtain ⟨g', hg'⟩ := hs m.property
    refine ⟨g * g', ?_⟩
    change LinearMap.trace K V (A (g * g')) = _
    rw [LinearMap.trace_eq_matrix_trace K b]
    change (M (g * g')).trace = _
    rw [map_mul, hg']
  let f (g : G) (m : s) : D := ⟨_, hm g m⟩
  apply Finite.of_injective f
  intro g h he
  apply hinj
  apply T.injective
  change M g = M h
  apply Matrix.ext_iff_trace_mul_right.mpr
  intro Y
  have hy : Y ∈ Submodule.span K (s : Set (Matrix (Fin d) (Fin d) K)) := by
    rw [hsp, hall]
    trivial
  induction hy using Submodule.span_induction with
  | mem m hmem =>
    exact congrArg Subtype.val (congrFun he ⟨m, hmem⟩)
  | zero => simp
  | add x y _ _ hx hy => simp only [Matrix.mul_add, Matrix.trace_add, hx, hy]
  | smul c x _ hx => simp only [Matrix.mul_smul, Matrix.trace_smul, hx]

end FiniteTrace

/- If both actions on an invariant subspace and its quotient have nontrivial kernels,
their intersection acts by commuting operators of the form 1 plus a square-zero map. -/
section FiniteFreeImage

open Function Module Polynomial Set
open scoped BigOperators

variable {K : Type} [Field K]
variable {V : Type} [AddCommGroup V] [Module K V]

private theorem finite_of_faithful_bound [IsAlgClosed K] [FiniteDimensional K V]
    {G : Type} [Group G] [IsFreeGroup G] [IsMulTorsionFree G]
    (hnoncomm : ¬ ∀ x y : G, Commute x y)
    (A : G →* End K V) (hA : Injective A) {N : ℕ} (hN : N ≠ 0)
    (hnil : ∀ g, IsNilpotent (A g ^ N - 1)) : Finite G := by
  classical
  generalize hd : finrank K V = d
  induction d using Nat.strong_induction_on generalizing V with
  | ind d ih =>
    by_cases hsimple : ∀ p : Submodule K V, (∀ g, MapsTo (A g) p p) → p = ⊥ ∨ p = ⊤
    · exact finite_of_irreducible_trace A hA (finite_range_trace A hN hnil) hsimple
    push Not at hsimple
    obtain ⟨p, hp, hp0, hp1⟩ := hsimple
    let Ap : G →* preservingEnd p := A.codRestrict (preservingEnd p) hp
    let R : G →* End K p := (restrictEnd p).toMonoidHom.comp Ap
    let Q : G →* End K (V ⧸ p) := (quotientEnd p).toMonoidHom.comp Ap
    have hnil' (g : G) : IsNilpotent (Ap g ^ N - 1) := by
      obtain ⟨k, hk⟩ := hnil g
      exact ⟨k, Subtype.ext hk⟩
    have hR : finrank K p < d := hd ▸ Submodule.finrank_lt hp1
    have hQ : finrank K (V ⧸ p) < d := by
      have hpos : 0 < finrank K p := Module.finrank_pos_iff.mpr (p.nontrivial_iff_ne_bot.mpr hp0)
      have hsum := p.finrank_quotient_add_finrank
      omega
    have hfix (g : G) (hg : g ∈ R.ker ⊓ Q.ker) (v : V) (hv : v ∈ p) : A g v = v := by
      have h := DFunLike.congr_fun (MonoidHom.mem_ker.mp hg.1) (⟨v, hv⟩ : p)
      exact congrArg Subtype.val h
    have hstep (g : G) (hg : g ∈ R.ker ⊓ Q.ker) (v : V) : A g v - v ∈ p := by
      have h := DFunLike.congr_fun (MonoidHom.mem_ker.mp hg.2)
        (Submodule.Quotient.mk v : V ⧸ p)
      change (Submodule.Quotient.mk (A g v) : V ⧸ p) = Submodule.Quotient.mk v at h
      apply (Submodule.Quotient.mk_eq_zero p).mp
      rw [Submodule.Quotient.mk_sub, h, sub_self]
    have hker : R.ker ⊓ Q.ker = ⊥ := by
      apply abelian_normal_eq_bot hnoncomm
      intro x hx y hy
      apply hA
      rw [map_mul, map_mul]
      apply LinearMap.ext
      intro v
      change A x (A y v) = A y (A x v)
      have hab (a b : G) (ha : a ∈ R.ker ⊓ Q.ker) (hb : b ∈ R.ker ⊓ Q.ker) :
          A a (A b v) = A b v - v + A a v := calc
        _ = A a (A b v - v + v) := by rw [sub_add_cancel]
        _ = _ := by rw [map_add, hfix a ha _ (hstep b hb v)]
      rw [hab x y hx hy, hab y x hy hx]
      abel
    rcases inf_normal_eq_bot hnoncomm R.ker Q.ker hker with he | he
    · have hRi := (MonoidHom.ker_eq_bot_iff R).mp he
      exact ih _ hR R hRi (fun g => by
        change IsNilpotent (restrictEnd p (Ap g) ^ N - 1)
        simpa only [map_sub, map_pow, map_one] using (hnil' g).map (restrictEnd p)) rfl
    · have hQi := (MonoidHom.ker_eq_bot_iff Q).mp he
      exact ih _ hQ Q hQi (fun g => by
        change IsNilpotent (quotientEnd p (Ap g) ^ N - 1)
        simpa only [map_sub, map_pow, map_one] using (hnil' g).map (quotientEnd p)) rfl

end FiniteFreeImage

open Function Module

private theorem no_faithful_representation {n : ℕ} (hn : 3 ≤ n)
    {K : Type} [Field K] {m : ℕ} (ρ : iaAut n →* Matrix.GeneralLinearGroup (Fin m) K)
    (hρ : Injective ρ) : False := by
  classical
  let L := AlgebraicClosure K
  let S := Matrix.GeneralLinearGroup.map (n := Fin m) (algebraMap K L)
  have hS : Injective S := by
    intro x y h
    apply Units.ext
    ext i j
    exact (algebraMap K L).injective
      (congrArg (fun g : Matrix.GeneralLinearGroup (Fin m) L => g.val i j) h)
  let M := S.comp ρ
  let V := Fin m → L
  let e : Matrix (Fin m) (Fin m) L ≃ₐ[L] End L V := Matrix.toLinAlgEquiv'
  let F : Matrix.GeneralLinearGroup (Fin m) L →* End L V :=
    e.toMonoidHom.comp (Units.coeHom (Matrix (Fin m) (Fin m) L))
  have hF : Injective F := e.injective.comp Units.val_injective
  let A := (F.comp M).comp (inner hn)
  let B := (F.comp M).comp (shift hn)
  have hA : Injective A := hF.comp (hS.comp (hρ.comp (inner_injective hn)))
  have hc (x y : SourceGroup) : Commute (B y) (A x) :=
    (inner_shift_commute hn x y).symm.map (F.comp M)
  have hchar (g : SourceGroup) : (A g * B g).charpoly = (B g).charpoly := by
    let t := M (inn (FreeGroup.of (newIndex hn)))
    let a := M (inner hn g)
    let b := M (shift hn g)
    have h := congrArg M (inner_mul_shift hn g)
    simp only [map_mul] at h
    change t * (a * b) = b * t at h
    have ht : t * (a * b) * t⁻¹ = b := by rw [h, mul_inv_cancel_right]
    have he := congrArg Units.val ht
    change t.val * (a.val * b.val) * t⁻¹.val = b.val at he
    have hinv : t⁻¹.val * t.val = (1 : Matrix (Fin m) (Fin m) L) := t.inv_val
    have hf : (a.val * b.val).charpoly = b.val.charpoly := calc
      _ = (t⁻¹.val * (t.val * (a.val * b.val))).charpoly := by
        rw [← mul_assoc, hinv, one_mul]
      _ = (t.val * (a.val * b.val) * t⁻¹.val).charpoly := Matrix.charpoly_mul_comm _ _
      _ = _ := congrArg Matrix.charpoly he
    change (F a * F b).charpoly = (F b).charpoly
    rw [← map_mul F]
    change (a.val * b.val).mulVecLin.charpoly = b.val.mulVecLin.charpoly
    simpa only [Matrix.charpoly_mulVecLin] using hf
  obtain ⟨N, hN, hnil⟩ := exists_unipotent_power A B hc hchar
  let G := commutator SourceGroup
  have hnc : ¬ ∀ x y : G, Commute x y := by
    intro h
    have hs : Group.IsSolvable G := Group.isSolvable_of_comm fun x y => (h x y).eq
    exact free_rank_two_not_solvable <|
      Group.isSolvable_commutator_iff.mp (Group.isSolvable_commutator_iff.mp hs)
  have hf : Finite G := finite_of_faithful_bound hnc (A.comp G.subtype)
    (hA.comp G.subtype_injective) hN.ne' (fun g => hnil g g.property)
  have hg : ∃ g : G, g ≠ 1 := by
    by_contra! h
    exact hnc fun x y => by rw [h x, h y]
  obtain ⟨g, hg⟩ := hg
  have hi : Infinite G := Infinite.of_injective (fun k : ℕ => g ^ k)
    (IsMulTorsionFree.pow_right_injective hg)
  exact not_finite G

/--
Resolved false: the Kourovka Archive answers 15.10 No: `IA(Fₙ)` is not linear for `n ≥ 5` (Pettet)
and for every `n ≥ 3` (Bardakov and Mikhailov). Source: E. I. Khukhro and V. D. Mazurov (eds.),
Unsolved Problems in Group Theory: The Kourovka Notebook, 21st issue, arXiv:1401.0300v49 (2026),
Archive of Solved Problems, Problem 15.10 (Yu. I. Merzlyakov; V. G. Bardakov); resolution: V. G.
Bardakov and R. Mikhailov, Commun. Algebra 36 (2008), no. 4, 1489-1499 (n ≥ 3); A. Pettet,
Cohomology of some subgroups of the automorphism group of a free group, Ph.D. thesis, 2006 (n ≥ 5),
Kourovka Archive, Problem 15.10.
-/
theorem iaAutLinear_refuted : ¬ iaAutLinear := by
  rintro ⟨n, hn, K, hK, m, ρ, hρ⟩
  exact no_faithful_representation hn ρ hρ

end MathlibExt.GroupTheory.IAAutomorphismsLinearKourovka15Problem10Wanted
