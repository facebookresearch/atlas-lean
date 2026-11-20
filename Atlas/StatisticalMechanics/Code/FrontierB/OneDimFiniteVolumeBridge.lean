/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/













import Code.FrontierB.OneDimTransferPerron
import Code.Ising.FVConsistencyProve
import Code.Lattice.ContourCountInjection

open scoped BigOperators
open Finset Matrix

namespace StatMech.FrontierB

open StatMech.Lattice StatMech.Ising StatMech.FrontierC


def site1 (z : ℤ) : Site 1 := fun _ => z


def site1Coord (x : Site 1) : ℤ := x 0

@[simp] lemma site1Coord_site1 (z : ℤ) : site1Coord (site1 z) = z := rfl

@[simp] lemma site1_site1Coord (x : Site 1) : site1 (site1Coord x) = x := by
  funext i
  fin_cases i
  rfl


def intEquivSite1 : ℤ ≃ Site 1 where
  toFun := site1
  invFun := site1Coord
  left_inv := site1Coord_site1
  right_inv := site1_site1Coord

lemma site1_mem_box_iff (z : ℤ) (n : ℕ) :
    site1 z ∈ box 1 n ↔ -(n : ℤ) ≤ z ∧ z ≤ (n : ℤ) := by
  rw [mem_box]
  simp only [site1, Fin.forall_fin_one]
  constructor
  · intro hz
    have hz' : (z.natAbs : ℤ) ≤ (n : ℤ) := by exact_mod_cast hz
    rw [← Int.abs_eq_natAbs, abs_le] at hz'
    exact hz'
  · intro hz
    have hz' : |z| ≤ (n : ℤ) := abs_le.mpr hz
    rw [Int.abs_eq_natAbs] at hz'
    exact_mod_cast hz'

lemma site1_adj_iff (z w : ℤ) :
    (hypercubicLattice 1).Adj (site1 z) (site1 w) ↔ (z - w).natAbs = 1 := by
  rw [hypercubicLattice_adj, Fin.sum_univ_one]
  rfl

lemma mem_bondFinsetTouch_mk_iff (n : ℕ) (x y : Site 1) :
    s(x, y) ∈ bondFinsetTouch 1 n ↔
      (hypercubicLattice 1).Adj x y ∧ (x ∈ box 1 n ∨ y ∈ box 1 n) := by
  constructor
  · intro he
    unfold bondFinsetTouch at he
    rw [Finset.mem_image] at he
    obtain ⟨p, hp, hpe⟩ := he
    unfold bondPairsTouch at hp
    rw [Finset.mem_filter] at hp
    obtain ⟨_, hadj, htouch⟩ := hp
    rw [Sym2.eq_iff] at hpe
    rcases hpe with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨hadj, htouch⟩
    · exact ⟨hadj.symm, htouch.symm⟩
  · rintro ⟨hadj, htouch⟩
    exact StatMech.Lattice.mk_mem_bondFinsetTouch hadj htouch


def chainBond (z : ℤ) : Sym2 (Site 1) := s(site1 z, site1 (z + 1))

lemma chainBond_mem_bondFinsetTouch_iff (z : ℤ) (n : ℕ) :
    chainBond z ∈ bondFinsetTouch 1 n ↔
      -(n : ℤ) - 1 ≤ z ∧ z ≤ (n : ℤ) := by
  rw [chainBond, mem_bondFinsetTouch_mk_iff, site1_adj_iff,
    site1_mem_box_iff, site1_mem_box_iff]
  norm_num
  omega


noncomputable def chainBondFinset (n : ℕ) : Finset (Sym2 (Site 1)) :=
  (Finset.Icc (-(n : ℤ) - 1) (n : ℤ)).image chainBond

lemma adjacent_site1_eq_chainBond (x y : Site 1)
    (hadj : (hypercubicLattice 1).Adj x y) :
    ∃ z : ℤ, s(x, y) = chainBond z := by
  rw [hypercubicLattice_adj, Fin.sum_univ_one] at hadj
  change (site1Coord x - site1Coord y).natAbs = 1 at hadj
  have hcoord := Int.natAbs_eq (site1Coord x - site1Coord y)
  rw [hadj] at hcoord
  rcases hcoord with h | h
  · refine ⟨site1Coord y, ?_⟩
    rw [← site1_site1Coord x, ← site1_site1Coord y]
    unfold chainBond
    rw [show site1Coord x = site1Coord y + 1 by omega]
    exact Sym2.eq_swap
  · refine ⟨site1Coord x, ?_⟩
    rw [← site1_site1Coord x, ← site1_site1Coord y]
    unfold chainBond
    rw [show site1Coord y = site1Coord x + 1 by omega]
    simp


theorem chainBondFinset_eq_bondFinsetTouch (n : ℕ) :
    chainBondFinset n = bondFinsetTouch 1 n := by
  ext e
  constructor
  · intro he
    rw [chainBondFinset, Finset.mem_image] at he
    obtain ⟨z, hz, rfl⟩ := he
    rw [Finset.mem_Icc] at hz
    exact (chainBond_mem_bondFinsetTouch_iff z n).mpr hz
  · intro he
    induction e with
    | h x y =>
      have hdata := (mem_bondFinsetTouch_mk_iff n x y).mp he
      obtain ⟨z, hz⟩ := adjacent_site1_eq_chainBond x y hdata.1
      rw [chainBondFinset, Finset.mem_image]
      refine ⟨z, ?_, hz.symm⟩
      rw [Finset.mem_Icc, ← chainBond_mem_bondFinsetTouch_iff z n, ← hz]
      exact he



lemma site1_injective : Function.Injective site1 := intEquivSite1.injective

lemma chainBond_injective : Function.Injective chainBond := by
  intro z w h
  unfold chainBond at h
  rw [Sym2.eq_iff] at h
  rcases h with ⟨h1, _⟩ | ⟨h1, h2⟩
  · exact site1_injective h1
  · have hz : z = w + 1 := site1_injective h1
    have hw : z + 1 = w := site1_injective h2
    omega


noncomputable def chainSiteFinset (n : ℕ) : Finset (Site 1) :=
  (Finset.Icc (-(n : ℤ)) (n : ℤ)).image site1

lemma chainSiteFinset_eq_boxFinset (n : ℕ) :
    chainSiteFinset n = boxFinset 1 n := by
  ext x
  rw [chainSiteFinset, Finset.mem_image, mem_boxFinset]
  constructor
  · rintro ⟨z, hz, rfl⟩
    rw [Finset.mem_Icc] at hz
    exact (site1_mem_box_iff z n).mpr hz
  · intro hx
    refine ⟨site1Coord x, ?_, site1_site1Coord x⟩
    rw [Finset.mem_Icc]
    apply (site1_mem_box_iff (site1Coord x) n).mp
    simpa only [site1_site1Coord] using hx

lemma sum_bondFinsetTouch_eq_chain (n : ℕ) (sigma : ConfigSpace (Site 1)) :
    (∑ e ∈ bondFinsetTouch 1 n, bond sigma e) =
      ∑ z ∈ Finset.Icc (-(n : ℤ) - 1) (n : ℤ),
        spin sigma (site1 z) * spin sigma (site1 (z + 1)) := by
  rw [← chainBondFinset_eq_bondFinsetTouch, chainBondFinset]
  rw [Finset.sum_image (Set.injOn_of_injective chainBond_injective)]
  apply Finset.sum_congr rfl
  intro z _
  simp [chainBond, bond_mk]

lemma sum_boxFinset_eq_chain (n : ℕ) (sigma : ConfigSpace (Site 1)) :
    (∑ x ∈ boxFinset 1 n, spin sigma x) =
      ∑ z ∈ Finset.Icc (-(n : ℤ)) (n : ℤ), spin sigma (site1 z) := by
  rw [← chainSiteFinset_eq_boxFinset, chainSiteFinset]
  rw [Finset.sum_image (Set.injOn_of_injective site1_injective)]



lemma sum_range_eq_sum_Icc {M : Type*} [AddCommMonoid M]
    (L : ℤ) (m : ℕ) (f : ℤ → M) :
    (∑ k ∈ Finset.range (m + 1), f (L + k)) =
      ∑ z ∈ Finset.Icc L (L + m), f z := by
  refine Finset.sum_bij
    (fun (k : ℕ) (_ : k ∈ Finset.range (m + 1)) => L + (k : ℤ)) ?_ ?_ ?_ ?_
  · intro k hk
    rw [Finset.mem_Icc]
    simp only [Finset.mem_range] at hk
    dsimp
    omega
  · intro k hk l hl heq
    dsimp at heq
    omega
  · intro z hz
    rw [Finset.mem_Icc] at hz
    let k := (z - L).toNat
    have hk : k < m + 1 := by
      dsimp [k]
      omega
    refine ⟨k, Finset.mem_range.mpr hk, ?_⟩
    dsimp [k]
    omega
  · intro k hk
    rfl

lemma sum_adjacent_half (f : ℕ → ℝ) (m : ℕ) :
    (∑ k ∈ Finset.range (m + 1), (f k + f (k + 1)) / 2) =
      (f 0 + f (m + 1)) / 2 + ∑ k ∈ Finset.range m, f (k + 1) := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [Finset.sum_range_succ]
      rw [ih]
      rw [Finset.sum_range_succ]
      ring


def boolTransferState (b : Bool) : Fin 2 := if b then 0 else 1

@[simp] lemma transferSpin_boolTransferState (b : Bool) :
    transferSpin (boolTransferState b) = if b then 1 else -1 := by
  cases b <;> simp [boolTransferState, transferSpin]

lemma transferSpin_of_config (sigma : ConfigSpace (Site 1)) (z : ℤ) :
    transferSpin (boolTransferState (sigma (site1 z))) = spin sigma (site1 z) := by
  simp [spin]

lemma isingTransferReal_apply (beta H : ℝ) (u v : Fin 2) :
    isingTransferReal beta H u v =
      Real.exp (beta * transferSpin u * transferSpin v +
        (H / 2) * (transferSpin u + transferSpin v)) := by
  fin_cases u <;> fin_cases v <;>
    simp [isingTransferReal, transferSpin] <;> ring



noncomputable def fvPathState (eta : ConfigSpace (Site 1)) (n : ℕ)
    (tau : {x // x ∈ box 1 n} → Bool) (k : ℕ) : Fin 2 :=
  boolTransferState (glue eta tau (site1 (-(n : ℤ) - 1 + k)))

lemma transferSpin_fvPathState (eta : ConfigSpace (Site 1)) (n : ℕ)
    (tau : {x // x ∈ box 1 n} → Bool) (k : ℕ) :
    transferSpin (fvPathState eta n tau k) =
      spin (glue eta tau) (site1 (-(n : ℤ) - 1 + k)) := by
  exact transferSpin_of_config _ _

lemma sum_bondFinsetTouch_eq_path (eta : ConfigSpace (Site 1)) (n : ℕ)
    (tau : {x // x ∈ box 1 n} → Bool) :
    (∑ e ∈ bondFinsetTouch 1 n, bond (glue eta tau) e) =
      ∑ k ∈ Finset.range (2 * n + 2),
        transferSpin (fvPathState eta n tau k) *
          transferSpin (fvPathState eta n tau (k + 1)) := by
  rw [sum_bondFinsetTouch_eq_chain]
  have henum := sum_range_eq_sum_Icc (-(n : ℤ) - 1) (2 * n + 1)
    (fun z => spin (glue eta tau) (site1 z) * spin (glue eta tau) (site1 (z + 1)))
  have htop : -(n : ℤ) - 1 + (2 * n + 1 : ℕ) = (n : ℤ) := by
    push_cast
    ring
  rw [htop] at henum
  rw [← henum]
  apply Finset.sum_congr rfl
  intro k hk
  rw [transferSpin_fvPathState, transferSpin_fvPathState]
  congr 2
  · congr 1
    omega

lemma sum_boxFinset_eq_path (eta : ConfigSpace (Site 1)) (n : ℕ)
    (tau : {x // x ∈ box 1 n} → Bool) :
    (∑ x ∈ boxFinset 1 n, spin (glue eta tau) x) =
      ∑ k ∈ Finset.range (2 * n + 1),
        transferSpin (fvPathState eta n tau (k + 1)) := by
  rw [sum_boxFinset_eq_chain]
  have henum := sum_range_eq_sum_Icc (-(n : ℤ)) (2 * n)
    (fun z => spin (glue eta tau) (site1 z))
  have htop : -(n : ℤ) + (2 * n : ℕ) = (n : ℤ) := by
    push_cast
    ring
  rw [htop] at henum
  rw [← henum]
  apply Finset.sum_congr rfl
  intro k hk
  rw [transferSpin_fvPathState]
  congr 2
  omega



noncomputable def fvTransferProduct (eta : ConfigSpace (Site 1)) (n : ℕ)
    (tau : {x // x ∈ box 1 n} → Bool) (beta h : ℝ) : ℝ :=
  ∏ k ∈ Finset.range (2 * n + 2),
    isingTransferReal beta (beta * h) (fvPathState eta n tau k)
      (fvPathState eta n tau (k + 1))



theorem fvWeight_eq_endpointFactor_mul_transferProduct
    (eta : ConfigSpace (Site 1)) (n : ℕ)
    (tau : {x // x ∈ box 1 n} → Bool) (beta h : ℝ) :
    fvWeight eta n (bondFinsetTouch 1 n) beta h tau =
      Real.exp (-(beta * h / 2) *
        (transferSpin (fvPathState eta n tau 0) +
          transferSpin (fvPathState eta n tau (2 * n + 2)))) *
        fvTransferProduct eta n tau beta h := by
  unfold fvWeight fvEnergy fvTransferProduct
  simp_rw [isingTransferReal_apply]
  rw [← Real.exp_sum, ← Real.exp_add]
  rw [sum_bondFinsetTouch_eq_path, sum_boxFinset_eq_path]
  rw [Finset.sum_add_distrib]
  have hbondfactor :
      (∑ k ∈ Finset.range (2 * n + 2),
        beta * transferSpin (fvPathState eta n tau k) *
          transferSpin (fvPathState eta n tau (k + 1))) =
        beta * ∑ k ∈ Finset.range (2 * n + 2),
          transferSpin (fvPathState eta n tau k) *
            transferSpin (fvPathState eta n tau (k + 1)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    ring
  rw [hbondfactor, ← Finset.mul_sum]
  have hhalf := sum_adjacent_half
    (fun k => transferSpin (fvPathState eta n tau k)) (2 * n + 1)
  rw [← Finset.sum_div] at hhalf
  have hfield :
      (∑ k ∈ Finset.range (2 * n + 2),
        (transferSpin (fvPathState eta n tau k) +
          transferSpin (fvPathState eta n tau (k + 1)))) =
        transferSpin (fvPathState eta n tau 0) +
          transferSpin (fvPathState eta n tau (2 * n + 2)) +
            2 * ∑ k ∈ Finset.range (2 * n + 1),
              transferSpin (fvPathState eta n tau (k + 1)) := by
    linarith
  rw [hfield]
  congr 1
  ring




noncomputable def box1EquivFin (n : ℕ) : {x // x ∈ box 1 n} ≃ Fin (2 * n + 1) where
  toFun x := ⟨(site1Coord x.1 + n).toNat, by
    have hx := (site1_mem_box_iff (site1Coord x.1) n).mp (by
      simpa only [site1_site1Coord] using x.2)
    omega⟩
  invFun k := ⟨site1 ((k : ℤ) - n), (site1_mem_box_iff _ _).mpr (by
    have hk := k.2
    constructor <;> omega)⟩
  left_inv x := by
    apply Subtype.ext
    change site1 ((((site1Coord x.1 + n).toNat : ℕ) : ℤ) - n) = x.1
    rw [← site1_site1Coord x.1]
    congr 1
    have hx := (site1_mem_box_iff (site1Coord x.1) n).mp (by
      simpa only [site1_site1Coord] using x.2)
    have hnonneg : 0 ≤ site1Coord x.1 + (n : ℤ) := by omega
    simp only [site1Coord_site1]
    rw [Int.toNat_of_nonneg hnonneg]
    ring
  right_inv k := by
    apply Fin.ext
    simp only [site1Coord_site1]
    have hk := k.2
    omega


def boolEquivFin2 : Bool ≃ Fin 2 where
  toFun := boolTransferState
  invFun s := if s = 0 then true else false
  left_inv b := by cases b <;> simp [boolTransferState]
  right_inv s := by fin_cases s <;> simp [boolTransferState]


noncomputable def interiorStateEquiv (n : ℕ) :
    ({x // x ∈ box 1 n} → Bool) ≃ (Fin (2 * n + 1) → Fin 2) :=
  Equiv.arrowCongr (box1EquivFin n) boolEquivFin2

lemma interiorStateEquiv_apply
    (eta : ConfigSpace (Site 1)) (n : ℕ)
    (tau : {x // x ∈ box 1 n} → Bool) (k : Fin (2 * n + 1)) :
    interiorStateEquiv n tau k = fvPathState eta n tau (k.val + 1) := by
  change boolEquivFin2 (tau ((box1EquivFin n).symm k)) =
    boolTransferState
      (glue eta tau (site1 (-(n : ℤ) - 1 + ((k.val + 1 : ℕ) : ℤ))))
  have hmem : site1 (-(n : ℤ) - 1 + ((k.val + 1 : ℕ) : ℤ)) ∈ box 1 n := by
    apply (site1_mem_box_iff _ _).mpr
    have hk := k.2
    constructor <;> omega
  rw [glue_mem _ _ hmem]
  change boolTransferState (tau ((box1EquivFin n).symm k)) = _
  apply congrArg boolTransferState
  apply congrArg tau
  apply Subtype.ext
  change site1 ((k : ℤ) - n) =
    site1 (-(n : ℤ) - 1 + ((k.val + 1 : ℕ) : ℤ))
  congr 1
  push_cast
  ring




def fvLeftBoundaryState (eta : ConfigSpace (Site 1)) (n : ℕ) : Fin 2 :=
  boolTransferState (eta (site1 (-(n : ℤ) - 1)))

def fvRightBoundaryState (eta : ConfigSpace (Site 1)) (n : ℕ) : Fin 2 :=
  boolTransferState (eta (site1 ((n : ℤ) + 1)))

lemma fvPathState_zero (eta : ConfigSpace (Site 1)) (n : ℕ)
    (tau : {x // x ∈ box 1 n} → Bool) :
    fvPathState eta n tau 0 = fvLeftBoundaryState eta n := by
  unfold fvPathState fvLeftBoundaryState
  rw [glue_not_mem]
  · simp
  · rw [site1_mem_box_iff]
    omega

lemma fvPathState_right (eta : ConfigSpace (Site 1)) (n : ℕ)
    (tau : {x // x ∈ box 1 n} → Bool) :
    fvPathState eta n tau (2 * n + 2) = fvRightBoundaryState eta n := by
  unfold fvPathState fvRightBoundaryState
  rw [show -(n : ℤ) - 1 + ((2 * n + 2 : ℕ) : ℤ) = (n : ℤ) + 1 by
    push_cast; ring]
  rw [glue_not_mem]
  rw [site1_mem_box_iff]
  omega

theorem matrix_pow_apply_walk {E R : Type*} [Fintype E] [DecidableEq E] [CommSemiring R]
    (A : Matrix E E R) :
    ∀ (n : ℕ) (i j : E),
      (A ^ n) i j =
        ∑ p : Fin n → E,
          (if (Fin.cons i p : Fin (n + 1) → E) (Fin.last n) = j then (1 : R) else 0) *
            ∏ k : Fin n, A ((Fin.cons i p : Fin (n + 1) → E) k.castSucc) (p k) := by
  intro n
  induction n with
  | zero =>
    intro i j
    simp only [pow_zero, Matrix.one_apply, Fin.prod_univ_zero, mul_one]
    rw [Fintype.sum_unique]
    simp [Fin.last]
  | succ n ih =>
    intro i j
    rw [pow_succ', Matrix.mul_apply]
    simp_rw [ih _ j, Finset.mul_sum]
    rw [← Fintype.sum_prod_type']
    rw [← Equiv.sum_comp (Fin.consEquiv fun _ : Fin (n + 1) => E)]
    have hcE : ∀ (x : E × (Fin n → E)),
        (Fin.consEquiv (fun _ : Fin (n + 1) => E)) x = Fin.cons x.1 x.2 := fun _ => rfl
    refine Finset.sum_congr rfl (fun x _ => ?_)
    obtain ⟨a, q⟩ := x
    rw [hcE]
    rw [Fin.prod_univ_succ]
    have hcond : (Fin.cons i (Fin.cons a q) : Fin (n + 2) → E) (Fin.last (n + 1))
        = (Fin.cons a q : Fin (n + 1) → E) (Fin.last n) := by
      rw [← Fin.succ_last, Fin.cons_succ]
    rw [hcond]
    simp only [Fin.castSucc_zero, Fin.cons_zero, ← Fin.succ_castSucc, Fin.cons_succ]
    ring

def openMatrixProduct {E R : Type*} [Fintype E] [DecidableEq E] [CommSemiring R]
    (A : Matrix E E R) (a b : E) {m : ℕ} (q : Fin m → E) : R :=
  ∏ k : Fin (m + 1),
    A ((Fin.cons a (Fin.snoc q b) : Fin (m + 2) → E) k.castSucc)
      ((Fin.snoc q b : Fin (m + 1) → E) k)

theorem matrix_pow_apply_eq_sum_open {E R : Type*} [Fintype E] [DecidableEq E] [CommSemiring R]
    (A : Matrix E E R) (a b : E) (m : ℕ) :
    (A ^ (m + 1)) a b = ∑ q : Fin m → E, openMatrixProduct A a b q := by
  rw [matrix_pow_apply_walk]
  rw [← Equiv.sum_comp (Fin.snocEquiv fun _ : Fin (m + 1) => E)]
  rw [Fintype.sum_prod_type]
  rw [Finset.sum_eq_single b]
  · apply Finset.sum_congr rfl
    intro q hq
    simp only [openMatrixProduct]
    rw [show (Fin.snocEquiv fun _ : Fin (m + 1) => E) (b, q) =
      Fin.snoc q b from rfl]
    rw [← Fin.succ_last, Fin.cons_succ, Fin.snoc_last]
    simp
  · intro c hc hcb
    simp [hcb]
  · simp


lemma interior_snoc_eq_path (eta : ConfigSpace (Site 1)) (n : ℕ)
    (tau : {x // x ∈ box 1 n} → Bool) :
    Fin.snoc (interiorStateEquiv n tau) (fvRightBoundaryState eta n) =
      fun k : Fin (2 * n + 2) => fvPathState eta n tau (k.val + 1) := by
  funext k
  refine Fin.lastCases ?_ (fun i => ?_) k
  · rw [Fin.snoc_last]
    simpa using (fvPathState_right eta n tau).symm
  · rw [Fin.snoc_castSucc]
    exact interiorStateEquiv_apply eta n tau i

lemma boundary_cons_snoc_eq_path (eta : ConfigSpace (Site 1)) (n : ℕ)
    (tau : {x // x ∈ box 1 n} → Bool) :
    Fin.cons (fvLeftBoundaryState eta n)
        (Fin.snoc (interiorStateEquiv n tau) (fvRightBoundaryState eta n)) =
      fun k : Fin (2 * n + 3) => fvPathState eta n tau k.val := by
  funext k
  refine Fin.cases ?_ (fun i => ?_) k
  · rw [Fin.cons_zero]
    simpa using (fvPathState_zero eta n tau).symm
  · rw [Fin.cons_succ, interior_snoc_eq_path]
    rfl

lemma fvTransferProduct_eq_openMatrixProduct
    (eta : ConfigSpace (Site 1)) (n : ℕ)
    (tau : {x // x ∈ box 1 n} → Bool) (beta h : ℝ) :
    fvTransferProduct eta n tau beta h =
      openMatrixProduct (isingTransferReal beta (beta * h))
        (fvLeftBoundaryState eta n) (fvRightBoundaryState eta n)
        (interiorStateEquiv n tau) := by
  rw [fvTransferProduct, openMatrixProduct, ← Fin.prod_univ_eq_prod_range]
  apply Finset.prod_congr rfl
  intro k hk
  rw [boundary_cons_snoc_eq_path, interior_snoc_eq_path]
  rfl



lemma sum_fvTransferProduct_eq_matrix_pow
    (eta : ConfigSpace (Site 1)) (n : ℕ) (beta h : ℝ) :
    (∑ tau : {x // x ∈ box 1 n} → Bool,
      fvTransferProduct eta n tau beta h) =
        (isingTransferReal beta (beta * h) ^ (2 * n + 2))
          (fvLeftBoundaryState eta n) (fvRightBoundaryState eta n) := by
  calc
    (∑ tau : {x // x ∈ box 1 n} → Bool,
        fvTransferProduct eta n tau beta h) =
      ∑ tau : {x // x ∈ box 1 n} → Bool,
        openMatrixProduct (isingTransferReal beta (beta * h))
          (fvLeftBoundaryState eta n) (fvRightBoundaryState eta n)
          (interiorStateEquiv n tau) := by
            apply Finset.sum_congr rfl
            intro tau htau
            exact fvTransferProduct_eq_openMatrixProduct eta n tau beta h
    _ = ∑ q : Fin (2 * n + 1) → Fin 2,
        openMatrixProduct (isingTransferReal beta (beta * h))
          (fvLeftBoundaryState eta n) (fvRightBoundaryState eta n) q :=
      Equiv.sum_comp (interiorStateEquiv n) _
    _ = (isingTransferReal beta (beta * h) ^ (2 * n + 2))
          (fvLeftBoundaryState eta n) (fvRightBoundaryState eta n) := by
      rw [show 2 * n + 2 = (2 * n + 1) + 1 by omega]
      exact (matrix_pow_apply_eq_sum_open _ _ _ _).symm


noncomputable def fvEndpointFactor (eta : ConfigSpace (Site 1)) (n : ℕ)
    (beta h : ℝ) : ℝ :=
  Real.exp (-(beta * h / 2) *
    (transferSpin (fvLeftBoundaryState eta n) +
      transferSpin (fvRightBoundaryState eta n)))

lemma fvWeight_eq_endpointFactor_mul_openProduct
    (eta : ConfigSpace (Site 1)) (n : ℕ)
    (tau : {x // x ∈ box 1 n} → Bool) (beta h : ℝ) :
    fvWeight eta n (bondFinsetTouch 1 n) beta h tau =
      fvEndpointFactor eta n beta h * fvTransferProduct eta n tau beta h := by
  rw [fvWeight_eq_endpointFactor_mul_transferProduct]
  unfold fvEndpointFactor
  rw [fvPathState_zero, fvPathState_right]



theorem fvZ_eq_endpointFactor_mul_matrix_pow
    (eta : ConfigSpace (Site 1)) (n : ℕ) (beta h : ℝ) :
    fvZ eta n (bondFinsetTouch 1 n) beta h =
      fvEndpointFactor eta n beta h *
        (isingTransferReal beta (beta * h) ^ (2 * n + 2))
          (fvLeftBoundaryState eta n) (fvRightBoundaryState eta n) := by
  unfold fvZ
  simp_rw [fvWeight_eq_endpointFactor_mul_openProduct]
  rw [← Finset.mul_sum, sum_fvTransferProduct_eq_matrix_pow]






def centerReorderEquiv (E : Type*) (n : ℕ) :
    E × ((Fin n → E) × (Fin n → E)) ≃
      (Fin n → E) × (E × (Fin n → E)) where
  toFun x := (x.2.1, (x.1, x.2.2))
  invFun x := (x.2.1, (x.1, x.2.2))
  left_inv x := by rcases x with ⟨s,l,r⟩; rfl
  right_inv x := by rcases x with ⟨l,s,r⟩; rfl

def centerPathEquiv (E : Type*) (n : ℕ) :
    E × ((Fin n → E) × (Fin n → E)) ≃ (Fin (2 * n + 1) → E) :=
  (centerReorderEquiv E n).trans
    ((Equiv.refl (Fin n → E)).prodCongr (Fin.consEquiv fun _ : Fin (n + 1) => E)) |>.trans
      (Fin.appendEquiv n (n + 1)) |>.trans
        (Equiv.arrowCongr (finCongr (by omega)) (Equiv.refl E))

lemma centerPathEquiv_apply (E : Type*) (n : ℕ) (s : E)
    (l r : Fin n → E) (k : Fin (2 * n + 1)) :
    centerPathEquiv E n (s,(l,r)) k =
      Fin.append l (Fin.cons s r) (Fin.cast (by omega) k) := by
  rfl

lemma centerPathEquiv_center (E : Type*) (n : ℕ) (s : E)
    (l r : Fin n → E) :
    centerPathEquiv E n (s,(l,r)) ⟨n, by omega⟩ = s := by
  rw [centerPathEquiv_apply]
  rw [show Fin.cast (by omega) (⟨n, by omega⟩ : Fin (2*n+1)) =
    Fin.natAdd n (0 : Fin (n+1)) by apply Fin.ext; simp]
  rw [Fin.append_right, Fin.cons_zero]


lemma centerPathEquiv_left (E : Type*) (n : ℕ) (s : E)
    (l r : Fin n → E) (i : Fin n) :
    centerPathEquiv E n (s,(l,r)) ⟨i.val, by omega⟩ = l i := by
  rw [centerPathEquiv_apply]
  rw [show Fin.cast (by omega) (⟨i.val, by omega⟩ : Fin (2*n+1)) =
    Fin.castAdd (n+1) i by apply Fin.ext; simp]
  rw [Fin.append_left]

lemma centerPathEquiv_right (E : Type*) (n : ℕ) (s : E)
    (l r : Fin n → E) (i : Fin n) :
    centerPathEquiv E n (s,(l,r)) ⟨n + 1 + i.val, by omega⟩ = r i := by
  rw [centerPathEquiv_apply]
  rw [show Fin.cast (by omega) (⟨n+1+i.val, by omega⟩ : Fin (2*n+1)) =
    Fin.natAdd n (Fin.succ i) by
      apply Fin.ext
      change n + 1 + i.val = n + (i.val + 1)
      omega]
  rw [Fin.append_right, Fin.cons_succ]

noncomputable def pathVertex {E : Type*} {m : ℕ}
    (a b : E) (q : Fin m → E) (k : ℕ) : E :=
  if h0 : k = 0 then a
  else if hk : k ≤ m then q ⟨k - 1, by omega⟩
  else b

lemma fullPath_eq_pathVertex {E : Type*} {m : ℕ}
    (a b : E) (q : Fin m → E) (k : Fin (m + 2)) :
    (Fin.cons a (Fin.snoc q b) : Fin (m + 2) → E) k =
      pathVertex a b q k.val := by
  refine Fin.cases ?_ (fun j => ?_) k
  · simp [pathVertex]
  · rw [Fin.cons_succ]
    refine Fin.lastCases ?_ (fun i => ?_) j
    · rw [Fin.snoc_last]
      simp [pathVertex, Fin.last]
    · rw [Fin.snoc_castSucc]
      simp [pathVertex]

lemma snoc_eq_pathVertex_succ {E : Type*} {m : ℕ}
    (a b : E) (q : Fin m → E) (k : Fin (m + 1)) :
    (Fin.snoc q b : Fin (m + 1) → E) k = pathVertex a b q (k.val + 1) := by
  have h := fullPath_eq_pathVertex a b q (Fin.succ k)
  rw [Fin.cons_succ] at h
  exact h

noncomputable def openMatrixProductNat {E R : Type*} [CommMonoid R]
    (A : Matrix E E R) (a b : E) {m : ℕ} (q : Fin m → E) : R :=
  ∏ k ∈ Finset.range (m + 1),
    A (pathVertex a b q k) (pathVertex a b q (k + 1))

lemma openMatrixProduct_eq_nat {E R : Type*} [Fintype E] [DecidableEq E]
    [CommSemiring R] (A : Matrix E E R) (a b : E) {m : ℕ} (q : Fin m → E) :
    openMatrixProduct A a b q = openMatrixProductNat A a b q := by
  rw [openMatrixProduct, openMatrixProductNat, Finset.prod_fin_eq_prod_range]
  apply Finset.prod_congr rfl
  intro k hk
  simp only [Finset.mem_range] at hk
  simp only [hk, dite_true]
  rw [fullPath_eq_pathVertex, snoc_eq_pathVertex_succ a b q]
  rfl

lemma pathVertex_center_left {E : Type*} (a s b : E) (n k : ℕ)
    (l r : Fin n → E) (hk : k ≤ n + 1) :
    pathVertex a b (centerPathEquiv E n (s,(l,r))) k =
      pathVertex a s l k := by
  by_cases h0 : k = 0
  · simp [pathVertex, h0]
  by_cases hn : k ≤ n
  · have hbig : k ≤ 2 * n + 1 := by omega
    simp only [pathVertex, h0, hn, hbig, dite_false, dite_true]
    exact centerPathEquiv_left E n s l r ⟨k - 1, by omega⟩
  · have hkn : k = n + 1 := by omega
    subst k
    have hbig : n + 1 ≤ 2 * n + 1 := by omega
    simp only [pathVertex, hbig, hn, dite_true, dite_false]
    simpa using centerPathEquiv_center E n s l r

lemma pathVertex_center_right {E : Type*} (a s b : E) (n k : ℕ)
    (l r : Fin n → E) (hk : k ≤ n + 1) :
    pathVertex a b (centerPathEquiv E n (s,(l,r))) (n + 1 + k) =
      pathVertex s b r k := by
  by_cases h0 : k = 0
  · subst k
    rw [pathVertex, pathVertex, dif_neg (by omega),
      dif_pos (by omega : n + 1 ≤ 2 * n + 1), dif_pos (by omega)]
    simpa using centerPathEquiv_center E n s l r
  by_cases hn : k ≤ n
  · rw [pathVertex, pathVertex, dif_neg (by omega), dif_neg h0,
      dif_pos (by omega : n + 1 + k ≤ 2 * n + 1), dif_pos hn]
    simpa only [show n + 1 + k - 1 = n + 1 + (k - 1) by omega] using
      centerPathEquiv_right E n s l r ⟨k - 1, by omega⟩
  · have hkn : k = n + 1 := by omega
    subst k
    rw [pathVertex, pathVertex, dif_neg (by omega), dif_neg (by omega),
      dif_neg (by omega), dif_neg (by omega)]

theorem openMatrixProduct_center_factor {E R : Type*} [Fintype E] [DecidableEq E]
    [CommSemiring R] (A : Matrix E E R) (a s b : E) (n : ℕ)
    (l r : Fin n → E) :
    openMatrixProduct A a b (centerPathEquiv E n (s,(l,r))) =
      openMatrixProduct A a s l * openMatrixProduct A s b r := by
  rw [openMatrixProduct_eq_nat, openMatrixProduct_eq_nat,
    openMatrixProduct_eq_nat]
  unfold openMatrixProductNat
  conv_lhs =>
    rw [show 2 * n + 1 + 1 = (n + 1) + (n + 1) by omega]
  rw [Finset.prod_range_add]
  congr 1
  · apply Finset.prod_congr rfl
    intro k hk
    simp only [Finset.mem_range] at hk
    rw [pathVertex_center_left a s b n k l r (by omega),
      pathVertex_center_left a s b n (k + 1) l r (by omega)]
  · apply Finset.prod_congr rfl
    intro k hk
    simp only [Finset.mem_range] at hk
    rw [pathVertex_center_right a s b n k l r (by omega)]
    rw [show n + 1 + k + 1 = n + 1 + (k + 1) by omega]
    rw [pathVertex_center_right a s b n (k + 1) l r (by omega)]

theorem sum_openMatrixProduct_center {E R : Type*} [Fintype E] [DecidableEq E]
    [CommSemiring R] (A : Matrix E E R) (a s b : E) (n : ℕ) :
    (∑ q : Fin (2 * n + 1) → E,
      if q ⟨n, by omega⟩ = s then openMatrixProduct A a b q else 0) =
        (A ^ (n + 1)) a s * (A ^ (n + 1)) s b := by
  rw [← Equiv.sum_comp (centerPathEquiv E n)
    (fun q => if q ⟨n, by omega⟩ = s then openMatrixProduct A a b q else 0)]
  rw [Fintype.sum_prod_type]
  simp_rw [Fintype.sum_prod_type]
  simp_rw [centerPathEquiv_center]
  rw [Finset.sum_eq_single s]
  · simp_rw [openMatrixProduct_center_factor]
    simp only [if_true]
    rw [← Finset.sum_mul_sum]
    rw [← matrix_pow_apply_eq_sum_open, ← matrix_pow_apply_eq_sum_open]
  · intro c hc hcs
    simp [hcs]
  · simp


lemma interiorStateEquiv_center
    (eta : ConfigSpace (Site 1)) (n : ℕ)
    (tau : {x // x ∈ box 1 n} → Bool) :
    interiorStateEquiv n tau ⟨n, by omega⟩ = fvPathState eta n tau (n + 1) := by
  exact interiorStateEquiv_apply eta n tau ⟨n, by omega⟩

theorem sum_fvTransferProduct_center_eq_matrix_pow
    (eta : ConfigSpace (Site 1)) (n : ℕ) (beta h : ℝ) (s : Fin 2) :
    (∑ tau : {x // x ∈ box 1 n} → Bool,
      if fvPathState eta n tau (n + 1) = s then
        fvTransferProduct eta n tau beta h else 0) =
      (isingTransferReal beta (beta * h) ^ (n + 1))
          (fvLeftBoundaryState eta n) s *
        (isingTransferReal beta (beta * h) ^ (n + 1))
          s (fvRightBoundaryState eta n) := by
  calc
    _ = ∑ tau : {x // x ∈ box 1 n} → Bool,
        if interiorStateEquiv n tau ⟨n, by omega⟩ = s then
          openMatrixProduct (isingTransferReal beta (beta * h))
            (fvLeftBoundaryState eta n) (fvRightBoundaryState eta n)
            (interiorStateEquiv n tau) else 0 := by
      apply Finset.sum_congr rfl
      intro tau htau
      rw [interiorStateEquiv_center eta n tau,
        fvTransferProduct_eq_openMatrixProduct]
    _ = ∑ q : Fin (2 * n + 1) → Fin 2,
        if q ⟨n, by omega⟩ = s then
          openMatrixProduct (isingTransferReal beta (beta * h))
            (fvLeftBoundaryState eta n) (fvRightBoundaryState eta n) q else 0 :=
      by
        simpa only using (Equiv.sum_comp (interiorStateEquiv n)
          (fun q : Fin (2 * n + 1) → Fin 2 =>
            if q (⟨n, by omega⟩ : Fin (2 * n + 1)) = s then
              (openMatrixProduct (isingTransferReal beta (beta * h))
                (fvLeftBoundaryState eta n) (fvRightBoundaryState eta n) q)
            else 0))
    _ = _ := sum_openMatrixProduct_center _ _ _ _ _



noncomputable def fvCenterStateProb (eta : ConfigSpace (Site 1)) (n : ℕ)
    (beta h : ℝ) (s : Fin 2) : ℝ :=
  ∑ tau : {x // x ∈ box 1 n} → Bool,
    if fvPathState eta n tau (n + 1) = s then
      fvProb eta n (bondFinsetTouch 1 n) beta h tau else 0

theorem sum_fvWeight_center_eq_matrix_pow
    (eta : ConfigSpace (Site 1)) (n : ℕ) (beta h : ℝ) (s : Fin 2) :
    (∑ tau : {x // x ∈ box 1 n} → Bool,
      if fvPathState eta n tau (n + 1) = s then
        fvWeight eta n (bondFinsetTouch 1 n) beta h tau else 0) =
      fvEndpointFactor eta n beta h *
        ((isingTransferReal beta (beta * h) ^ (n + 1))
            (fvLeftBoundaryState eta n) s *
          (isingTransferReal beta (beta * h) ^ (n + 1))
            s (fvRightBoundaryState eta n)) := by
  simp_rw [fvWeight_eq_endpointFactor_mul_openProduct]
  have hfactor :
      (∑ tau : {x // x ∈ box 1 n} → Bool,
        if fvPathState eta n tau (n + 1) = s then
          fvEndpointFactor eta n beta h * fvTransferProduct eta n tau beta h else 0) =
        fvEndpointFactor eta n beta h *
          ∑ tau : {x // x ∈ box 1 n} → Bool,
            if fvPathState eta n tau (n + 1) = s then
              fvTransferProduct eta n tau beta h else 0 := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro tau htau
    by_cases hc : fvPathState eta n tau (n + 1) = s <;> simp [hc]
  rw [hfactor, sum_fvTransferProduct_center_eq_matrix_pow]

theorem fvCenterStateProb_eq_matrix_ratio
    (eta : ConfigSpace (Site 1)) (n : ℕ) (beta h : ℝ) (s : Fin 2) :
    fvCenterStateProb eta n beta h s =
      ((isingTransferReal beta (beta * h) ^ (n + 1))
          (fvLeftBoundaryState eta n) s *
        (isingTransferReal beta (beta * h) ^ (n + 1))
          s (fvRightBoundaryState eta n)) /
      (isingTransferReal beta (beta * h) ^ (2 * n + 2))
        (fvLeftBoundaryState eta n) (fvRightBoundaryState eta n) := by
  unfold fvCenterStateProb fvProb
  have hdiv :
      (∑ tau : {x // x ∈ box 1 n} → Bool,
        if fvPathState eta n tau (n + 1) = s then
          fvWeight eta n (bondFinsetTouch 1 n) beta h tau /
            fvZ eta n (bondFinsetTouch 1 n) beta h else 0) =
        (∑ tau : {x // x ∈ box 1 n} → Bool,
          if fvPathState eta n tau (n + 1) = s then
            fvWeight eta n (bondFinsetTouch 1 n) beta h tau else 0) /
              fvZ eta n (bondFinsetTouch 1 n) beta h := by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro tau htau
    by_cases hc : fvPathState eta n tau (n + 1) = s <;> simp [hc]
  rw [hdiv]
  have hsum :
      (∑ tau : {x // x ∈ box 1 n} → Bool,
        (if fvPathState eta n tau (n + 1) = s then
          fvWeight eta n (bondFinsetTouch 1 n) beta h tau else 0)) =
        fvEndpointFactor eta n beta h *
          ((isingTransferReal beta (beta * h) ^ (n + 1))
              (fvLeftBoundaryState eta n) s *
            (isingTransferReal beta (beta * h) ^ (n + 1))
              s (fvRightBoundaryState eta n)) :=
    sum_fvWeight_center_eq_matrix_pow eta n beta h s
  rw [hsum, fvZ_eq_endpointFactor_mul_matrix_pow]
  apply mul_div_mul_left
  exact (Real.exp_pos _).ne'

theorem fvCenterStateProb_tendsto
    (eta : ℕ → ConfigSpace (Site 1)) (beta h : ℝ) (s : Fin 2) :
    Filter.Tendsto
      (fun n => fvCenterStateProb (eta n) n beta h s)
      Filter.atTop (nhds (isingTransferProjectorPlus beta (beta * h) s s)) := by
  have hshift : Filter.Tendsto (fun n : ℕ => n + 1) Filter.atTop Filter.atTop := by
    rw [Filter.tendsto_atTop]
    intro N
    filter_upwards [Filter.eventually_ge_atTop N] with n hn
    omega
  have hfixed (a b : Fin 2) : Filter.Tendsto
      (fun n : ℕ =>
        (isingTransferReal beta (beta * h) ^ (n + 1)) a s *
          (isingTransferReal beta (beta * h) ^ (n + 1)) s b /
            (isingTransferReal beta (beta * h) ^ (2 * n + 2)) a b)
      Filter.atTop (nhds (isingTransferProjectorPlus beta (beta * h) s s)) := by
    have ht := (isingTransfer_central_state_weight_tendsto beta (beta * h) a s b).comp hshift
    simpa only [Function.comp_apply, show ∀ n : ℕ, 2 * (n + 1) = 2 * n + 2 by omega]
      using ht
  rw [Metric.tendsto_atTop]
  intro eps heps
  obtain ⟨N00, h00⟩ := (Metric.tendsto_atTop.mp (hfixed 0 0)) eps heps
  obtain ⟨N01, h01⟩ := (Metric.tendsto_atTop.mp (hfixed 0 1)) eps heps
  obtain ⟨N10, h10⟩ := (Metric.tendsto_atTop.mp (hfixed 1 0)) eps heps
  obtain ⟨N11, h11⟩ := (Metric.tendsto_atTop.mp (hfixed 1 1)) eps heps
  refine ⟨max (max N00 N01) (max N10 N11), fun n hn => ?_⟩
  rw [fvCenterStateProb_eq_matrix_ratio]
  have hn00 : N00 ≤ n := le_trans (le_max_left _ _) (le_trans (le_max_left _ _) hn)
  have hn01 : N01 ≤ n := le_trans (le_max_right _ _) (le_trans (le_max_left _ _) hn)
  have hn10 : N10 ≤ n := le_trans (le_max_left _ _) (le_trans (le_max_right _ _) hn)
  have hn11 : N11 ≤ n := le_trans (le_max_right _ _) (le_trans (le_max_right _ _) hn)
  generalize hL : fvLeftBoundaryState (eta n) n = L
  generalize hR : fvRightBoundaryState (eta n) n = R
  fin_cases L <;> fin_cases R
  · simpa only [hL, hR] using h00 n hn00
  · simpa only [hL, hR] using h01 n hn01
  · simpa only [hL, hR] using h10 n hn10
  · simpa only [hL, hR] using h11 n hn11


def centerStateEvent (s : Fin 2) : Set (ConfigSpace (Site 1)) :=
  {sigma | boolTransferState (sigma (origin 1)) = s}

lemma measurableSet_centerStateEvent (s : Fin 2) :
    MeasurableSet (centerStateEvent s) := by
  have hcoord : Measurable (fun sigma : ConfigSpace (Site 1) => sigma (origin 1)) :=
    measurable_pi_apply _
  have hstate : Measurable (fun b : Bool => boolTransferState b) :=
    measurable_of_finite _
  exact (hstate.comp hcoord) (measurableSet_singleton s)

lemma origin_one_eq_site1_zero : origin 1 = site1 0 := by
  funext i
  fin_cases i
  rfl

lemma fvPathState_center (eta : ConfigSpace (Site 1)) (n : ℕ)
    (tau : {x // x ∈ box 1 n} → Bool) :
    fvPathState eta n tau (n + 1) =
      boolTransferState (glue eta tau (origin 1)) := by
  unfold fvPathState
  rw [origin_one_eq_site1_zero]
  congr 2
  push_cast
  ring_nf



theorem fvMeasure_centerStateEvent_real
    (eta : ConfigSpace (Site 1)) (n : ℕ) (beta h : ℝ) (s : Fin 2) :
    (fvMeasure eta n (bondFinsetTouch 1 n) beta h).real (centerStateEvent s) =
      fvCenterStateProb eta n beta h s := by
  rw [fvMeasure_real_eq eta n (bondFinsetTouch 1 n) beta h
    (measurableSet_centerStateEvent s)]
  unfold fvCenterStateProb
  apply Finset.sum_congr rfl
  intro tau htau
  rw [fvPathState_center]
  by_cases hs : boolTransferState (glue eta tau (origin 1)) = s
  · rw [if_pos hs]
    simp [centerStateEvent, hs]
  · rw [if_neg hs]
    simp [centerStateEvent, hs]



theorem fvMeasure_centerStateEvent_tendsto
    (eta : ℕ → ConfigSpace (Site 1)) (beta h : ℝ) (s : Fin 2) :
    Filter.Tendsto
      (fun n => (fvMeasure (eta n) n (bondFinsetTouch 1 n) beta h).real
        (centerStateEvent s))
      Filter.atTop (nhds (isingTransferProjectorPlus beta (beta * h) s s)) := by
  simpa only [fvMeasure_centerStateEvent_real] using
    fvCenterStateProb_tendsto eta beta h s




def splitReorderEquiv (E : Type*) (m n : ℕ) :
    E × ((Fin m → E) × (Fin n → E)) ≃
      (Fin m → E) × (E × (Fin n → E)) where
  toFun x := (x.2.1, (x.1, x.2.2))
  invFun x := (x.2.1, (x.1, x.2.2))
  left_inv x := by rcases x with ⟨s, l, r⟩; rfl
  right_inv x := by rcases x with ⟨l, s, r⟩; rfl


def splitPathEquiv (E : Type*) (m n : ℕ) :
    E × ((Fin m → E) × (Fin n → E)) ≃ (Fin (m + n + 1) → E) :=
  (splitReorderEquiv E m n).trans
    ((Equiv.refl (Fin m → E)).prodCongr (Fin.consEquiv fun _ : Fin (n + 1) => E)) |>.trans
      (Fin.appendEquiv m (n + 1)) |>.trans
        (Equiv.arrowCongr (finCongr (by omega)) (Equiv.refl E))

lemma splitPathEquiv_apply (E : Type*) (m n : ℕ) (s : E)
    (l : Fin m → E) (r : Fin n → E) (k : Fin (m + n + 1)) :
    splitPathEquiv E m n (s, (l, r)) k =
      Fin.append l (Fin.cons s r) (Fin.cast (by omega) k) := by
  rfl

lemma splitPathEquiv_center (E : Type*) (m n : ℕ) (s : E)
    (l : Fin m → E) (r : Fin n → E) :
    splitPathEquiv E m n (s, (l, r)) ⟨m, by omega⟩ = s := by
  rw [splitPathEquiv_apply]
  rw [show Fin.cast (by omega) (⟨m, by omega⟩ : Fin (m + n + 1)) =
    Fin.natAdd m (0 : Fin (n + 1)) by apply Fin.ext; simp]
  rw [Fin.append_right, Fin.cons_zero]

lemma splitPathEquiv_left (E : Type*) (m n : ℕ) (s : E)
    (l : Fin m → E) (r : Fin n → E) (i : Fin m) :
    splitPathEquiv E m n (s, (l, r)) ⟨i.val, by omega⟩ = l i := by
  rw [splitPathEquiv_apply]
  rw [show Fin.cast (by omega) (⟨i.val, by omega⟩ : Fin (m + n + 1)) =
    Fin.castAdd (n + 1) i by apply Fin.ext; simp]
  rw [Fin.append_left]

lemma splitPathEquiv_right (E : Type*) (m n : ℕ) (s : E)
    (l : Fin m → E) (r : Fin n → E) (i : Fin n) :
    splitPathEquiv E m n (s, (l, r)) ⟨m + 1 + i.val, by omega⟩ = r i := by
  rw [splitPathEquiv_apply]
  rw [show Fin.cast (by omega) (⟨m + 1 + i.val, by omega⟩ : Fin (m + n + 1)) =
    Fin.natAdd m (Fin.succ i) by
      apply Fin.ext
      change m + 1 + i.val = m + (i.val + 1)
      omega]
  rw [Fin.append_right, Fin.cons_succ]

lemma pathVertex_split_left {E : Type*} (a s b : E) (m n k : ℕ)
    (l : Fin m → E) (r : Fin n → E) (hk : k ≤ m + 1) :
    pathVertex a b (splitPathEquiv E m n (s, (l, r))) k =
      pathVertex a s l k := by
  by_cases h0 : k = 0
  · simp [pathVertex, h0]
  by_cases hm : k ≤ m
  · have hbig : k ≤ m + n + 1 := by omega
    simp only [pathVertex, h0, hm, hbig, dite_false, dite_true]
    exact splitPathEquiv_left E m n s l r ⟨k - 1, by omega⟩
  · have hkm : k = m + 1 := by omega
    subst k
    have hbig : m + 1 ≤ m + n + 1 := by omega
    simp only [pathVertex, hbig, hm, dite_true, dite_false]
    simpa using splitPathEquiv_center E m n s l r

lemma pathVertex_split_right {E : Type*} (a s b : E) (m n k : ℕ)
    (l : Fin m → E) (r : Fin n → E) (hk : k ≤ n + 1) :
    pathVertex a b (splitPathEquiv E m n (s, (l, r))) (m + 1 + k) =
      pathVertex s b r k := by
  by_cases h0 : k = 0
  · subst k
    rw [pathVertex, pathVertex, dif_neg (by omega),
      dif_pos (by omega : m + 1 ≤ m + n + 1), dif_pos (by omega)]
    simpa using splitPathEquiv_center E m n s l r
  by_cases hn : k ≤ n
  · rw [pathVertex, pathVertex, dif_neg (by omega), dif_neg h0,
      dif_pos (by omega : m + 1 + k ≤ m + n + 1), dif_pos hn]
    simpa only [show m + 1 + k - 1 = m + 1 + (k - 1) by omega] using
      splitPathEquiv_right E m n s l r ⟨k - 1, by omega⟩
  · have hkn : k = n + 1 := by omega
    subst k
    rw [pathVertex, pathVertex, dif_neg (by omega), dif_neg (by omega),
      dif_neg (by omega), dif_neg (by omega)]

theorem openMatrixProduct_split_factor {E R : Type*} [Fintype E] [DecidableEq E]
    [CommSemiring R] (A : Matrix E E R) (a s b : E) (m n : ℕ)
    (l : Fin m → E) (r : Fin n → E) :
    openMatrixProduct A a b (splitPathEquiv E m n (s, (l, r))) =
      openMatrixProduct A a s l * openMatrixProduct A s b r := by
  rw [openMatrixProduct_eq_nat, openMatrixProduct_eq_nat, openMatrixProduct_eq_nat]
  unfold openMatrixProductNat
  conv_lhs =>
    rw [show m + n + 1 + 1 = (m + 1) + (n + 1) by omega]
  rw [Finset.prod_range_add]
  congr 1
  · apply Finset.prod_congr rfl
    intro k hk
    simp only [Finset.mem_range] at hk
    rw [pathVertex_split_left a s b m n k l r (by omega),
      pathVertex_split_left a s b m n (k + 1) l r (by omega)]
  · apply Finset.prod_congr rfl
    intro k hk
    simp only [Finset.mem_range] at hk
    rw [pathVertex_split_right a s b m n k l r (by omega)]
    rw [show m + 1 + k + 1 = m + 1 + (k + 1) by omega]
    rw [pathVertex_split_right a s b m n (k + 1) l r (by omega)]

theorem sum_openMatrixProduct_split {E R : Type*} [Fintype E] [DecidableEq E]
    [CommSemiring R] (A : Matrix E E R) (a s b : E) (m n : ℕ) :
    (∑ q : Fin (m + n + 1) → E,
      if q ⟨m, by omega⟩ = s then openMatrixProduct A a b q else 0) =
        (A ^ (m + 1)) a s * (A ^ (n + 1)) s b := by
  rw [← Equiv.sum_comp (splitPathEquiv E m n)
    (fun q => if q ⟨m, by omega⟩ = s then openMatrixProduct A a b q else 0)]
  rw [Fintype.sum_prod_type]
  simp_rw [Fintype.sum_prod_type]
  simp_rw [splitPathEquiv_center]
  rw [Finset.sum_eq_single s]
  · simp_rw [openMatrixProduct_split_factor]
    simp only [if_true]
    rw [← Finset.sum_mul_sum]
    rw [← matrix_pow_apply_eq_sum_open, ← matrix_pow_apply_eq_sum_open]
  · intro c hc hcs
    simp [hcs]
  · simp


end StatMech.FrontierB
