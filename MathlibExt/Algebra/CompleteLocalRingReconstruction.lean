/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Defs
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Defs
import Mathlib.Algebra.Algebra.Unitization
import Mathlib.Algebra.MvPolynomial.Rename
import Mathlib.Algebra.Ring.ULift
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.PerfectClosure
import Mathlib.LinearAlgebra.SModEq.Pow
import Mathlib.Logic.Equiv.Fintype
import Mathlib.RingTheory.AdicCompletion.Topology
import Mathlib.RingTheory.Finiteness.Prod
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.LocalRing.RingHom.Basic
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.Nilpotent.Basic
import Mathlib.RingTheory.WittVector.Complete
import Mathlib.RingTheory.WittVector.DiscreteValuationRing
import Mathlib.RingTheory.WittVector.TeichmullerSeries
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring
import MathlibExt.RingTheory.AdicCompletion.ModuleFinite

/-!
# Reconstructing complete local rings from quotients

OWR-1453-004: Reconstructing complete local rings from finite quotients.
If complete local Noetherian rings `A`, `B` satisfy `A/𝔪^r ≅ B/𝔫^r`
for every natural number `r`, must `A ≅ B`?

Source record `OWR-1453-004__30000671`.

`conjecture_refuted` gives a counterexample. Over the perfect closure of a rational
function field in variables `xᵢ` over `𝔽₂`, an automorphism of each truncated Witt ring
carries the vector with coordinates `xᵢ` to the one with coordinates `x₂ᵢ`.
No field automorphism sends every `xᵢ` to `x₂ᵢ`.
A finite algebra with cube-zero nilradical encodes the marked element in its multiplication.
The two rings are finite algebras over the ring of Witt vectors of that field, so they have mixed
characteristic: characteristic zero and residue characteristic two.
-/

@[expose] public section

namespace MathlibExt.Algebra.CompleteLocalRingReconstructionWanted

/-- **Complete local ring reconstruction conjecture.** The statement that any two commutative
Noetherian local rings $A$ and $B$, with maximal ideals $\mathfrak m_A$ and $\mathfrak m_B$, that
are complete and Hausdorff for the $\mathfrak m_A$-adic and $\mathfrak m_B$-adic topologies are
isomorphic as rings whenever $A/\mathfrak m_A^r$ and $B/\mathfrak m_B^r$ are isomorphic as rings
for every natural number $r$.

Source: OWR-1453-004. -/
def conjecture : Prop :=
  ∀ (A B : Type*) [CommRing A] [CommRing B] [IsLocalRing A] [IsLocalRing B]
    [IsNoetherianRing A] [IsNoetherianRing B]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    [IsAdicComplete (IsLocalRing.maximalIdeal B) B],
    (∀ r : ℕ, Nonempty (A ⧸ (IsLocalRing.maximalIdeal A) ^ r ≃+*
      B ⧸ (IsLocalRing.maximalIdeal B) ^ r)) →
    Nonempty (A ≃+* B)

section Coefficients

-- A permutation can send the first n variables to the first n even variables.
private abbrev P := MvPolynomial ℕ (ZMod 2)
private abbrev K := FractionRing P

private noncomputable def x (i : ℕ) : K := algebraMap P K (MvPolynomial.X i)

private noncomputable def rename (e : Equiv.Perm ℕ) : K ≃+* K :=
  IsFractionRing.ringEquivOfRingEquiv ((MvPolynomial.renameEquiv (ZMod 2) e).toRingEquiv)

private theorem rename_x (e : Equiv.Perm ℕ) (i : ℕ) : rename e (x i) = x (e i) := by
  simp [rename, x]

private theorem finite_prefix (n : ℕ) : ∃ e : K ≃+* K, ∀ i < n, e (x i) = x (2 * i) := by
  obtain ⟨s, hs⟩ := Equiv.Perm.exists_extending_pair (Fin.val (n := n))
    (fun i : Fin n ↦ 2 * i.val) Fin.val_injective (by
      intro i j h
      apply Fin.ext
      change 2 * i.val = 2 * j.val at h
      omega)
  exact ⟨rename s, fun i hi ↦ (rename_x s i).trans (congrArg x (hs ⟨i, hi⟩))⟩

private abbrev F := PerfectClosure K 2
private noncomputable abbrev incl := PerfectClosure.of K 2
private noncomputable abbrev y (i : ℕ) := incl (x i)

private theorem perfect_ext {f g : F →+* F} (h : f.comp incl = g.comp incl) : f = g :=
  (PerfectClosure.lift K 2 F).symm.injective h

private noncomputable def extendHom (e : K ≃+* K) : F →+* F :=
  (PerfectClosure.lift K 2 F) (incl.comp e.toRingHom)

private theorem extend_of (e : K ≃+* K) (a : K) : extendHom e (incl a) = incl (e a) :=
  DFunLike.congr_fun ((PerfectClosure.lift K 2 F).symm_apply_apply (incl.comp e.toRingHom)) a

private theorem extend_comp (e : K ≃+* K) :
    (extendHom e).comp (extendHom e.symm) = RingHom.id F := by
  apply perfect_ext
  ext1 a
  simp [RingHom.comp_apply, extend_of]

private noncomputable def extendPerm (e : K ≃+* K) : F ≃+* F :=
  RingEquiv.ofRingHom _ _ (extend_comp e) (extend_comp e.symm)

private theorem extendPerm_of (e : K ≃+* K) (a : K) :
    extendPerm e (incl a) = incl (e a) := extend_of _ _

private theorem finite_perfect (n : ℕ) : ∃ e : F ≃+* F, ∀ i < n, e (y i) = y (2 * i) := by
  obtain ⟨g, hg⟩ := finite_prefix n
  exact ⟨extendPerm g, fun i hi ↦ (extend_of _ _).trans (congrArg incl (hg i hi))⟩

-- The odd transposition fixes every even variable. After a putative automorphism it
-- would fix generators, hence would be the identity on the perfect closure.
private theorem no_global : ¬ ∃ e : F ≃+* F, ∀ i, e (y i) = y (2 * i) := by
  rintro ⟨e, he⟩
  let s := extendPerm (rename (Equiv.swap 1 3))
  have hfix (i : ℕ) : s (e (y i)) = e (y i) := by
    rw [he]
    change extendPerm _ (incl _) = _
    rw [extendPerm_of, rename_x, Equiv.swap_apply_of_ne_of_ne] <;> omega
  have h : s.toRingHom.comp e.toRingHom = e.toRingHom := by
    apply perfect_ext
    apply IsLocalization.ringHom_ext (nonZeroDivisors P)
    apply MvPolynomial.ringHom_ext'
    · exact Subsingleton.elim _ _
    · exact hfix
  have hall (a : F) : s a = a := by
    obtain ⟨b, rfl⟩ := e.surjective a
    exact DFunLike.congr_fun h b
  have h31 := hall (y 1)
  change extendPerm _ (incl _) = _ at h31
  rw [extendPerm_of, rename_x, Equiv.swap_apply_left] at h31
  have hX := (IsFractionRing.injective P K) (incl.injective h31)
  have hn : (3 : ℕ) = 1 := MvPolynomial.X_injective hX
  omega

private abbrev W := WittVector 2 F
private noncomputable abbrev twoIdeal : Ideal W := Ideal.span {((2 : ℕ) : W)}

private noncomputable def wittEquiv (e : F ≃+* F) : W ≃+* W :=
  RingEquiv.ofBijective (WittVector.map e.toRingHom)
    ⟨WittVector.map_injective _ e.injective, WittVector.map_surjective _ e.surjective⟩

private theorem map_twoIdeal (e : W ≃+* W) : twoIdeal = twoIdeal.map (e : W →+* W) := by
  simp [twoIdeal, Ideal.map_span, -Nat.cast_ofNat]

private noncomputable def residuePerm (e : W ≃+* W) : F ≃+* F :=
  WittVector.quotientPEquiv.symm.trans
    ((Ideal.quotientEquiv twoIdeal twoIdeal e (map_twoIdeal e)).trans WittVector.quotientPEquiv)

private theorem residue_eq (e : W ≃+* W) (a : W) :
    residuePerm e (a.coeff 0) = (e a).coeff 0 := by
  let z := Ideal.Quotient.mk twoIdeal a
  have hz : WittVector.quotientPEquiv z = a.coeff 0 := rfl
  rw [← hz]
  simp only [residuePerm, RingEquiv.trans_apply, RingEquiv.symm_apply_apply]
  exact congrArg WittVector.quotientPEquiv
    (Ideal.quotientEquiv_mk twoIdeal twoIdeal e (map_twoIdeal e) a)

-- An automorphism agrees with the lift of its residue action on Teichmüller representatives:
-- taking successive square roots in the residue field improves agreement by powers of 2.
private theorem wittEquiv_eq_map (e : W ≃+* W) (a : W) :
    e a = WittVector.map (residuePerm e).toRingHom a := by
  let g : W →+* W := WittVector.map (residuePerm e).toRingHom
  have h0 (b : W) : e b ≡ g b [SMOD twoIdeal] := by
    apply SModEq.sub_mem.mpr
    rw [WittVector.mem_span_p_iff_coeff_zero_eq_zero (p := 2)]
    change WittVector.constantCoeff (e b - g b) = 0
    rw [map_sub, sub_eq_zero]
    exact (residue_eq e b).symm
  have ht (b : F) : e (WittVector.teichmuller 2 b) = g (WittVector.teichmuller 2 b) := by
    apply (IsHausdorff.eq_iff_smodEq (I := twoIdeal)).mpr
    intro n
    rw [smul_eq_mul, Ideal.mul_top]
    obtain ⟨c, hc⟩ : ∃ c : F, c ^ 2 ^ n = b :=
      ⟨_, iterate_frobeniusEquiv_symm_pow_p_pow F 2 b n⟩
    rw [← hc, map_pow, map_pow, map_pow]
    have hp : ((2 : ℕ) : W) ∈ twoIdeal := Ideal.subset_span (by simp)
    exact ((h0 (WittVector.teichmuller 2 c)).pow_pow_add_one hp n).mono
      (Ideal.pow_le_pow_right (by omega))
  apply (IsHausdorff.eq_iff_smodEq (I := twoIdeal)).mpr
  intro n
  rw [smul_eq_mul, Ideal.mul_top]
  apply SModEq.idealQuotientMk.mpr
  let q := Ideal.Quotient.mk (twoIdeal ^ n)
  have hnil : IsNilpotent ((2 : ℕ) : W ⧸ twoIdeal ^ n) := by
    refine ⟨n, ?_⟩
    rw [← map_natCast q 2]
    rw [← map_pow]
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    exact Ideal.pow_mem_pow (Ideal.subset_span (by simp)) n
  have := WittVector.eq_of_apply_teichmuller_eq (p := 2) (q.comp e.toRingHom) (q.comp g)
    hnil (fun b ↦ congrArg q (ht b))
  exact DFunLike.congr_fun this a

private noncomputable def allCoords : W := WittVector.mk 2 y
private noncomputable def evenCoords : W := WittVector.mk 2 (fun i ↦ y (2 * i))

private theorem marked_truncations (n : ℕ) :
    ∃ e : W ⧸ twoIdeal ^ n ≃+* W ⧸ twoIdeal ^ n,
      e (Ideal.Quotient.mk _ allCoords) = Ideal.Quotient.mk _ evenCoords := by
  obtain ⟨d, hd⟩ := finite_perfect n
  let e := wittEquiv d
  refine ⟨Ideal.quotientEquiv _ _ e (by rw [Ideal.map_pow, ← map_twoIdeal]), ?_⟩
  rw [Ideal.quotientEquiv_mk, Ideal.Quotient.eq]
  rw [twoIdeal, Ideal.span_singleton_pow, WittVector.mem_span_p_pow_iff_le_coeff_eq_zero]
  apply WittVector.le_coeff_eq_iff_le_sub_coeff_eq_zero.mp
  exact hd

private theorem marked_global : ¬ ∃ e : W ≃+* W, e allCoords = evenCoords := by
  rintro ⟨e, he⟩
  apply no_global
  refine ⟨residuePerm e, fun i ↦ ?_⟩
  exact congrArg (fun v : W ↦ v.coeff i) ((wittEquiv_eq_map e allCoords).symm.trans he)

end Coefficients

noncomputable section

variable {R : Type*} [CommRing R]

-- In the nilradical the products of distinct basis vectors vanish. The square of the i-th
-- vector is 2 ^ i times a direction in the last two coordinates, which annihilate the radical.
private abbrev Axes (R : Type*) := Fin 4 → R
private def NilPart {R : Type*} (_a : R) := Axes R × (R × R)

private instance instAddNilPart (a : R) : AddCommGroup (NilPart a) :=
  inferInstanceAs (AddCommGroup (Axes R × R × R))
private instance instModuleNilPart (a : R) : Module R (NilPart a) :=
  inferInstanceAs (Module R (Axes R × R × R))

private def direction (a : R) : Fin 4 → R × R := ![(1, 0), (0, 1), (1, 1), (1, a)]

private def weightedDir (a : R) (i : Fin 4) : R × R := (2 : R) ^ i.val • direction a i

private def form (a : R) (v w : Axes R) : R × R := ∑ i, (v i * w i) • weightedDir a i

private instance instRingNilPart (a : R) : NonUnitalCommRing (NilPart a) where
  __ := instAddNilPart a
  mul x y := (0, form a x.1 y.1)
  zero_mul x := by
    change (0, form a 0 x.1) = (0, 0)
    simp [form]
  mul_zero x := by
    change (0, form a x.1 0) = (0, 0)
    simp [form]
  left_distrib x y z := by
    change (0, form a x.1 (y.1 + z.1)) = (0 + 0, form a x.1 y.1 + form a x.1 z.1)
    simp [form, mul_add, add_smul, Finset.sum_add_distrib]
  right_distrib x y z := by
    change (0, form a (x.1 + y.1) z.1) = (0 + 0, form a x.1 z.1 + form a y.1 z.1)
    simp [form, add_mul, add_smul, Finset.sum_add_distrib]
  mul_comm x y := by
    change (0, form a x.1 y.1) = (0, form a y.1 x.1)
    simp [form, mul_comm]
  mul_assoc x y z := by
    change (0, form a 0 z.1) = (0, form a x.1 0)
    simp [form]

private instance instTowerNilPart (a : R) : IsScalarTower R (NilPart a) (NilPart a) where
  smul_assoc r x y := by
    change (0, form a (r • x.1) y.1) = (r • 0, r • form a x.1 y.1)
    simp [form, Finset.smul_sum, smul_smul, mul_assoc]

private instance instSMulCommNilPart (a : R) : SMulCommClass R (NilPart a) (NilPart a) where
  smul_comm r x y := by
    change (r • 0, r • form a x.1 y.1) = (0, form a x.1 (r • y.1))
    simp [form, Finset.smul_sum, smul_smul, mul_left_comm]

private abbrev EncodingRing (a : R) := Unitization R (NilPart a)

private def scalar (a : R) : R →+* EncodingRing a := Unitization.inlRingHom _ _
private def proj (a : R) : EncodingRing a →+* R := (Unitization.fstHom R (NilPart a)).toRingHom
private def nilElem (a : R) (v : Axes R) (w : R × R) : EncodingRing a := Unitization.mk (0, (v, w))
private def axisPart {a : R} (z : EncodingRing a) : Axes R := z.snd.1
private def planePart {a : R} (z : EncodingRing a) : R × R := z.snd.2

private theorem rad_mul (a : R) (v v' : Axes R) (w w' : R × R) :
    nilElem a v w * nilElem a v' w' = nilElem a 0 (form a v v') := by
  exact (Unitization.inr_mul (A := NilPart a) R ((v, w) : NilPart a) ((v', w') : NilPart a)).symm

private theorem mul_soc (a : R) (z : EncodingRing a) (w : R × R) :
    z * nilElem a 0 w = nilElem a 0 (z.fst • w) := by
  apply Unitization.ext
  · simp [nilElem]
  · apply Prod.ext
    · change z.fst • (0 : Axes R) + (0 : R) • z.snd.1 + 0 = 0
      simp
    · change z.fst • w + (0 : R) • z.snd.2 + form a z.snd.1 0 = z.fst • w
      simp [form]

private theorem nil_rad (a : R) (v : Axes R) (w : R × R) : IsNilpotent (nilElem a v w) := by
  refine ⟨3, ?_⟩
  rw [pow_succ, sq, rad_mul, rad_mul]
  simp [form, nilElem]
  rfl

private theorem nil_iff [IsDomain R] (a : R) (z : EncodingRing a) : IsNilpotent z ↔ z.fst = 0 := by
  refine ⟨fun h ↦ isNilpotent_iff_eq_zero.mp (h.map (proj a)), fun h ↦ ?_⟩
  have hz : z = nilElem a z.snd.1 z.snd.2 := Unitization.ext h rfl
  rw [hz]
  exact nil_rad ..

private theorem unit_of_fst (a : R) (z : EncodingRing a) (h : IsUnit z.fst) : IsUnit z := by
  have hz : z = scalar a z.fst + nilElem a z.snd.1 z.snd.2 := by
    apply Unitization.ext
    · simp [scalar, nilElem]
    · change z.snd = (0 : NilPart a) + z.snd
      simp
  rw [hz]
  exact (nil_rad ..).isUnit_add_left_of_commute (h.map (scalar a)) (.all ..)

private instance instLocalEncodingRing [IsLocalRing R] (a : R) : IsLocalRing (EncodingRing a) :=
  IsLocalRing.of_isUnit_or_isUnit_of_isUnit_add fun {x y} h ↦
    (IsLocalRing.isUnit_or_isUnit_of_isUnit_add (h.map (proj a))).imp (unit_of_fst a x)
      (unit_of_fst a y)

private instance instFiniteEncodingRing (a : R) : Module.Finite R (EncodingRing a) := by
  have : Module.Finite R (NilPart a) := inferInstanceAs (Module.Finite R (Axes R × R × R))
  exact Module.Finite.equiv (Unitization.linearEquiv R R (NilPart a)).symm

private instance instNoetherianEncodingRing [IsNoetherianRing R] (a : R) :
    IsNoetherianRing (EncodingRing a) :=
  isNoetherian_of_tower R inferInstance

private def coord (i : Fin 4) (r : R) : Axes R := fun j ↦ if j = i then r else 0
private def axis (a : R) (i : Fin 4) : EncodingRing a := nilElem a (coord i 1) 0

private theorem form_coord (a : R) (v : Axes R) (i : Fin 4) (r : R) :
    form a v (coord i r) = (v i * r) • weightedDir a i := by
  simp [form, coord, mul_ite, ite_smul]

private theorem rad_sq (a : R) (i : Fin 4) (r : R) (w : R × R) :
    nilElem a (coord i r) w ^ 2 = nilElem a 0 ((r * r) • weightedDir a i) := by
  rw [sq, rad_mul, form_coord]
  simp [coord]

private theorem axis_sq (a : R) (i : Fin 4) : axis a i ^ 2 = nilElem a 0 (weightedDir a i) := by
  simp [axis, rad_sq]

private def lead (i : Fin 4) (w : R × R) : R := if i = 1 then w.2 else w.1

private theorem lead_smul (i : Fin 4) (r : R) (w : R × R) :
    lead i (r • w) = r * lead i w := by
  by_cases h : i = 1 <;> simp [lead, h]

private theorem lead_dir (a : R) (i : Fin 4) : lead i (direction a i) = 1 := by
  fin_cases i <;> rfl

private def det (x y : R × R) : R := x.1 * y.2 - x.2 * y.1

private theorem det_smul (r s : R) (x y : R × R) :
    det (r • x) (s • y) = r * s * det x y := by
  simp [det]
  ring

private theorem dir_ne_parallel {a : R} (ha : a ≠ 0) (ha' : a ≠ 1)
    [Nontrivial R] {i j : Fin 4} (hij : i ≠ j) : det (direction a i) (direction a j) ≠ 0 := by
  fin_cases i <;> fin_cases j <;> simp_all [direction, det] <;> grind

private theorem maps_nil [IsDomain R] {a b : R} (e : EncodingRing a ≃+* EncodingRing b)
    (z : EncodingRing a)
    (h : z.fst = 0) : (e z).fst = 0 :=
  (nil_iff ..).mp (((nil_iff a z).mpr h).map e.toRingHom)

private def redHom {a b : R} (e : EncodingRing a ≃+* EncodingRing b) : R →+* R :=
  (proj b).comp (e.toRingHom.comp (scalar a))

private theorem fst_map [IsDomain R] {a b : R} (e : EncodingRing a ≃+* EncodingRing b)
    (z : EncodingRing a) :
    (e z).fst = redHom e z.fst := by
  have h := maps_nil e (z - scalar a z.fst) (by simp [scalar])
  rw [map_sub] at h
  exact sub_eq_zero.mp h

private theorem comp_red [IsDomain R] {a b : R} (e : EncodingRing a ≃+* EncodingRing b) :
    (redHom e).comp (redHom e.symm) = RingHom.id R := by
  ext1 t
  change redHom e (e.symm (scalar b t)).fst = t
  rw [← fst_map, e.apply_symm_apply]
  rfl

private def redPerm [IsDomain R] {a b : R} (e : EncodingRing a ≃+* EncodingRing b) : R ≃+* R :=
  RingEquiv.ofRingHom _ _ (comp_red e) (comp_red e.symm)

private theorem axis_products [IsDomain R] {a : R} (i : Fin 4)
    (z : EncodingRing a) (hz : z.fst = 0) :
    ∃ t : EncodingRing a, axis a i * z = t * axis a i ^ 2 := by
  obtain ⟨v, w, h⟩ : ∃ v w, z = nilElem a v w := ⟨z.snd.1, z.snd.2, Unitization.ext hz rfl⟩
  rw [h, axis_sq]
  use scalar a (v i)
  rw [mul_soc, mul_comm (axis a i)]
  change nilElem a v w * nilElem a (coord i 1) 0 = nilElem a 0 (v i • weightedDir a i)
  rw [rad_mul, form_coord, mul_one]

private theorem image_products [IsDomain R] {a b : R} (e : EncodingRing a ≃+* EncodingRing b)
    (i : Fin 4) (z : EncodingRing b) (hz : z.fst = 0) :
    ∃ t : EncodingRing b, e (axis a i) * z = t * e (axis a i) ^ 2 := by
  obtain ⟨t, ht⟩ := axis_products i _ (maps_nil e.symm z hz)
  exact ⟨e t, by simpa using congrArg e ht⟩

-- Multiplication of an axis by the nilradical has cyclic image generated by its square.
-- Two nonzero coordinates in its image under an isomorphism would give independent directions.
private theorem image_coord [IsDomain R] (hp : (2 : R) ≠ 0) {a b : R}
    (hb : b ≠ 0) (hb' : b ≠ 1) (e : EncodingRing a ≃+* EncodingRing b) (i : Fin 4) :
    ∃ (j : Fin 4) (u : R) (w : R × R), IsUnit u ∧ e (axis a i) = nilElem b (coord j u) w := by
  let z := e (axis a i)
  let v := axisPart z
  let w := planePart z
  have hz : z = nilElem b v w := Unitization.ext (maps_nil e _ rfl) rfl
  let D := form b v v
  have prod (j : Fin 4) : ∃ c : R, v j • weightedDir b j = c • D := by
    obtain ⟨t, ht⟩ := image_products e i (axis b j) rfl
    change z * nilElem b (coord j 1) 0 = t * z ^ 2 at ht
    rw [hz, sq, rad_mul, rad_mul, mul_soc, form_coord, mul_one] at ht
    exact ⟨t.fst, congrArg planePart ht⟩
  have nz : ∃ j, v j ≠ 0 := by
    by_contra! h
    have hv : v = 0 := funext h
    have hzero : z ^ 2 = 0 := by
      rw [hz, hv, sq, rad_mul]
      simp [form, nilElem]
      rfl
    change e (axis a i) ^ 2 = 0 at hzero
    rw [← map_pow, map_eq_zero_iff e e.injective, axis_sq] at hzero
    have := congrArg (fun t : EncodingRing a ↦ lead i (planePart t)) hzero
    change lead i (weightedDir a i) = lead i 0 at this
    rw [weightedDir, lead_smul, lead_dir, mul_one] at this
    have hz0 : lead i (0 : R × R) = 0 := by simp [lead]
    exact pow_ne_zero _ hp (this.trans hz0)
  obtain ⟨j, hj⟩ := nz
  have hv : v = coord j (v j) := by
    funext k
    by_cases h : k = j
    · simp [coord, h]
    simp only [coord, ite_eq_right h]
    obtain ⟨c, hc⟩ := prod k
    obtain ⟨d, hd⟩ := prod j
    have he : det (v k • weightedDir b k) (v j • weightedDir b j) = 0 := by
      rw [hc, hd, det_smul]
      simp [det, mul_comm]
    rw [det_smul, weightedDir, weightedDir, det_smul] at he
    simpa [mul_eq_zero, hp, hj, dir_ne_parallel hb hb' h] using he
  obtain ⟨c, hc⟩ := prod j
  have hD : D = (v j * v j) • weightedDir b j := by
    change form b v v = _
    conv_lhs => rw [hv, form_coord]
    simp [coord]
  rw [hD, smul_smul] at hc
  have hL := congrArg (lead j) hc
  simp only [weightedDir, lead_smul, lead_dir, mul_one] at hL
  have h1 : v j = c * (v j * v j) := mul_right_cancel₀ (pow_ne_zero _ hp) hL
  have h2 : 1 = c * v j := mul_right_cancel₀ hj (by simpa [mul_assoc] using h1)
  exact ⟨j, v j, w, isUnit_iff_dvd_one.mpr ⟨c, by rwa [mul_comm]⟩, hz.trans (by rw [← hv])⟩

private theorem scalar_mul_soc (a r : R) (z : EncodingRing a) :
    planePart (scalar a r * z) = r • planePart z := by
  change r • z.snd.2 + z.fst • (0 : R × R) + form a 0 z.snd.1 = _
  simp [form, planePart]

private theorem two_pow_scalar (a : R) (n : ℕ) :
    (2 : EncodingRing a) ^ n = scalar a ((2 : R) ^ n) := by
  rw [map_pow, map_ofNat]

-- Divisibility by powers of 2 distinguishes the four axes, even over the same residue field.
private theorem two_pow_dvd_direction [IsDomain R] (hp : (2 : R) ≠ 0) (hpu : ¬ IsUnit (2 : R))
    (a : R) (i : Fin 4) (u : R) (hu : IsUnit u) (n : ℕ) :
    (2 : EncodingRing a) ^ n ∣ nilElem a 0 (u • weightedDir a i) ↔ n ≤ i.val := by
  rw [two_pow_scalar]
  constructor
  · rintro ⟨z, h⟩
    have h1 := congrArg (fun z : EncodingRing a ↦ lead i (planePart z)) h
    change lead i (u • weightedDir a i) = lead i (planePart (scalar a ((2 : R) ^ n) * z)) at h1
    rw [scalar_mul_soc, weightedDir, lead_smul, lead_smul, lead_dir, mul_one, lead_smul] at h1
    exact (pow_dvd_pow_iff hp hpu).mp (hu.dvd_mul_left.mp ⟨_, h1⟩)
  · intro h
    obtain ⟨d, hd⟩ := pow_dvd_pow (2 : R) h
    refine ⟨nilElem a 0 ((u * d) • direction a i), ?_⟩
    rw [mul_soc, weightedDir, hd]
    change nilElem a 0 _ = nilElem a 0 ((2 : R) ^ n • _)
    simp [smul_smul, mul_comm, mul_assoc]

private theorem map_square [IsDomain R] (hp : (2 : R) ≠ 0) (hpu : ¬ IsUnit (2 : R))
    {a b : R} (hb : b ≠ 0) (hb' : b ≠ 1) (e : EncodingRing a ≃+* EncodingRing b) (i : Fin 4) :
    ∃ t : R, IsUnit t ∧ e (nilElem a 0 (weightedDir a i)) = nilElem b 0 (t • weightedDir b i) := by
  obtain ⟨j, u, w, hu, h⟩ := image_coord hp hb hb' e i
  have hs := congrArg (· ^ 2) h
  rw [← map_pow, axis_sq, rad_sq] at hs
  have hh (n : ℕ) : n ≤ i.val ↔ n ≤ j.val := by
    rw [← two_pow_dvd_direction hp hpu a i 1 isUnit_one, one_smul,
      ← two_pow_dvd_direction hp hpu b j (u * u) (hu.mul hu), ← hs]
    simpa only [map_pow, map_ofNat] using
      (map_dvd_iff e (a := (2 : EncodingRing a) ^ n) (b := nilElem a 0 (weightedDir a i))).symm
  obtain rfl : i = j := Fin.ext (le_antisymm ((hh _).mp le_rfl) ((hh _).mpr le_rfl))
  exact ⟨u * u, hu.mul hu, hs⟩

private theorem scalar_mul_rad (a r : R) (v : Axes R) (w : R × R) :
    scalar a r * nilElem a v w = nilElem a (r • v) (r • w) :=
  Unitization.inl_mul_inr (A := NilPart a) r ((v, w) : NilPart a)

private theorem cancel_two_pow [IsDomain R] (hp : (2 : R) ≠ 0) (a : R) (n : ℕ)
    {z z' : EncodingRing a} (h : (2 : EncodingRing a) ^ n * z = (2 : EncodingRing a) ^ n * z') :
    z = z' := by
  rw [two_pow_scalar] at h
  have h0 := congrArg (proj a) h
  simp only [map_mul] at h0
  apply Unitization.ext
  · exact mul_left_cancel₀ (pow_ne_zero _ hp) h0
  · have hh : (2 : R) ^ n • z = (2 : R) ^ n • z' := by
      simpa only [Algebra.smul_def, Unitization.algebraMap_eq_inlRingHom, scalar] using h
    have h1 : (2 : R) ^ n • axisPart z = (2 : R) ^ n • axisPart z' := congrArg axisPart hh
    have h2 : (2 : R) ^ n • planePart z = (2 : R) ^ n • planePart z' := congrArg planePart hh
    exact Prod.ext ((smul_right_injective _ (pow_ne_zero n hp)) h1)
      ((smul_right_injective _ (pow_ne_zero n hp)) h2)

private theorem map_direction [IsDomain R] (hp : (2 : R) ≠ 0) (hpu : ¬ IsUnit (2 : R))
    {a b : R} (hb : b ≠ 0) (hb' : b ≠ 1) (e : EncodingRing a ≃+* EncodingRing b) (i : Fin 4) :
    ∃ t : R, IsUnit t ∧ e (nilElem a 0 (direction a i)) = nilElem b 0 (t • direction b i) := by
  obtain ⟨t, ht, h⟩ := map_square hp hpu hb hb' e i
  refine ⟨t, ht, cancel_two_pow hp b i.val ?_⟩
  have H (c : R) (w : R × R) :
      (2 : EncodingRing c) ^ i.val * nilElem c 0 w = nilElem c 0 ((2 : R) ^ i.val • w) := by
    rw [two_pow_scalar, scalar_mul_rad, smul_zero]
  calc
    _ = e ((2 : EncodingRing a) ^ i.val * nilElem a 0 (direction a i)) := by
      rw [map_mul, map_pow, map_ofNat]
    _ = _ := by
      rw [H, H]
      simpa only [weightedDir, smul_comm t] using h

-- Once the axes are fixed, the first three directions force a common scale on the plane.
-- The slope of the fourth then determines the image of the parameter.
private theorem redPerm_apply_parameter [IsDomain R] (hp : (2 : R) ≠ 0) (hpu : ¬ IsUnit (2 : R))
    {a b : R} (hb : b ≠ 0) (hb' : b ≠ 1) (e : EncodingRing a ≃+* EncodingRing b) :
    redPerm e a = b := by
  choose t ht h using map_direction hp hpu hb hb' e
  let p (c : R) := nilElem c 0 (1, 0)
  let q (c : R) := nilElem c 0 (0, 1)
  have h0 : e (p a) = nilElem b 0 (t 0, 0) := by simpa [direction, p] using h 0
  have h1 : e (q a) = nilElem b 0 (0, t 1) := by simpa [direction, q] using h 1
  have sum_pair (v w : R × R) : nilElem b 0 v + nilElem b 0 w = nilElem b 0 (v+w) := by
    apply Unitization.ext
    · exact add_zero _
    · exact Prod.ext (zero_add _) rfl
  have split (c d : R) : nilElem c 0 (1, d) = p c + scalar c d * q c := by
    rw [mul_soc]
    apply Unitization.ext
    · exact (add_zero _).symm
    · apply Prod.ext
      · exact (zero_add _).symm
      · change (1, d) = (1, 0) + d • ((0, 1) : R × R)
        simp
  have compare (i : Fin 4) (r s : R) (hr : direction a i = (1, r)) (hs : direction b i = (1, s)) :
      (t 0, redHom e r * t 1) = (t i, t i * s) := by
    have H := h i
    rw [hr, hs, split, map_add, map_mul, h0, h1, mul_soc, sum_pair] at H
    have := congrArg planePart H
    change ((t 0, 0) + (e (scalar a r)).fst • ((0, t 1) : R × R)) =
      t i • (1, s) at this
    simpa [redHom, proj, Prod.smul_mk] using this
  have h2 := compare 2 1 1 rfl rfl
  have h3 := compare 3 a b rfl rfl
  have heq : t 0 = t 1 := by
    calc
      _ = t 2 := congrArg Prod.fst h2
      _ = t 1 := by simpa using (congrArg Prod.snd h2).symm
  have hz : redHom e a * t 1 = b * t 1 := by
    calc
      _ = t 3 * b := congrArg Prod.snd h3
      _ = _ := by rw [← (show t 0 = t 3 from congrArg Prod.fst h3), heq, mul_comm]
  exact mul_right_cancel₀ (ht 1).ne_zero hz

variable {S : Type*} [CommRing S]

private theorem map_pair_smul (f : R →+* S) (r : R) (w : R × R) :
    f.prodMap f (r • w) = f r • f.prodMap f w := by
  ext <;> simp [RingHom.coe_prodMap, map_mul]

private theorem map_weightedDir (f : R →+* S) (a : R) (i : Fin 4) :
    f.prodMap f (weightedDir a i) = weightedDir (f a) i := by
  rw [weightedDir, map_pair_smul, map_pow, map_ofNat, weightedDir]
  congr 1
  fin_cases i <;> simp [direction, RingHom.coe_prodMap]

private theorem map_form (f : R →+* S) (a : R) (v w : Axes R) :
    f.prodMap f (form a v w) = form (f a) (f ∘ v) (f ∘ w) := by
  simp [form, map_pair_smul, map_weightedDir]

private def mapEncoding {a : R} {b : S} (f : R →+* S) (h : f a = b) :
    EncodingRing a →+* EncodingRing b where
  toFun z := Unitization.mk (f z.fst, (f ∘ axisPart z, f.prodMap f (planePart z)))
  map_one' := by
    apply Unitization.ext (map_one f)
    apply Prod.ext
    · exact funext fun _ ↦ map_zero f
    · exact map_zero _
  map_zero' := by
    apply Unitization.ext (map_zero f)
    apply Prod.ext
    · exact funext fun _ ↦ map_zero f
    · exact map_zero _
  map_add' z z' := by
    apply Unitization.ext (map_add f ..)
    apply Prod.ext
    · exact funext fun _ ↦ map_add f ..
    · exact map_add _ ..
  map_mul' z z' := by
    apply Unitization.ext (map_mul f ..)
    apply Prod.ext
    · funext i
      change f (z.fst * axisPart z' i + z'.fst * axisPart z i + 0) =
        f z.fst * f (axisPart z' i) + f z'.fst * f (axisPart z i) + 0
      simp
    · change f.prodMap f (z.fst • planePart z' + z'.fst • planePart z +
        form a (axisPart z) (axisPart z')) =
        f z.fst • f.prodMap f (planePart z') + f z'.fst • f.prodMap f (planePart z) +
        form b (f ∘ axisPart z) (f ∘ axisPart z')
      simp only [map_add, map_pair_smul, map_form, h]

private theorem mapEncoding_surjective {a : R} {b : S} {f : R →+* S} (hf : Function.Surjective f)
    (h : f a = b) : Function.Surjective (mapEncoding f h) := by
  intro z
  obtain ⟨c, hc⟩ := hf z.fst
  choose v hv using fun i ↦ hf (axisPart z i)
  obtain ⟨s, hs⟩ := hf (planePart z).1
  obtain ⟨t, ht⟩ := hf (planePart z).2
  exact ⟨Unitization.mk (c, (v, (s, t))),
    Unitization.ext hc (Prod.ext (funext hv) (Prod.ext hs ht))⟩

open IsLocalRing in
private noncomputable def quotPowEquiv [IsLocalRing R] [IsLocalRing S]
    (n : ℕ) (f : R →+* S) (hf : Function.Surjective f) (hk : RingHom.ker f ≤ maximalIdeal R ^ n) :
    R ⧸ maximalIdeal R ^ n ≃+* S ⧸ maximalIdeal S ^ n := by
  let q := Ideal.Quotient.mk (maximalIdeal S ^ n)
  have h : RingHom.ker (q.comp f) = maximalIdeal R ^ n := by
    rw [← RingHom.comap_ker, Ideal.mk_ker, ← map_maximalIdeal_of_surjective f hf, ← Ideal.map_pow,
      Ideal.comap_map_of_surjective' f hf, sup_eq_left.mpr hk]
  exact (Ideal.quotEquivOfEq h.symm).trans <|
    RingHom.quotientKerEquivOfSurjective (f := q.comp f) (Ideal.Quotient.mk_surjective.comp hf)

open IsLocalRing in
private theorem ker_mapEncoding_le [IsLocalRing R] {n : ℕ} (hpu : ¬ IsUnit (2 : R))
    {a : R} {b : S} {f : R →+* S} (h : f a = b)
    (hf : ∀ r, f r = 0 → (2 : R) ^ n ∣ r) :
    RingHom.ker (mapEncoding f h) ≤ maximalIdeal (EncodingRing a) ^ n := by
  intro z hz
  have he : mapEncoding f h z = 0 := hz
  obtain ⟨c, hc⟩ := hf _ (congrArg (fun u : EncodingRing b ↦ u.fst) he)
  choose v hv using fun i ↦ hf _ (congrArg (fun u : EncodingRing b ↦ axisPart u i) he)
  obtain ⟨s, hs⟩ := hf _ (congrArg (fun u : EncodingRing b ↦ (planePart u).1) he)
  obtain ⟨t, ht⟩ := hf _ (congrArg (fun u : EncodingRing b ↦ (planePart u).2) he)
  let d : EncodingRing a := Unitization.mk (c, (v, (s, t)))
  have hzm : z = (2 : R) ^ n • d :=
    Unitization.ext hc (Prod.ext (funext hv) (Prod.ext hs ht))
  have hp : (2 : EncodingRing a) ∈ maximalIdeal (EncodingRing a) := fun hu ↦ hpu (by
    simpa only [map_ofNat] using hu.map (proj a))
  rw [hzm, Algebra.smul_def, map_pow, map_ofNat]
  exact Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow hp n)

-- Reduce every coordinate modulo 2 ^ n. Both resulting maps are surjective with kernels
-- contained in the n-th maximal ideal powers, so both rings have the same n-th quotient.
open IsLocalRing in
private def quotientEncodingEquiv {a b : R} [IsLocalRing R] (hpu : ¬ IsUnit (2 : R))
    (n : ℕ) (hn : 0 < n) (e : R ⧸ Ideal.span {(2 : R) ^ n} ≃+* R ⧸ Ideal.span {(2 : R) ^ n})
    (he : e (Ideal.Quotient.mk _ a) = Ideal.Quotient.mk _ b) :
    EncodingRing a ⧸ maximalIdeal (EncodingRing a) ^ n ≃+*
      EncodingRing b ⧸ maximalIdeal (EncodingRing b) ^ n := by
  let J := Ideal.span {(2 : R) ^ n}
  let q := Ideal.Quotient.mk J
  have hne : J ≠ ⊤ := by
    rw [ne_eq, Ideal.span_singleton_eq_top]
    exact fun hu ↦ hpu ((isUnit_pow_iff hn.ne').mp hu)
  let : Nontrivial (R ⧸ J) := Ideal.Quotient.nontrivial_iff.mpr hne
  let : IsLocalRing (R ⧸ J) := IsLocalRing.of_surjective' q Ideal.Quotient.mk_surjective
  have hq (r : R) (hr : q r = 0) : (2 : R) ^ n ∣ r :=
    Ideal.mem_span_singleton.mp (Ideal.Quotient.eq_zero_iff_mem.mp hr)
  let l := mapEncoding (e.toRingHom.comp q) he
  let r := mapEncoding q (rfl : q b = q b)
  have hl := mapEncoding_surjective (f := e.toRingHom.comp q)
    (e.surjective.comp Ideal.Quotient.mk_surjective) he
  have hker := ker_mapEncoding_le (f := e.toRingHom.comp q) hpu he
    (fun z hz ↦ hq z (e.injective (hz.trans (map_zero e).symm)))
  exact (quotPowEquiv n l hl hker).trans
    (quotPowEquiv n r (mapEncoding_surjective Ideal.Quotient.mk_surjective rfl)
      (ker_mapEncoding_le hpu rfl hq)).symm

end

open IsLocalRing

private theorem witt_maximal : maximalIdeal W = twoIdeal :=
  (IsDiscreteValuationRing.irreducible_iff_uniformizer _).mp (WittVector.irreducible 2)

private theorem base_jets (n : ℕ) :
    Nonempty (EncodingRing allCoords ⧸ maximalIdeal (EncodingRing allCoords) ^ n ≃+*
      EncodingRing evenCoords ⧸ maximalIdeal (EncodingRing evenCoords) ^ n) := by
  cases n with
  | zero =>
    have ha : maximalIdeal (EncodingRing allCoords) ^ 0 = ⊤ := by simp
    have hb : maximalIdeal (EncodingRing evenCoords) ^ 0 = ⊤ := by simp
    exact ⟨(Ideal.quotEquivOfEq ha).trans (RingEquiv.ofUnique.trans (Ideal.quotEquivOfEq hb).symm)⟩
  | succ n =>
    have H := marked_truncations (n + 1)
    unfold twoIdeal at H
    rw [Ideal.span_singleton_pow] at H
    obtain ⟨e, he⟩ := H
    exact ⟨quotientEncodingEquiv (by exact_mod_cast (WittVector.irreducible (k := F) 2).not_isUnit)
      _ (Nat.succ_pos n) e he⟩

private theorem parameter_ne (i : ℕ) : y i ≠ 0 ∧ y i ≠ 1 := by
  let f := incl.comp (algebraMap P K)
  have hf := incl.injective.comp (IsFractionRing.injective P K)
  have hX : (MvPolynomial.X i : P) ≠ 1 := by
    intro h
    have H := congrArg (MvPolynomial.eval (fun _ : ℕ ↦ (0 : ZMod 2))) h
    simp at H
  exact ⟨fun h ↦ MvPolynomial.X_ne_zero i (hf (h.trans (map_zero f).symm)),
    fun h ↦ hX (hf (h.trans (map_one f).symm))⟩

private theorem no_equiv : ¬ Nonempty (EncodingRing allCoords ≃+* EncodingRing evenCoords) := by
  rintro ⟨e⟩
  have hb : evenCoords ≠ 0 := fun h ↦
    (parameter_ne 0).1 (by simpa [evenCoords] using congrArg (fun w : W ↦ w.coeff 0) h)
  have hb' : evenCoords ≠ 1 := fun h ↦
    (parameter_ne 0).2 (by simpa [evenCoords] using congrArg (fun w : W ↦ w.coeff 0) h)
  have hp : Irreducible (2 : W) := by exact_mod_cast (WittVector.irreducible (k := F) 2)
  exact marked_global ⟨redPerm e, redPerm_apply_parameter hp.ne_zero hp.not_isUnit hb hb' e⟩

private def liftQuot {A B : Type*} [CommRing A] [CommRing B] [IsLocalRing A] [IsLocalRing B]
    (e : A ≃+* B) (n : ℕ) : A ⧸ maximalIdeal A ^ n ≃+* B ⧸ maximalIdeal B ^ n :=
  Ideal.quotientEquiv _ _ e (by
    rw [Ideal.map_pow]
    exact congrArg (· ^ n) (map_maximalIdeal_of_surjective e.toRingHom e.surjective).symm)

private theorem complete_of_equiv {C D : Type*} [CommRing C] [CommRing D]
    [IsLocalRing C] [IsLocalRing D] (f : C ≃+* D) (hc : IsAdicComplete (maximalIdeal D) D) :
    IsAdicComplete (maximalIdeal C) C := by
  apply (IsAdicComplete.congr_ringEquiv _ f).mp
  simpa using hc

private theorem refutes.{u, v} : ¬ conjecture.{u, v} := by
  intro h
  let A := ULift.{u} (EncodingRing allCoords)
  let B := ULift.{v} (EncodingRing evenCoords)
  let l : A ≃+* EncodingRing allCoords := ULift.ringEquiv
  let r : B ≃+* EncodingRing evenCoords := ULift.ringEquiv
  let : IsLocalRing A := l.symm.isLocalRing
  let : IsLocalRing B := r.symm.isLocalRing
  let : IsNoetherianRing A := isNoetherianRing_of_ringEquiv (EncodingRing allCoords) l.symm
  let : IsNoetherianRing B := isNoetherianRing_of_ringEquiv (EncodingRing evenCoords) r.symm
  let : IsAdicComplete (maximalIdeal W) W := witt_maximal ▸ WittVector.isAdicCompleteIdealSpanP
  let : IsAdicComplete (maximalIdeal A) A :=
    complete_of_equiv l (isAdicComplete_of_module_finite (𝒪 := W))
  let : IsAdicComplete (maximalIdeal B) B :=
    complete_of_equiv r (isAdicComplete_of_module_finite (𝒪 := W))
  obtain ⟨e⟩ := h A B fun n ↦ (base_jets n).map fun en ↦
    (liftQuot l n).trans (en.trans (liftQuot r n).symm)
  exact no_equiv ⟨l.symm.trans (e.trans r)⟩

/--
**The complete local ring reconstruction conjecture is false.** There exist commutative
Noetherian local rings $A$ and $B$, with maximal ideals $\mathfrak m_A$ and $\mathfrak m_B$, that
are complete and Hausdorff for the $\mathfrak m_A$-adic and $\mathfrak m_B$-adic topologies, such
that $A/\mathfrak m_A^r$ and $B/\mathfrak m_B^r$ are isomorphic as rings for every natural number
$r$, but $A$ and $B$ are not isomorphic as rings.

Van den Dries proves that such rings are isomorphic when the residue field is algebraic over its
prime field, and reports examples by Gabber showing that the answer is no in general.

Source: Lou van den Dries, Isomorphism of complete local noetherian rings and strong
approximation, Proc. Amer. Math. Soc. 136 (2008), 3435-3448,
https://doi.org/10.1090/S0002-9939-08-09401-X. Moved from
`OpenConjectures/Algebra/CompleteLocalRingReconstruction`.
-/
theorem conjecture_refuted : ¬ conjecture := refutes

end MathlibExt.Algebra.CompleteLocalRingReconstructionWanted
