/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Finset.Basic
public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Multiset.Basic
public import Mathlib.SetTheory.Cardinal.Finite
public import MathlibExt.Combinatorics.Enumerative.Partition.Overpartition
public import MathlibExt.NumberTheory.QuadraticForms.ThreeSquares
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Combinatorics.Enumerative.Partition.Basic
import Mathlib.Combinatorics.Enumerative.Partition.GenFun
import Mathlib.Combinatorics.Enumerative.Pentagonal.PowerSeries
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Int.Cast.Lemmas
import Mathlib.Data.Int.Interval
import Mathlib.Data.ZMod.Basic
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.RingTheory.PowerSeries.Expand
import Mathlib.RingTheory.PowerSeries.NoZeroDivisors
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Combinatorics.Enumerative.Pentagonal.EulerFunction
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Analysis.Analytic.OfScalars
import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Analytic.ConvergenceRadius
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import MathlibExt.Analysis.SpecialFunctions.JacobiTripleProduct

section

namespace MetaMathlibExt

open PowerSeries
open scoped PowerSeries.WithPiTopology

/-- Overpartition count: alias for the Wanted left-hand side. -/
private def opcOver (m : ℕ) : Type :=
  { p : Multiset ℕ × Finset ℕ //
    (∀ a ∈ p.1, 0 < a) ∧ p.1.sum = m ∧ ∀ a ∈ p.2, a ∈ p.1 }

-- SupportedMod
private def opcSupportedMod (R : Type*) [CommRing R] (p : ℕ) (r : ZMod p)
    (F : R⟦X⟧) : Prop :=
  ∀ n : ℕ, PowerSeries.coeff n F ≠ 0 → ((n : ℕ) : ZMod p) = r

private theorem opc_supportedMod_mul {R : Type*} [CommRing R] (p : ℕ)
    (r s : ZMod p) (F G : R⟦X⟧) (hF : opcSupportedMod R p r F)
    (hG : opcSupportedMod R p s G) :
    opcSupportedMod R p (r + s) (F * G) := by
  intro n hn
  rw [PowerSeries.coeff_mul] at hn
  obtain ⟨ij, hij, hterm⟩ : ∃ ij ∈ Finset.antidiagonal n,
      PowerSeries.coeff ij.1 F * PowerSeries.coeff ij.2 G ≠ 0 := by
    by_contra h
    push Not at h
    exact hn (Finset.sum_eq_zero h)
  have h1 : PowerSeries.coeff ij.1 F ≠ 0 := left_ne_zero_of_mul hterm
  have h2 : PowerSeries.coeff ij.2 G ≠ 0 := right_ne_zero_of_mul hterm
  have e1 := hF _ h1
  have e2 := hG _ h2
  have hsum : ij.1 + ij.2 = n := Finset.mem_antidiagonal.mp hij
  conv_lhs => rw [← hsum]
  push_cast
  rw [e1, e2]

private theorem opc_supportedMod_add {R : Type*} [CommRing R] (p : ℕ)
    (r : ZMod p) (F G : R⟦X⟧) (hF : opcSupportedMod R p r F)
    (hG : opcSupportedMod R p r G) : opcSupportedMod R p r (F + G) := by
  intro n hn
  have hFG : PowerSeries.coeff n (F + G)
      = PowerSeries.coeff n F + PowerSeries.coeff n G := map_add _ _ _
  rw [hFG] at hn
  by_cases h1 : PowerSeries.coeff n F = 0
  · rw [h1, zero_add] at hn
    exact hG n hn
  · exact hF n h1

private theorem opc_supportedMod_nsmul {R : Type*} [CommRing R] (p : ℕ)
    (r : ZMod p) (F : R⟦X⟧) (k : ℕ) (hF : opcSupportedMod R p r F) :
    opcSupportedMod R p r (k • F) := by
  intro n hn
  have hFG : PowerSeries.coeff n (k • F) = k • PowerSeries.coeff n F :=
    map_nsmul _ _ _
  rw [hFG] at hn
  exact hF n (fun h => hn (by rw [h, nsmul_zero]))

private theorem opc_supportedMod_map {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (p : ℕ) (r : ZMod p) (F : R⟦X⟧)
    (hF : opcSupportedMod R p r F) : opcSupportedMod S p r (PowerSeries.map f F) := by
  intro n hn
  rw [PowerSeries.coeff_map] at hn
  exact hF n (fun h => hn (by rw [h, map_zero]))

private theorem opc_supportedMod_expand {R : Type*} [CommRing R] (p : ℕ)
    (hp : p ≠ 0) (G : R⟦X⟧) : opcSupportedMod R p 0 (PowerSeries.expand p hp G) := by
  have : NeZero p := ⟨hp⟩
  intro n hn
  rw [PowerSeries.coeff_expand] at hn
  by_contra hcon
  have hdvd : p ∣ n := by
    by_contra hnd
    simp [hnd] at hn
  exact hcon ((ZMod.natCast_eq_zero_iff n p).mpr hdvd)

private theorem opc_supportedMod_coeff_eq_zero {R : Type*} [CommRing R]
    (p : ℕ) [NeZero p] (r : ZMod p) (F : R⟦X⟧) (hF : opcSupportedMod R p r F)
    (hr : r ≠ 0) (m : ℕ) : PowerSeries.coeff (p * m) F = 0 := by
  by_contra hne
  exact hr ((hF _ hne).symm.trans
    ((ZMod.natCast_eq_zero_iff (p * m) p).mpr (dvd_mul_right p m)))

private def opcSubsetPowerset (t : Finset ℕ) :
    ↥(t.powerset) ≃ {s : Finset ℕ // s ⊆ t} where
  toFun s := ⟨s.val, Finset.mem_powerset.mp s.property⟩
  invFun s := ⟨s.val, Finset.mem_powerset.mpr s.property⟩
  left_inv s := by obtain ⟨s, h⟩ := s; rfl
  right_inv s := by obtain ⟨s, h⟩ := s; rfl

private theorem opc_card_subset (t : Finset ℕ) :
    Nat.card {s : Finset ℕ // s ⊆ t} = 2 ^ t.card := by
  have hfin : Finite ↥(t.powerset) := Finite.of_fintype _
  rw [← Nat.card_congr (opcSubsetPowerset t), Nat.card_eq_finsetCard,
    Finset.card_powerset]

private def opcOverSigma (m : ℕ) :
    opcOver m ≃ (Σ _π : m.Partition, {s : Finset ℕ // s ⊆ _π.parts.toFinset}) where
  toFun p := ⟨⟨p.val.1, fun {a} ha => p.property.1 a ha, p.property.2.1⟩,
    ⟨p.val.2, fun a ha => Multiset.mem_toFinset.mpr (p.property.2.2 a ha)⟩⟩
  invFun q := ⟨⟨q.1.parts, q.2.val⟩, fun a ha => q.1.parts_pos ha, q.1.parts_sum,
    fun a ha => Multiset.mem_toFinset.mp (q.2.property ha)⟩
  left_inv p := by obtain ⟨⟨M, S⟩, hpos, hsum, hsub⟩ := p; rfl
  right_inv q := by obtain ⟨⟨M, hpos, hsum⟩, ⟨S, hsub⟩⟩ := q; rfl

private theorem opc_overpartition_card_eq_coeff_genFun (m : ℕ) :
    ((Nat.card (opcOver m) : ℕ) : ℤ)
      = (Nat.Partition.genFun (fun _ _ ↦ (2 : ℤ))).coeff m := by
  have hfin : ∀ π : m.Partition,
      Finite {s : Finset ℕ // s ⊆ π.parts.toFinset} :=
    fun π => Finite.of_equiv _ (opcSubsetPowerset _)
  rw [Nat.Partition.coeff_genFun, Nat.card_congr (opcOverSigma m), Nat.card_sigma,
    Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro π _
  rw [opc_card_subset π.parts.toFinset, Nat.cast_pow, Nat.cast_two]
  simp only [Finsupp.prod, Multiset.toFinsupp_support, Finset.prod_const]

/-- Generating series of a weight function: the `k`-th coefficient counts the fiber. -/
private noncomputable def opcWeight {α : Type*} (w : α → ℕ) : ℤ⟦X⟧ :=
  PowerSeries.mk fun k => ((Nat.card {a // w a = k} : ℕ) : ℤ)

private theorem opc_coeff_weight {α : Type*} (w : α → ℕ) (k : ℕ) :
    PowerSeries.coeff k (opcWeight w) = ((Nat.card {a // w a = k} : ℕ) : ℤ) :=
  PowerSeries.coeff_mk _ _

private def opcProdEquiv {α β : Type*} (w₁ : α → ℕ) (w₂ : β → ℕ) (N : ℕ) :
    {p : α × β // w₁ p.1 + w₂ p.2 = N} ≃
      Σ _ij : ↥(Finset.HasAntidiagonal.antidiagonal N),
        ({a : α // w₁ a = _ij.1.1} × {b : β // w₂ b = _ij.1.2}) where
  toFun p :=
    ⟨⟨(w₁ p.val.1, w₂ p.val.2),
      Finset.HasAntidiagonal.mem_antidiagonal.mpr p.property⟩,
      ⟨p.val.1, rfl⟩, ⟨p.val.2, rfl⟩⟩
  invFun q := ⟨(q.2.1.val, q.2.2.val), by
    have ha := q.2.1.property
    have hb := q.2.2.property
    have hm := Finset.HasAntidiagonal.mem_antidiagonal.mp q.1.property
    change w₁ q.2.1.val + w₂ q.2.2.val = N
    rw [ha, hb]
    exact hm⟩
  left_inv p := by obtain ⟨⟨a, b⟩, hp⟩ := p; rfl
  right_inv q := by
    obtain ⟨⟨⟨i, j⟩, hmem⟩, ⟨a, ha⟩, ⟨b, hb⟩⟩ := q
    have e1 : w₁ a = i := ha
    have e2 : w₂ b = j := hb
    subst e1
    subst e2
    rfl

/-- Product of weight series is the weight series of the sum weight. -/
private theorem opc_weight_mul {α β : Type*} (w₁ : α → ℕ) (w₂ : β → ℕ)
    (h₁ : ∀ k, Finite {a // w₁ a = k}) (h₂ : ∀ k, Finite {a // w₂ a = k}) :
    opcWeight (fun p : α × β => w₁ p.1 + w₂ p.2)
      = opcWeight w₁ * opcWeight w₂ := by
  apply PowerSeries.ext
  intro N
  have : ∀ ij : ↥(Finset.HasAntidiagonal.antidiagonal N),
      Fintype {a : α // w₁ a = ij.1.1} := by
    intro ij
    have hfin := h₁ ij.1.1
    exact Fintype.ofFinite _
  have : ∀ ij : ↥(Finset.HasAntidiagonal.antidiagonal N),
      Fintype {b : β // w₂ b = ij.1.2} := by
    intro ij
    have hfin := h₂ ij.1.2
    exact Fintype.ofFinite _
  rw [PowerSeries.coeff_mul]
  simp_rw [opc_coeff_weight]
  rw [Nat.card_congr (opcProdEquiv w₁ w₂ N), Nat.card_sigma, Nat.cast_sum]
  simp_rw [Nat.card_prod, Nat.cast_mul]
  rw [← Finset.sum_coe_sort (s := Finset.HasAntidiagonal.antidiagonal N)]

private def opcSumEquiv {α β : Type*} (w₁ : α → ℕ) (w₂ : β → ℕ) (N : ℕ) :
    {x : α ⊕ β // Sum.elim w₁ w₂ x = N} ≃
      ({a : α // w₁ a = N} ⊕ {b : β // w₂ b = N}) where
  toFun x := match x with
    | ⟨.inl a, h⟩ => .inl ⟨a, h⟩
    | ⟨.inr b, h⟩ => .inr ⟨b, h⟩
  invFun x := match x with
    | .inl ⟨a, h⟩ => ⟨.inl a, h⟩
    | .inr ⟨b, h⟩ => ⟨.inr b, h⟩
  left_inv x := by obtain ⟨x, h⟩ := x; cases x <;> rfl
  right_inv x := by cases x <;> rfl

/-- Sum of weight series is the weight series of the sum-elim weight. -/
private theorem opc_weight_add {α β : Type*} (w₁ : α → ℕ) (w₂ : β → ℕ)
    (h₁ : ∀ k, Finite {a // w₁ a = k}) (h₂ : ∀ k, Finite {a // w₂ a = k}) :
    opcWeight (Sum.elim w₁ w₂) = opcWeight w₁ + opcWeight w₂ := by
  apply PowerSeries.ext
  intro N
  have hF1 : Finite {a : α // w₁ a = N} := h₁ N
  have hF2 : Finite {b : β // w₂ b = N} := h₂ N
  rw [opc_coeff_weight, map_add, opc_coeff_weight, opc_coeff_weight,
    Nat.card_congr (opcSumEquiv w₁ w₂ N), Nat.card_sum, Nat.cast_add]

/-- Weight series is invariant under a weight-preserving equiv. -/
private theorem opc_weight_congr {α β : Type*} (w₁ : α → ℕ) (w₂ : β → ℕ)
    (e : α ≃ β) (h : ∀ a, w₂ (e a) = w₁ a) :
    opcWeight w₁ = opcWeight w₂ := by
  apply PowerSeries.ext
  intro k
  simp_rw [opc_coeff_weight]
  congr 1
  apply Nat.card_congr
  exact Equiv.subtypeEquiv e (fun a => by rw [h a])

/-- Fibers of `x ↦ x.natAbs ^ 2` on `ℤ` are finite. -/
private theorem opc_finite_intFiber (k : ℕ) :
    Finite {x : ℤ // x.natAbs ^ 2 = k} := by
  have hbound : ∀ x : {x : ℤ // x.natAbs ^ 2 = k},
      x.val ∈ Finset.Icc (-((k : ℤ) + 1)) ((k : ℤ) + 1) := by
    intro x
    have hle : x.val.natAbs ≤ x.val.natAbs ^ 2 :=
      Nat.le_self_pow (by norm_num) _
    have hle2 : x.val.natAbs ≤ k := hle.trans_eq x.property
    have habs : |x.val| ≤ ((k : ℤ) + 1) := by
      have h3 : ((x.val.natAbs : ℕ) : ℤ) ≤ ((k : ℤ) + 1) := by
        exact_mod_cast Nat.le_succ_of_le hle2
      rwa [Int.natCast_natAbs] at h3
    rw [Finset.mem_Icc]
    exact abs_le.mp habs
  exact Finite.of_injective
    (fun x : {x : ℤ // x.natAbs ^ 2 = k} =>
      (⟨x.val, hbound x⟩ : ↥(Finset.Icc (-((k : ℤ) + 1)) ((k : ℤ) + 1))))
    (fun a b h => Subtype.ext (by simpa using h))

/-- Fibers of the theta weight on a subtype of `ℤ` are finite. -/
private theorem opc_finite_thetaOnFiber (P : ℤ → Prop) (k : ℕ) :
    Finite {a : {b : ℤ // P b} // a.val.natAbs ^ 2 = k} := by
  have := opc_finite_intFiber k
  exact Finite.of_injective
    (fun x : {a : {b : ℤ // P b} // a.val.natAbs ^ 2 = k} =>
      (⟨x.val.val, x.property⟩ : {x : ℤ // x.natAbs ^ 2 = k}))
    (fun a b h => Subtype.ext (Subtype.ext (by simpa using h)))

/-- Fibers of a sum weight on a product are finite. -/
private theorem opc_finite_prodFiber {α β : Type*} (w₁ : α → ℕ) (w₂ : β → ℕ)
    (h₁ : ∀ k, Finite {a // w₁ a = k}) (h₂ : ∀ k, Finite {a // w₂ a = k})
    (k : ℕ) : Finite {p : α × β // w₁ p.1 + w₂ p.2 = k} := by
  have : ∀ ij : ↥(Finset.HasAntidiagonal.antidiagonal k),
      Fintype {a : α // w₁ a = ij.1.1} := by
    intro ij
    have hfin := h₁ ij.1.1
    exact Fintype.ofFinite _
  have : ∀ ij : ↥(Finset.HasAntidiagonal.antidiagonal k),
      Fintype {b : β // w₂ b = ij.1.2} := by
    intro ij
    have hfin := h₂ ij.1.2
    exact Fintype.ofFinite _
  exact Finite.of_equiv _ (opcProdEquiv w₁ w₂ k).symm

/-- Theta series restricted to a predicate on `ℤ`. -/
private noncomputable def opcThetaOn (P : ℤ → Prop) : ℤ⟦X⟧ :=
  opcWeight (fun x : {x : ℤ // P x} => x.val.natAbs ^ 2)

/-- The theta series `θ = Σ_{x ∈ ℤ} X^{x²}`. -/
private noncomputable def opcTheta : ℤ⟦X⟧ := opcThetaOn (fun _ => True)

/-- Reassociation equiv for the triple product. -/
private def opcReassoc :
    (({_x : ℤ // True} × {_x : ℤ // True}) × {_x : ℤ // True}) ≃ (ℤ × ℤ × ℤ) where
  toFun p := (p.1.1.val, p.1.2.val, p.2.val)
  invFun t := ((⟨t.1, trivial⟩, ⟨t.2.1, trivial⟩), ⟨t.2.2, trivial⟩)
  left_inv p := by obtain ⟨⟨⟨a, _⟩, ⟨b, _⟩⟩, ⟨c, _⟩⟩ := p; rfl
  right_inv t := by obtain ⟨a, b, c⟩ := t; rfl

/-- The natAbs weight agrees with the sum-of-three-squares equation. -/
private theorem opc_natAbs_weight_iff_sq (t : ℤ × ℤ × ℤ) (n : ℕ) :
    (t.1.natAbs ^ 2 + (t.2.1.natAbs ^ 2 + t.2.2.natAbs ^ 2) = n) ↔
    (t.1 ^ 2 + t.2.1 ^ 2 + t.2.2 ^ 2 = (n : ℤ)) := by
  constructor
  · intro h
    have h' : (((t.1.natAbs ^ 2 + (t.2.1.natAbs ^ 2 + t.2.2.natAbs ^ 2) : ℕ)) : ℤ)
        = ((n : ℕ) : ℤ) := by rw [h]
    simp only [Nat.cast_add, Nat.cast_pow, Int.natAbs_sq] at h'
    rw [← add_assoc] at h'
    exact h'
  · intro h
    have h' : (((t.1.natAbs ^ 2 + (t.2.1.natAbs ^ 2 + t.2.2.natAbs ^ 2) : ℕ)) : ℤ)
        = ((n : ℕ) : ℤ) := by
      simp only [Nat.cast_add, Nat.cast_pow, Int.natAbs_sq, ← add_assoc]
      exact h
    exact_mod_cast h'

/-- The `n`-th coefficient of `θ³` counts ordered three-square representations. -/
private theorem opc_coeff_theta_cube (n : ℕ) :
    PowerSeries.coeff n (opcTheta ^ 3)
      = ((Nat.card {x : ℤ × ℤ × ℤ //
          x.1 ^ 2 + x.2.1 ^ 2 + x.2.2 ^ 2 = (n : ℤ)} : ℕ) : ℤ) := by
  have hfin : ∀ k, Finite {x : {x : ℤ // True} // x.val.natAbs ^ 2 = k} :=
    fun k => opc_finite_thetaOnFiber _ k
  have hfin2 : ∀ k, Finite {p : {x : ℤ // True} × {x : ℤ // True} //
      p.1.val.natAbs ^ 2 + p.2.val.natAbs ^ 2 = k} :=
    fun k => opc_finite_prodFiber _ _ hfin hfin k
  have e1 : opcTheta * opcTheta
      = opcWeight (fun p : {x : ℤ // True} × {x : ℤ // True} =>
          p.1.val.natAbs ^ 2 + p.2.val.natAbs ^ 2) :=
    (opc_weight_mul _ _ hfin hfin).symm
  have e2 : (opcWeight (fun p : {x : ℤ // True} × {x : ℤ // True} =>
          p.1.val.natAbs ^ 2 + p.2.val.natAbs ^ 2)) * opcTheta
      = opcWeight (fun p : ({x : ℤ // True} × {x : ℤ // True}) × {x : ℤ // True} =>
          (p.1.1.val.natAbs ^ 2 + p.1.2.val.natAbs ^ 2) + p.2.val.natAbs ^ 2) :=
    (opc_weight_mul _ _ hfin2 hfin).symm
  have e3 : opcWeight (fun p : ({x : ℤ // True} × {x : ℤ // True}) × {x : ℤ // True} =>
          (p.1.1.val.natAbs ^ 2 + p.1.2.val.natAbs ^ 2) + p.2.val.natAbs ^ 2)
      = opcWeight (fun t : ℤ × ℤ × ℤ =>
          t.1.natAbs ^ 2 + (t.2.1.natAbs ^ 2 + t.2.2.natAbs ^ 2)) :=
    opc_weight_congr _ _ opcReassoc (fun p => (add_assoc _ _ _).symm)
  have e4 : ∀ k, ((Nat.card {t : ℤ × ℤ × ℤ //
          t.1.natAbs ^ 2 + (t.2.1.natAbs ^ 2 + t.2.2.natAbs ^ 2) = k} : ℕ) : ℤ)
      = ((Nat.card {x : ℤ × ℤ × ℤ //
          x.1 ^ 2 + x.2.1 ^ 2 + x.2.2 ^ 2 = (k : ℤ)} : ℕ) : ℤ) := by
    intro k
    apply congrArg
    apply Nat.card_congr
    exact Equiv.subtypeEquiv (Equiv.refl _) (fun t => opc_natAbs_weight_iff_sq t k)
  rw [show (3 : ℕ) = 2 + 1 from rfl, pow_succ, pow_two, e1, e2, e3,
    opc_coeff_weight]
  exact e4 n

private theorem opc_genFun_two_mul_pentagonalSeries_sq :
    Nat.Partition.genFun (fun _ _ ↦ (2 : ℤ)) * (PowerSeries.pentagonalSeries ℤ) ^ 2
      = PowerSeries.expand 2 two_ne_zero (PowerSeries.pentagonalSeries ℤ) := by
  have hP : HasProd
      (fun i : ℕ ↦ 1 + ∑' j : ℕ, (2 : ℤ) • (X ^ ((i + 1) * (j + 1)) : ℤ⟦X⟧))
      (Nat.Partition.genFun (fun _ _ ↦ (2 : ℤ))) :=
    Nat.Partition.hasProd_genFun (fun _ _ ↦ (2 : ℤ))
  have hE : HasProd (fun n : ℕ ↦ (1 - X ^ (n + 1) : ℤ⟦X⟧))
      (PowerSeries.pentagonalSeries ℤ) :=
    PowerSeries.WithPiTopology.hasProd_one_sub_X_pow ℤ
  have hPE := (hP.mul hE).mul hE
  have hfactor : ∀ i : ℕ, (1 + ∑' j : ℕ, (2 : ℤ) • (X ^ ((i + 1) * (j + 1)) : ℤ⟦X⟧))
      * (1 - (X ^ (i + 1) : ℤ⟦X⟧)) * (1 - (X ^ (i + 1) : ℤ⟦X⟧))
      = 1 - (X ^ (2 * (i + 1)) : ℤ⟦X⟧) := by
    intro i
    have hconst : (X ^ (i + 1) : ℤ⟦X⟧).constantCoeff = 0 := by
      rw [← PowerSeries.coeff_zero_eq_constantCoeff, PowerSeries.coeff_X_pow]
      simp
    have hS : (∑' j : ℕ, (X ^ (i + 1) : ℤ⟦X⟧) ^ j) * (1 - X ^ (i + 1)) = 1 :=
      PowerSeries.WithPiTopology.tsum_pow_mul_one_sub_of_constantCoeff_eq_zero
        hconst
    have hsumY : Summable (fun j : ℕ => (X ^ (i + 1) : ℤ⟦X⟧) ^ j) :=
      PowerSeries.WithPiTopology.summable_pow_of_constantCoeff_eq_zero hconst
    have hterm : ∀ j : ℕ, (2 : ℤ) • (X ^ ((i + 1) * (j + 1)) : ℤ⟦X⟧)
        = (PowerSeries.C 2 * X ^ (i + 1)) * (X ^ (i + 1) : ℤ⟦X⟧) ^ j := by
      intro j
      have e1 : (2 : ℤ) • (X ^ ((i + 1) * (j + 1)) : ℤ⟦X⟧)
          = PowerSeries.C 2 * X ^ ((i + 1) * (j + 1)) :=
        PowerSeries.smul_eq_C_mul _ _
      rw [e1, pow_mul, pow_succ', mul_assoc]
    have hA : (∑' j : ℕ, (2 : ℤ) • (X ^ ((i + 1) * (j + 1)) : ℤ⟦X⟧))
        = (PowerSeries.C 2 * X ^ (i + 1))
          * (∑' j : ℕ, (X ^ (i + 1) : ℤ⟦X⟧) ^ j) := by
      rw [tsum_congr hterm]
      exact hsumY.tsum_mul_left _
    have hC2 : (PowerSeries.C (2 : ℤ) : ℤ⟦X⟧) = 2 := by simp
    have hY2 : (X ^ (2 * (i + 1) : ℕ) : ℤ⟦X⟧) = (X ^ (i + 1) : ℤ⟦X⟧) ^ 2 := by
      rw [show 2 * (i + 1) = (i + 1) * 2 from by ring, pow_mul]
    have h1 : (1 + (2 : ℤ⟦X⟧) * X ^ (i + 1)
          * (∑' j : ℕ, (X ^ (i + 1) : ℤ⟦X⟧) ^ j)) * (1 - X ^ (i + 1))
        = 1 + X ^ (i + 1) := by
      have e : (1 + (2 : ℤ⟦X⟧) * X ^ (i + 1)
            * (∑' j : ℕ, (X ^ (i + 1) : ℤ⟦X⟧) ^ j)) * (1 - X ^ (i + 1))
          = (1 - X ^ (i + 1)) + (2 : ℤ⟦X⟧) * X ^ (i + 1)
            * ((∑' j : ℕ, (X ^ (i + 1) : ℤ⟦X⟧) ^ j) * (1 - X ^ (i + 1))) := by
        ring
      rw [e, hS]
      ring
    rw [hA, hC2, h1, hY2]
    ring
  have hPE' : HasProd (fun n : ℕ ↦ (1 - X ^ (2 * (n + 1)) : ℤ⟦X⟧))
      ((Nat.Partition.genFun (fun _ _ ↦ (2 : ℤ)) * PowerSeries.pentagonalSeries ℤ)
        * PowerSeries.pentagonalSeries ℤ) :=
    hPE.congr_fun (fun i => (hfactor i).symm)
  have hprod : ∀ s : Finset ℕ, (∏ n ∈ s, (1 - X ^ (2 * (n + 1)) : ℤ⟦X⟧))
      = PowerSeries.expand 2 two_ne_zero
        (∏ n ∈ s, (1 - X ^ (n + 1) : ℤ⟦X⟧)) := by
    intro s
    rw [map_prod]
    apply Finset.prod_congr rfl
    intro n _
    rw [map_sub, map_one, map_pow, PowerSeries.expand_X, ← pow_mul]
  have hexp : HasProd (fun n : ℕ ↦ (1 - X ^ (2 * (n + 1)) : ℤ⟦X⟧))
      (PowerSeries.expand 2 two_ne_zero (PowerSeries.pentagonalSeries ℤ)) := by
    rw [HasProd, PowerSeries.WithPiTopology.tendsto_iff_coeff_tendsto]
    intro d
    apply tendsto_nhds_of_eventually_eq
    by_cases hd : 2 ∣ d
    · obtain ⟨m, rfl⟩ := hd
      have e1 : ∀ s : Finset ℕ, (∏ n ∈ s, (1 - X ^ (2 * (n + 1)) : ℤ⟦X⟧)).coeff
          (2 * m) = (∏ n ∈ s, (1 - X ^ (n + 1) : ℤ⟦X⟧)).coeff m := by
        intro s
        rw [hprod s, PowerSeries.coeff_expand_mul]
      have e2 : (PowerSeries.expand 2 two_ne_zero
          (PowerSeries.pentagonalSeries ℤ)).coeff (2 * m)
          = (PowerSeries.pentagonalSeries ℤ).coeff m :=
        PowerSeries.coeff_expand_mul _ _ _ _
      simp only [e1, e2]
      exact PowerSeries.coeff_prod_one_sub_X_pow_eventually_eq _ _
    · apply Filter.Eventually.of_forall
      intro s
      rw [hprod s, PowerSeries.coeff_expand_of_not_dvd _ _ _ hd,
        PowerSeries.coeff_expand_of_not_dvd _ _ _ hd]
  have hunique := HasProd.unique hPE' hexp
  rw [pow_two, ← hunique]
  exact (mul_assoc _ _ _).symm

private noncomputable def opcA : ℤ⟦X⟧ := opcThetaOn (fun x => x % 5 = 0)
private noncomputable def opcB : ℤ⟦X⟧ :=
  opcThetaOn (fun x => x % 5 = 1 ∨ x % 5 = 4)
private noncomputable def opcC : ℤ⟦X⟧ :=
  opcThetaOn (fun x => x % 5 = 2 ∨ x % 5 = 3)

private theorem opc_support_thetaOn (P : ℤ → Prop) (r : ZMod 5)
    (hP : ∀ x : ℤ, P x → ((x ^ 2 : ℤ) : ZMod 5) = r) :
    opcSupportedMod ℤ 5 r (opcThetaOn P) := by
  intro m hm
  have hcoeff : PowerSeries.coeff m (opcThetaOn P)
      = ((Nat.card {a : {b : ℤ // P b} // a.val.natAbs ^ 2 = m} : ℕ) : ℤ) :=
    opc_coeff_weight (fun x : {x : ℤ // P x} => x.val.natAbs ^ 2) m
  rw [hcoeff] at hm
  have hfin := opc_finite_thetaOnFiber P m
  have hFT : Fintype {a : {b : ℤ // P b} // a.val.natAbs ^ 2 = m} :=
    Fintype.ofFinite _
  have hpos : 0 < Nat.card {a : {b : ℤ // P b} // a.val.natAbs ^ 2 = m} :=
    Nat.pos_of_ne_zero (by exact_mod_cast hm)
  rw [Nat.card_eq_fintype_card, Fintype.card_pos_iff] at hpos
  obtain ⟨⟨x, hxP⟩, hx⟩ := hpos
  have hmx : x ^ 2 = (((m : ℕ)) : ℤ) := by
    have hx' : (((x.natAbs ^ 2 : ℕ)) : ℤ) = (((m : ℕ)) : ℤ) := by rw [hx]
    rwa [Nat.cast_pow, Int.natAbs_sq] at hx'
  have hr := hP x hxP
  rw [hmx] at hr
  rwa [Int.cast_natCast] at hr

private theorem opc_intCast_residue (x r : ℤ) (h : x % 5 = r) :
    ((x : ℤ) : ZMod 5) = ((r : ℤ) : ZMod 5) := by
  have h5 : (5 : ZMod 5) = 0 := by decide
  have hxx : x = 5 * (x / 5) + r := by omega
  rw [hxx]
  push_cast
  rw [h5, zero_mul, zero_add]

private theorem opc_supportA : opcSupportedMod ℤ 5 0 opcA := by
  apply opc_support_thetaOn
  intro x h0
  have h0' : x % 5 = 0 := h0
  have hx0 : ((x : ℤ) : ZMod 5) = 0 := by
    have h := opc_intCast_residue x 0 h0'
    rwa [Int.cast_zero] at h
  have hsq : (((x ^ 2 : ℤ)) : ZMod 5) = (((x : ℤ)) : ZMod 5) ^ 2 := by
    push_cast
    ring
  rw [hsq, hx0]
  simp

private theorem opc_supportB : opcSupportedMod ℤ 5 1 opcB := by
  apply opc_support_thetaOn
  intro x hx
  have hx' : x % 5 = 1 ∨ x % 5 = 4 := hx
  have hsq : (((x ^ 2 : ℤ)) : ZMod 5) = (((x : ℤ)) : ZMod 5) ^ 2 := by
    push_cast
    ring
  rcases hx' with h1 | h4
  · have hx1 : ((x : ℤ) : ZMod 5) = 1 := by
      have h := opc_intCast_residue x 1 h1
      rwa [Int.cast_one] at h
    rw [hsq, hx1, one_pow]
  · have hx4 : ((x : ℤ) : ZMod 5) = ((4 : ℤ) : ZMod 5) :=
      opc_intCast_residue x 4 h4
    rw [hsq, hx4]
    decide

private theorem opc_supportC : opcSupportedMod ℤ 5 4 opcC := by
  apply opc_support_thetaOn
  intro x hx
  have hx' : x % 5 = 2 ∨ x % 5 = 3 := hx
  have hsq : (((x ^ 2 : ℤ)) : ZMod 5) = (((x : ℤ)) : ZMod 5) ^ 2 := by
    push_cast
    ring
  rcases hx' with h2 | h3
  · have hx2 : ((x : ℤ) : ZMod 5) = ((2 : ℤ) : ZMod 5) :=
      opc_intCast_residue x 2 h2
    rw [hsq, hx2]
    decide
  · have hx3 : ((x : ℤ) : ZMod 5) = ((3 : ℤ) : ZMod 5) :=
      opc_intCast_residue x 3 h3
    rw [hsq, hx3]
    decide

private def opcSplitFwd
    (p : ((({x : ℤ // x % 5 = 0} ⊕ {x : ℤ // x % 5 = 1 ∨ x % 5 = 4})
    ⊕ {x : ℤ // x % 5 = 2 ∨ x % 5 = 3}))) : {_x : ℤ // True} :=
  match p with
  | .inl (.inl ⟨x, _⟩) => ⟨x, trivial⟩
  | .inl (.inr ⟨x, _⟩) => ⟨x, trivial⟩
  | .inr ⟨x, _⟩ => ⟨x, trivial⟩

private def opcSplitBwd (t : {_x : ℤ // True}) :
    ((({x : ℤ // x % 5 = 0} ⊕ {x : ℤ // x % 5 = 1 ∨ x % 5 = 4})
    ⊕ {x : ℤ // x % 5 = 2 ∨ x % 5 = 3})) :=
  if h0 : t.val % 5 = 0 then .inl (.inl ⟨t.val, h0⟩)
  else if h1 : t.val % 5 = 1 ∨ t.val % 5 = 4 then .inl (.inr ⟨t.val, h1⟩)
  else .inr ⟨t.val, by omega⟩

private theorem opcSplit_fwd_bwd (t : {_x : ℤ // True}) :
    opcSplitFwd (opcSplitBwd t) = t := by
  obtain ⟨x, _⟩ := t
  by_cases h0 : x % 5 = 0
  · simp [h0, opcSplitBwd, opcSplitFwd]
  · by_cases h1 : x % 5 = 1 ∨ x % 5 = 4
    · simp [h0, h1, opcSplitBwd, opcSplitFwd]
    · simp [h0, h1, opcSplitBwd, opcSplitFwd]

private theorem opcSplit_bwd_fwd
    (p : ((({x : ℤ // x % 5 = 0} ⊕ {x : ℤ // x % 5 = 1 ∨ x % 5 = 4})
    ⊕ {x : ℤ // x % 5 = 2 ∨ x % 5 = 3}))) :
    opcSplitBwd (opcSplitFwd p) = p := by
  match p with
  | .inl (.inl ⟨x, h0⟩) => simp [h0, opcSplitBwd, opcSplitFwd]
  | .inl (.inr ⟨x, h1⟩) =>
    have hn0 : ¬ x % 5 = 0 := by omega
    simp [hn0, h1, opcSplitBwd, opcSplitFwd]
  | .inr ⟨x, h2⟩ =>
    have hn0 : ¬ x % 5 = 0 := by omega
    have hn1 : ¬ (x % 5 = 1 ∨ x % 5 = 4) := by omega
    simp [hn0, hn1, opcSplitBwd, opcSplitFwd]

private def opcSplit :
    ((({x : ℤ // x % 5 = 0} ⊕ {x : ℤ // x % 5 = 1 ∨ x % 5 = 4})
    ⊕ {x : ℤ // x % 5 = 2 ∨ x % 5 = 3})) ≃ {_x : ℤ // True} where
  toFun := opcSplitFwd
  invFun := opcSplitBwd
  left_inv := opcSplit_bwd_fwd
  right_inv := opcSplit_fwd_bwd

private theorem opc_finite_sumFiber {α β : Type*} (w₁ : α → ℕ) (w₂ : β → ℕ)
    (h₁ : ∀ k, Finite {a // w₁ a = k}) (h₂ : ∀ k, Finite {a // w₂ a = k})
    (k : ℕ) : Finite {x : α ⊕ β // Sum.elim w₁ w₂ x = k} := by
  have hf1 := h₁ k
  have hf2 := h₂ k
  have hF1 : Fintype {a : α // w₁ a = k} := Fintype.ofFinite _
  have hF2 : Fintype {b : β // w₂ b = k} := Fintype.ofFinite _
  have hFS : Fintype ({a : α // w₁ a = k} ⊕ {b : β // w₂ b = k}) := inferInstance
  have hFinS : Finite ({a : α // w₁ a = k} ⊕ {b : β // w₂ b = k}) :=
    Finite.of_fintype _
  exact @Finite.of_equiv _ _ hFinS (opcSumEquiv w₁ w₂ k).symm

private theorem opc_theta_eq_dissection : opcTheta = opcA + opcB + opcC := by
  have hfinA : ∀ k, Finite
      {x : {x : ℤ // x % 5 = 0} // x.val.natAbs ^ 2 = k} :=
    fun k => opc_finite_thetaOnFiber _ k
  have hfinB : ∀ k, Finite
      {x : {x : ℤ // x % 5 = 1 ∨ x % 5 = 4} // x.val.natAbs ^ 2 = k} :=
    fun k => opc_finite_thetaOnFiber _ k
  have hfinC : ∀ k, Finite
      {x : {x : ℤ // x % 5 = 2 ∨ x % 5 = 3} // x.val.natAbs ^ 2 = k} :=
    fun k => opc_finite_thetaOnFiber _ k
  have hfinAB : ∀ k, Finite {x : ({x : ℤ // x % 5 = 0}
        ⊕ {x : ℤ // x % 5 = 1 ∨ x % 5 = 4}) //
      Sum.elim (fun x : {x : ℤ // x % 5 = 0} => x.val.natAbs ^ 2)
        (fun x : {x : ℤ // x % 5 = 1 ∨ x % 5 = 4} => x.val.natAbs ^ 2) x = k} :=
    fun k => opc_finite_sumFiber _ _ hfinA hfinB k
  change opcWeight (fun x : {x : ℤ // True} => x.val.natAbs ^ 2)
      = opcWeight (fun x : {x : ℤ // x % 5 = 0} => x.val.natAbs ^ 2)
      + opcWeight (fun x : {x : ℤ // x % 5 = 1 ∨ x % 5 = 4} => x.val.natAbs ^ 2)
      + opcWeight (fun x : {x : ℤ // x % 5 = 2 ∨ x % 5 = 3} => x.val.natAbs ^ 2)
  rw [← opc_weight_add _ _ hfinA hfinB, ← opc_weight_add _ _ hfinAB hfinC]
  symm
  exact opc_weight_congr _ _ opcSplit (fun p => by
    match p with
    | .inl (.inl ⟨x, _⟩) => rfl
    | .inl (.inr ⟨x, _⟩) => rfl
    | .inr ⟨x, _⟩ => rfl)

private def opcSq (P Q : ℤ → Prop) (N : ℕ) : Type :=
  {t : ℤ × ℤ // P t.1 ∧ Q t.2 ∧ t.1 ^ 2 + t.2 ^ 2 = (((N : ℕ)) : ℤ)}

private def opcFiberSqEquiv (P Q : ℤ → Prop) (N : ℕ) :
    {p : {x : ℤ // P x} × {x : ℤ // Q x} //
      p.1.val.natAbs ^ 2 + p.2.val.natAbs ^ 2 = N} ≃ opcSq P Q N where
  toFun p := by
    obtain ⟨⟨⟨x, hx⟩, ⟨y, hy⟩⟩, h⟩ := p
    exact ⟨(x, y), hx, hy, by
      have h' : ((((x.natAbs ^ 2 + y.natAbs ^ 2 : ℕ))) : ℤ)
          = (((N : ℕ)) : ℤ) := by rw [h]
      simp only [Nat.cast_add, Nat.cast_pow, Int.natAbs_sq] at h'
      exact h'⟩
  invFun t := by
    obtain ⟨⟨x, y⟩, hx, hy, h⟩ := t
    exact ⟨⟨⟨x, hx⟩, ⟨y, hy⟩⟩, by
      have h' : ((((x.natAbs ^ 2 + y.natAbs ^ 2 : ℕ))) : ℤ)
          = (((N : ℕ)) : ℤ) := by
        simp only [Nat.cast_add, Nat.cast_pow, Int.natAbs_sq]
        exact h
      exact_mod_cast h'⟩
  left_inv p := by obtain ⟨⟨⟨x, _⟩, ⟨y, _⟩⟩, _⟩ := p; rfl
  right_inv t := by obtain ⟨⟨x, y⟩, _, _, _⟩ := t; rfl

private theorem opc_coeff_mul_thetaOn (P Q : ℤ → Prop) (N : ℕ) :
    PowerSeries.coeff N (opcThetaOn P * opcThetaOn Q)
      = ((Nat.card (opcSq P Q N) : ℕ) : ℤ) := by
  have hfinP : ∀ k, Finite {x : {x : ℤ // P x} // x.val.natAbs ^ 2 = k} :=
    fun k => opc_finite_thetaOnFiber _ k
  have hfinQ : ∀ k, Finite {x : {x : ℤ // Q x} // x.val.natAbs ^ 2 = k} :=
    fun k => opc_finite_thetaOnFiber _ k
  have e : opcThetaOn P * opcThetaOn Q
      = opcWeight (fun p : {x : ℤ // P x} × {x : ℤ // Q x} =>
          p.1.val.natAbs ^ 2 + p.2.val.natAbs ^ 2) :=
    (opc_weight_mul _ _ hfinP hfinQ).symm
  rw [e]
  simp only [opc_coeff_weight]
  rw [Nat.card_congr (opcFiberSqEquiv P Q N)]

private theorem opc_sq_zero (x : ℤ) (h : x % 5 = 0) :
    ((((x ^ 2 : ℤ))) : ZMod 5) = 0 := by
  have hx0 : ((x : ℤ) : ZMod 5) = 0 := by
    have hh := opc_intCast_residue x 0 h
    rwa [Int.cast_zero] at hh
  have hsq : ((((x ^ 2 : ℤ))) : ZMod 5) = (((x : ℤ)) : ZMod 5) ^ 2 := by
    push_cast
    ring
  rw [hsq, hx0]
  simp

private theorem opc_sq_one (x : ℤ) (h : x % 5 = 1 ∨ x % 5 = 4) :
    ((((x ^ 2 : ℤ))) : ZMod 5) = 1 := by
  have hsq : ((((x ^ 2 : ℤ))) : ZMod 5) = (((x : ℤ)) : ZMod 5) ^ 2 := by
    push_cast
    ring
  rcases h with h1 | h4
  · have hx1 : ((x : ℤ) : ZMod 5) = 1 := by
      have hh := opc_intCast_residue x 1 h1
      rwa [Int.cast_one] at hh
    rw [hsq, hx1, one_pow]
  · have hx4 : ((x : ℤ) : ZMod 5) = ((4 : ℤ) : ZMod 5) :=
      opc_intCast_residue x 4 h4
    rw [hsq, hx4]
    decide

private theorem opc_sq_four (x : ℤ) (h : x % 5 = 2 ∨ x % 5 = 3) :
    ((((x ^ 2 : ℤ))) : ZMod 5) = 4 := by
  have hsq : ((((x ^ 2 : ℤ))) : ZMod 5) = (((x : ℤ)) : ZMod 5) ^ 2 := by
    push_cast
    ring
  rcases h with h2 | h3
  · have hx2 : ((x : ℤ) : ZMod 5) = ((2 : ℤ) : ZMod 5) :=
      opc_intCast_residue x 2 h2
    rw [hsq, hx2]
    decide
  · have hx3 : ((x : ℤ) : ZMod 5) = ((3 : ℤ) : ZMod 5) :=
      opc_intCast_residue x 3 h3
    rw [hsq, hx3]
    decide

private theorem opc_dvd_of_sq (x y : ℤ) (N : ℕ)
    (h0 : ((((x ^ 2 + y ^ 2 : ℤ))) : ZMod 5) = 0)
    (heq : x ^ 2 + y ^ 2 = (((N : ℕ)) : ℤ)) : (5 : ℕ) ∣ N := by
  have e1 : (((((N : ℕ))) : ℤ) : ZMod 5) = ((((x ^ 2 + y ^ 2 : ℤ))) : ZMod 5) := by
    rw [← heq]
  have e : (((N : ℕ)) : ZMod 5) = 0 := e1.trans h0
  exact (ZMod.natCast_eq_zero_iff N 5).mp e

private theorem opc_card_sq_eq_zero (P Q : ℤ → Prop) (N : ℕ)
    (hPQ : ∀ x y : ℤ, P x → Q y → ((((x ^ 2 + y ^ 2 : ℤ))) : ZMod 5) = 0)
    (hd : ¬ (5 : ℕ) ∣ N) : Nat.card (opcSq P Q N) = 0 := by
  rw [Nat.card_eq_zero]
  exact Or.inl ⟨fun t => by
    obtain ⟨⟨x, y⟩, hP, hQ, heq⟩ := t
    exact hd (opc_dvd_of_sq x y N (hPQ x y hP hQ) heq)⟩

private theorem opc_finite_sqFiber (P Q : ℤ → Prop) (N : ℕ) :
    Finite (opcSq P Q N) := by
  have hfinP : ∀ k, Finite {x : {x : ℤ // P x} // x.val.natAbs ^ 2 = k} :=
    fun k => opc_finite_thetaOnFiber _ k
  have hfinQ : ∀ k, Finite {x : {x : ℤ // Q x} // x.val.natAbs ^ 2 = k} :=
    fun k => opc_finite_thetaOnFiber _ k
  have hfin : Finite {p : {x : ℤ // P x} × {x : ℤ // Q x} //
      p.1.val.natAbs ^ 2 + p.2.val.natAbs ^ 2 = N} :=
    opc_finite_prodFiber _ _ hfinP hfinQ N
  exact @Finite.of_equiv _ _ hfin (opcFiberSqEquiv P Q N)

private theorem opc_dvd_add (x y : ℤ)
    (hmod : ((x : ZMod 5)) = 3 * ((y : ZMod 5))) : (5 : ℤ) ∣ x + 2 * y := by
  have h5 : (5 : ZMod 5) = 0 := by decide
  have e : ((((x + 2 * y : ℤ))) : ZMod 5) = 0 := by
    have e1 : ((((x + 2 * y : ℤ))) : ZMod 5)
        = ((x : ZMod 5)) + 2 * ((y : ZMod 5)) := by push_cast; ring
    have e2 : (3 : ZMod 5) * ((y : ZMod 5)) + 2 * ((y : ZMod 5))
        = 5 * ((y : ZMod 5)) := by ring
    rw [e1, hmod, e2, h5, zero_mul]
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp e

private theorem opc_dvd_sub (x y : ℤ)
    (hmod : ((x : ZMod 5)) = 3 * ((y : ZMod 5))) : (5 : ℤ) ∣ 2 * x - y := by
  have h5 : (5 : ZMod 5) = 0 := by decide
  have e : ((((2 * x - y : ℤ))) : ZMod 5) = 0 := by
    have e1 : ((((2 * x - y : ℤ))) : ZMod 5)
        = 2 * ((x : ZMod 5)) - ((y : ZMod 5)) := by push_cast; ring
    have e2 : 2 * ((3 : ZMod 5) * ((y : ZMod 5))) - ((y : ZMod 5))
        = 5 * ((y : ZMod 5)) := by ring
    rw [e1, hmod, e2, h5, zero_mul]
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp e

private def opcT (M : ℕ) : Type :=
  {t : ℤ × ℤ // t.1 ^ 2 + t.2 ^ 2 = ((((5 * M : ℕ))) : ℤ) ∧
    ((t.1 : ℤ) : ZMod 5) = 3 * ((t.2 : ℤ) : ZMod 5)}

private def opcPhi (M : ℕ) :
    opcSq (fun _ => True) (fun _ => True) M ≃ opcT M where
  toFun s := by
    obtain ⟨⟨u, v⟩, _, _, h⟩ := s
    exact ⟨(u + 2 * v, 2 * u - v), by
      have e : (u + 2 * v) ^ 2 + (2 * u - v) ^ 2 = 5 * (u ^ 2 + v ^ 2) := by
        ring
      have eM : ((((5 * M : ℕ))) : ℤ) = 5 * ((((M : ℕ))) : ℤ) := by
        push_cast
        ring
      rw [e, h, eM], by
        have e0 : ((((u + 2 * v) - 3 * (2 * u - v) : ℤ)) : ZMod 5) = 0 := by
          rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
          exact ⟨v - u, by push_cast; ring⟩
        have e1 : ((((u + 2 * v) - 3 * (2 * u - v) : ℤ)) : ZMod 5)
            = ((((u + 2 * v : ℤ))) : ZMod 5)
              - 3 * ((((2 * u - v : ℤ))) : ZMod 5) := by push_cast; ring
        rw [e1] at e0
        exact sub_eq_zero.mp e0⟩
  invFun t := by
    obtain ⟨⟨x, y⟩, heq, hmod⟩ := t
    have d1 : (5 : ℤ) ∣ x + 2 * y := opc_dvd_add x y hmod
    have d2 : (5 : ℤ) ∣ 2 * x - y := opc_dvd_sub x y hmod
    refine ⟨((x + 2 * y) / 5, (2 * x - y) / 5), trivial, trivial, ?_⟩
    have hu : 5 * ((x + 2 * y) / 5) = x + 2 * y := Int.mul_ediv_cancel' d1
    have hv : 5 * ((2 * x - y) / 5) = 2 * x - y := Int.mul_ediv_cancel' d2
    have key : 25 * ((((x + 2 * y) / 5) ^ 2 + ((2 * x - y) / 5) ^ 2 : ℤ))
        = 25 * ((((M : ℕ))) : ℤ) := by
      have e2 : 25 * ((((x + 2 * y) / 5) ^ 2 + ((2 * x - y) / 5) ^ 2 : ℤ))
          = (5 * ((x + 2 * y) / 5)) ^ 2 + (5 * ((2 * x - y) / 5)) ^ 2 := by
        ring
      have e3 : (5 * ((x + 2 * y) / 5)) ^ 2 + (5 * ((2 * x - y) / 5)) ^ 2
          = 5 * (x ^ 2 + y ^ 2) := by rw [hu, hv]; ring
      have eM : ((((5 * M : ℕ))) : ℤ) = 5 * ((((M : ℕ))) : ℤ) := by
        push_cast
        ring
      rw [e2, e3, heq, eM]
      ring
    have hfin : ((((x + 2 * y) / 5) ^ 2 + ((2 * x - y) / 5) ^ 2 : ℤ))
        = ((((M : ℕ))) : ℤ) :=
      mul_left_cancel₀ (show (25 : ℤ) ≠ 0 by norm_num) key
    exact hfin
  left_inv s := by
    obtain ⟨⟨u, v⟩, _, _, h⟩ := s
    apply Subtype.ext
    change ((u + 2 * v + 2 * (2 * u - v)) / 5, (2 * (u + 2 * v) - (2 * u - v)) / 5)
      = (u, v)
    have e1 : u + 2 * v + 2 * (2 * u - v) = 5 * u := by ring
    have e2 : 2 * (u + 2 * v) - (2 * u - v) = 5 * v := by ring
    rw [e1, e2]
    congr 1
    · have hd : (5 : ℤ) ∣ 5 * u := dvd_mul_right _ _
      have hh := Int.mul_ediv_cancel' hd
      exact mul_left_cancel₀ (show (5 : ℤ) ≠ 0 by norm_num) hh
    · have hd : (5 : ℤ) ∣ 5 * v := dvd_mul_right _ _
      have hh := Int.mul_ediv_cancel' hd
      exact mul_left_cancel₀ (show (5 : ℤ) ≠ 0 by norm_num) hh
  right_inv t := by
    obtain ⟨⟨x, y⟩, heq, hmod⟩ := t
    have d1 : (5 : ℤ) ∣ x + 2 * y := opc_dvd_add x y hmod
    have d2 : (5 : ℤ) ∣ 2 * x - y := opc_dvd_sub x y hmod
    have hu : 5 * ((x + 2 * y) / 5) = x + 2 * y := Int.mul_ediv_cancel' d1
    have hv : 5 * ((2 * x - y) / 5) = 2 * x - y := Int.mul_ediv_cancel' d2
    apply Subtype.ext
    change (((x + 2 * y) / 5 + 2 * ((2 * x - y) / 5)),
        (2 * ((x + 2 * y) / 5) - ((2 * x - y) / 5))) = (x, y)
    congr 1
    · have h5 : 5 * ((((x + 2 * y) / 5) + 2 * (((2 * x - y) / 5)) : ℤ))
          = 5 * x := by
        have e : 5 * ((((x + 2 * y) / 5) + 2 * (((2 * x - y) / 5)) : ℤ))
            = (5 * ((x + 2 * y) / 5)) + 2 * (5 * ((2 * x - y) / 5)) := by ring
        rw [e, hu, hv]
        ring
      exact mul_left_cancel₀ (show (5 : ℤ) ≠ 0 by norm_num) h5
    · have h5 : 5 * ((2 * (((x + 2 * y) / 5)) - (((2 * x - y) / 5)) : ℤ))
          = 5 * y := by
        have e : 5 * ((2 * (((x + 2 * y) / 5)) - (((2 * x - y) / 5)) : ℤ))
            = 2 * (5 * ((x + 2 * y) / 5)) - (5 * ((2 * x - y) / 5)) := by ring
        rw [e, hu, hv]
        ring
      exact mul_left_cancel₀ (show (5 : ℤ) ≠ 0 by norm_num) h5

-- Continued: the two-square dissection identity.

/-- In `ZMod 5`, squares equal to `1` come from `±1`. -/
private theorem opc_sq_eq_one_iff :
    ∀ a : ZMod 5, a ^ 2 = 1 ↔ a = 1 ∨ a = 4 := by
  decide

/-- In `ZMod 5`, squares equal to `4` come from `±2`. -/
private theorem opc_sq_eq_four_iff :
    ∀ a : ZMod 5, a ^ 2 = 4 ↔ a = 2 ∨ a = 3 := by
  decide

/-- Integer residues with square `1` mod 5 are `±1`. -/
private theorem opc_mem_pm1 (x : ℤ) (h : ((x : ZMod 5)) ^ 2 = 1) :
    x % 5 = 1 ∨ x % 5 = 4 := by
  have hx : ((x : ZMod 5)) = ((((x % 5 : ℤ))) : ZMod 5) :=
    opc_intCast_residue x _ rfl
  have h' : ((((x % 5 : ℤ))) : ZMod 5) ^ 2 = 1 := by rw [← hx]; exact h
  have hmem := (opc_sq_eq_one_iff _).mp h'
  rcases hmem with h1 | h4
  · have hd : (5 : ℤ) ∣ x % 5 - 1 := by
      have e : ((((x % 5 - 1 : ℤ))) : ZMod 5) = 0 := by
        have e1 : ((((x % 5 - 1 : ℤ))) : ZMod 5)
            = ((((x % 5 : ℤ))) : ZMod 5) - 1 := by push_cast; ring
        rw [e1, h1, sub_self]
      exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp e
    exact Or.inl (by omega)
  · have hd : (5 : ℤ) ∣ x % 5 - 4 := by
      have e : ((((x % 5 - 4 : ℤ))) : ZMod 5) = 0 := by
        have e1 : ((((x % 5 - 4 : ℤ))) : ZMod 5)
            = ((((x % 5 : ℤ))) : ZMod 5) - 4 := by push_cast; ring
        rw [e1, h4, sub_self]
      exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp e
    exact Or.inr (by omega)

/-- Integer residues with square `4` mod 5 are `±2`. -/
private theorem opc_mem_pm2 (y : ℤ) (h : ((y : ZMod 5)) ^ 2 = 4) :
    y % 5 = 2 ∨ y % 5 = 3 := by
  have hy : ((y : ZMod 5)) = ((((y % 5 : ℤ))) : ZMod 5) :=
    opc_intCast_residue y _ rfl
  have h' : ((((y % 5 : ℤ))) : ZMod 5) ^ 2 = 4 := by rw [← hy]; exact h
  have hmem := (opc_sq_eq_four_iff _).mp h'
  rcases hmem with h2 | h3
  · have hd : (5 : ℤ) ∣ y % 5 - 2 := by
      have e : ((((y % 5 - 2 : ℤ))) : ZMod 5) = 0 := by
        have e1 : ((((y % 5 - 2 : ℤ))) : ZMod 5)
            = ((((y % 5 : ℤ))) : ZMod 5) - 2 := by push_cast; ring
        rw [e1, h2, sub_self]
      exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp e
    exact Or.inl (by omega)
  · have hd : (5 : ℤ) ∣ y % 5 - 3 := by
      have e : ((((y % 5 - 3 : ℤ))) : ZMod 5) = 0 := by
        have e1 : ((((y % 5 - 3 : ℤ))) : ZMod 5)
            = ((((y % 5 : ℤ))) : ZMod 5) - 3 := by push_cast; ring
        rw [e1, h3, sub_self]
      exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp e
    exact Or.inr (by omega)

/-- A sum of two squares both divisible by 5 is zero mod 5. -/
private theorem opc_sq_add_zero_of_zero (x y : ℤ) (hx : x % 5 = 0)
    (hy : y % 5 = 0) : ((((x ^ 2 + y ^ 2 : ℤ))) : ZMod 5) = 0 := by
  have hpush : ((((x ^ 2 + y ^ 2 : ℤ))) : ZMod 5)
      = ((((x ^ 2 : ℤ))) : ZMod 5) + ((((y ^ 2 : ℤ))) : ZMod 5) := by
    push_cast; ring
  rw [hpush, opc_sq_zero x hx, opc_sq_zero y hy, add_zero]

/-- A `1 + 4` sum of squares is zero mod 5. -/
private theorem opc_sq_add_zero_of_mem (x y : ℤ)
    (hx : x % 5 = 1 ∨ x % 5 = 4) (hy : y % 5 = 2 ∨ y % 5 = 3) :
    ((((x ^ 2 + y ^ 2 : ℤ))) : ZMod 5) = 0 := by
  have hpush : ((((x ^ 2 + y ^ 2 : ℤ))) : ZMod 5)
      = ((((x ^ 2 : ℤ))) : ZMod 5) + ((((y ^ 2 : ℤ))) : ZMod 5) := by
    push_cast; ring
  rw [hpush, opc_sq_one x hx, opc_sq_four y hy]
  decide

/-- The two residue-class conditions cannot hold simultaneously off multiples
of 5: `x ≡ 3y` and `y ≡ 3x` force `5 ∣ y`. -/
private theorem opc_no_collide (x y : ℤ)
    (hmod : ((x : ZMod 5)) = 3 * ((y : ZMod 5)))
    (hcon : ((y : ZMod 5)) = 3 * ((x : ZMod 5))) : (5 : ℤ) ∣ y := by
  have hy0 : ((y : ZMod 5)) = 0 := by
    have h5 : (5 : ZMod 5) = 0 := by decide
    linear_combination 4 * hmod + 3 * hcon
      + ((x : ZMod 5) + (y : ZMod 5) * 2) * h5
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hy0

/-- The part of `opcT M` with `5 ∣ y` is the support of `a²`. -/
private def opcPart1 (M : ℕ) :
    {t : opcT M // (5 : ℤ) ∣ t.val.2} ≃
      opcSq (fun x => x % 5 = 0) (fun x => x % 5 = 0) (5 * M) where
  toFun t := by
    obtain ⟨⟨⟨x, y⟩, heq, hmod⟩, hdiv⟩ := t
    have hdiv' : (5 : ℤ) ∣ y := hdiv
    have hy0 : ((y : ZMod 5)) = 0 :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hdiv'
    have hx0 : ((x : ZMod 5)) = 0 := by rw [hmod, hy0, mul_zero]
    have hxdvd : (5 : ℤ) ∣ x :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hx0
    exact ⟨(x, y), (by omega : x % 5 = 0), (by omega : y % 5 = 0), heq⟩
  invFun s := by
    obtain ⟨⟨x, y⟩, hx, hy, heq⟩ := s
    have hxdvd : (5 : ℤ) ∣ x := by omega
    have hydvd : (5 : ℤ) ∣ y := by omega
    have hx0 : ((x : ZMod 5)) = 0 :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hxdvd
    have hy0 : ((y : ZMod 5)) = 0 :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hydvd
    exact ⟨⟨(x, y), heq, by rw [hx0, hy0, mul_zero]⟩, hydvd⟩
  left_inv t := by obtain ⟨⟨⟨x, y⟩, _, _⟩, _⟩ := t; rfl
  right_inv s := by obtain ⟨⟨x, y⟩, _, _, _⟩ := s; rfl

/-- The cast equation in `ZMod 5`. -/
private theorem opc_fwd_hXY (M : ℕ) (x y : ℤ)
    (heq : x ^ 2 + y ^ 2 = (((5 * M : ℕ)) : ℤ)) :
    ((x : ZMod 5)) ^ 2 + ((y : ZMod 5)) ^ 2 = 0 := by
  have hcast : ((((x ^ 2 + y ^ 2 : ℤ))) : ZMod 5)
      = ((((5 * M : ℕ))) : ZMod 5) := by rw [heq, Int.cast_natCast]
  have h0 : ((((5 * M : ℕ))) : ZMod 5) = 0 :=
    (ZMod.natCast_eq_zero_iff _ _).mpr (dvd_mul_right 5 M)
  rw [h0] at hcast
  have hpush : ((((x ^ 2 + y ^ 2 : ℤ))) : ZMod 5)
      = ((x : ZMod 5)) ^ 2 + ((y : ZMod 5)) ^ 2 := by push_cast; ring
  rw [hpush] at hcast
  exact hcast

/-- Negated form of the cast equation. -/
private theorem opc_fwd_hneg (x y : ℤ)
    (hXY : ((x : ZMod 5)) ^ 2 + ((y : ZMod 5)) ^ 2 = 0) :
    ((x : ZMod 5)) ^ 2 = -((y : ZMod 5)) ^ 2 := by
  linear_combination hXY

/-- From the equation and `y ≡ ±2`, get `x ≡ ±1`. -/
private theorem opc_fwd_mem_left (M : ℕ) (x y : ℤ)
    (heq : x ^ 2 + y ^ 2 = (((5 * M : ℕ)) : ℤ))
    (hcase : y % 5 = 2 ∨ y % 5 = 3) : x % 5 = 1 ∨ x % 5 = 4 := by
  have hneg := opc_fwd_hneg x y (opc_fwd_hXY M x y heq)
  have hy2 : ((y : ZMod 5)) ^ 2 = 4 := by
    have hsq := opc_sq_four y hcase
    have hpush : ((((y ^ 2 : ℤ))) : ZMod 5) = ((y : ZMod 5)) ^ 2 := by
      push_cast; ring
    rw [← hpush]
    exact hsq
  have hx2 : ((x : ZMod 5)) ^ 2 = 1 := by
    rw [hneg, hy2]
    decide
  exact opc_mem_pm1 x hx2

/-- Off multiples of 5 and outside `±2`, the residue is `±1`. -/
private theorem opc_fwd_mem_y (y : ℤ) (hny : ¬ (5 : ℤ) ∣ y)
    (_hcase : ¬ (y % 5 = 2 ∨ y % 5 = 3)) : y % 5 = 1 ∨ y % 5 = 4 := by
  omega

/-- From the equation and `y ≡ ±1`, get `x ≡ ±2`. -/
private theorem opc_fwd_mem_right (M : ℕ) (x y : ℤ)
    (heq : x ^ 2 + y ^ 2 = (((5 * M : ℕ)) : ℤ))
    (hym : y % 5 = 1 ∨ y % 5 = 4) : x % 5 = 2 ∨ x % 5 = 3 := by
  have hneg := opc_fwd_hneg x y (opc_fwd_hXY M x y heq)
  have hy2 : ((y : ZMod 5)) ^ 2 = 1 := by
    have hsq := opc_sq_one y hym
    have hpush : ((((y ^ 2 : ℤ))) : ZMod 5) = ((y : ZMod 5)) ^ 2 := by
      push_cast; ring
    rw [← hpush]
    exact hsq
  have hx2 : ((x : ZMod 5)) ^ 2 = 4 := by
    rw [hneg, hy2]
    decide
  exact opc_mem_pm2 x hx2

/-- The swapped equation. -/
private theorem opc_fwd_eq_swap (M : ℕ) (x y : ℤ)
    (heq : x ^ 2 + y ^ 2 = (((5 * M : ℕ)) : ℤ)) :
    y ^ 2 + x ^ 2 = (((5 * M : ℕ)) : ℤ) := by
  linear_combination heq

/-- Forward map for the off-diagonal part: identity when `y ≡ ±2`,
swap when `y ≡ ±1`. -/
private def opcPart2Fwd (M : ℕ) (x y : ℤ)
    (heq : x ^ 2 + y ^ 2 = (((5 * M : ℕ)) : ℤ))
    (_hmod : ((x : ZMod 5)) = 3 * ((y : ZMod 5))) (hny : ¬ (5 : ℤ) ∣ y) :
    opcSq (fun x => x % 5 = 1 ∨ x % 5 = 4)
      (fun x => x % 5 = 2 ∨ x % 5 = 3) (5 * M) := by
  refine dite (y % 5 = 2 ∨ y % 5 = 3) (fun hcase => ?_) (fun hcase => ?_)
  · exact ⟨(x, y), opc_fwd_mem_left M x y heq hcase, hcase, heq⟩
  · exact ⟨(y, x), opc_fwd_mem_y y hny hcase,
      opc_fwd_mem_right M x y heq (opc_fwd_mem_y y hny hcase),
      opc_fwd_eq_swap M x y heq⟩

/-- Off `±1`, the second coordinate is not divisible by 5. -/
private theorem opc_bwd_hn (b : ℤ) (hb : b % 5 = 2 ∨ b % 5 = 3) :
    ¬ (5 : ℤ) ∣ b := by
  omega

/-- Off `±2`, the first coordinate is not divisible by 5. -/
private theorem opc_bwd_hna (a : ℤ) (ha : a % 5 = 1 ∨ a % 5 = 4) :
    ¬ (5 : ℤ) ∣ a := by
  omega

/-- The swapped-back equation. -/
private theorem opc_bwd_eq_swap (M : ℕ) (a b : ℤ)
    (heq : a ^ 2 + b ^ 2 = (((5 * M : ℕ)) : ℤ)) :
    b ^ 2 + a ^ 2 = (((5 * M : ℕ)) : ℤ) := by
  linear_combination heq

/-- From residues and the negated equation, recover `b ≡ 3a`. -/
private theorem opc_bwd_hba (a b : ℤ)
    (ha : a % 5 = 1 ∨ a % 5 = 4) (hb : b % 5 = 2 ∨ b % 5 = 3)
    (h : ¬ ((a : ZMod 5)) = 3 * ((b : ZMod 5))) :
    ((b : ZMod 5)) = 3 * ((a : ZMod 5)) := by
  rcases ha with ha1 | ha4 <;> rcases hb with hb2 | hb3
  · exfalso
    apply h
    have ea := opc_intCast_residue a 1 ha1
    have eb := opc_intCast_residue b 2 hb2
    rw [ea, eb]
    decide
  · have ea := opc_intCast_residue a 1 ha1
    have eb := opc_intCast_residue b 3 hb3
    rw [eb, ea]
    decide
  · have ea := opc_intCast_residue a 4 ha4
    have eb := opc_intCast_residue b 2 hb2
    rw [eb, ea]
    decide
  · exfalso
    apply h
    have ea := opc_intCast_residue a 4 ha4
    have eb := opc_intCast_residue b 3 hb3
    rw [ea, eb]
    decide

/-- Backward map for the off-diagonal part: undo the swap exactly when the
equation reads `b ≡ 3a` instead of `a ≡ 3b`. -/
private def opcPart2Bwd (M : ℕ) (a b : ℤ)
    (ha : a % 5 = 1 ∨ a % 5 = 4) (hb : b % 5 = 2 ∨ b % 5 = 3)
    (heq : a ^ 2 + b ^ 2 = (((5 * M : ℕ)) : ℤ)) :
    {t : opcT M // ¬ (5 : ℤ) ∣ t.val.2} := by
  refine dite (((a : ZMod 5)) = 3 * ((b : ZMod 5))) (fun h => ?_) (fun h => ?_)
  · exact ⟨⟨(a, b), heq, h⟩, opc_bwd_hn b hb⟩
  · exact ⟨⟨(b, a), opc_bwd_eq_swap M a b heq, opc_bwd_hba a b ha hb h⟩,
      opc_bwd_hna a ha⟩

/-- Computation rule: the forward map takes the identity branch. -/
private theorem opcPart2Fwd_pos (M : ℕ) (x y : ℤ)
    (heq : x ^ 2 + y ^ 2 = (((5 * M : ℕ)) : ℤ))
    (hmod : ((x : ZMod 5)) = 3 * ((y : ZMod 5))) (hny : ¬ (5 : ℤ) ∣ y)
    (hcase : y % 5 = 2 ∨ y % 5 = 3) :
    opcPart2Fwd M x y heq hmod hny
      = ⟨(x, y), opc_fwd_mem_left M x y heq hcase, hcase, heq⟩ := by
  unfold opcPart2Fwd
  exact dite_eq_left hcase

/-- Computation rule: the forward map takes the swap branch. -/
private theorem opcPart2Fwd_neg (M : ℕ) (x y : ℤ)
    (heq : x ^ 2 + y ^ 2 = (((5 * M : ℕ)) : ℤ))
    (hmod : ((x : ZMod 5)) = 3 * ((y : ZMod 5))) (hny : ¬ (5 : ℤ) ∣ y)
    (hcase : ¬ (y % 5 = 2 ∨ y % 5 = 3)) :
    opcPart2Fwd M x y heq hmod hny
      = ⟨(y, x), opc_fwd_mem_y y hny hcase,
        opc_fwd_mem_right M x y heq (opc_fwd_mem_y y hny hcase),
        opc_fwd_eq_swap M x y heq⟩ := by
  unfold opcPart2Fwd
  exact dite_eq_right hcase

/-- Computation rule: the backward map keeps the coordinates. -/
private theorem opcPart2Bwd_pos (M : ℕ) (a b : ℤ)
    (ha : a % 5 = 1 ∨ a % 5 = 4) (hb : b % 5 = 2 ∨ b % 5 = 3)
    (heq : a ^ 2 + b ^ 2 = (((5 * M : ℕ)) : ℤ))
    (h : ((a : ZMod 5)) = 3 * ((b : ZMod 5))) :
    opcPart2Bwd M a b ha hb heq = ⟨⟨(a, b), heq, h⟩, opc_bwd_hn b hb⟩ := by
  unfold opcPart2Bwd
  exact dite_eq_left h

/-- Computation rule: the backward map swaps the coordinates back. -/
private theorem opcPart2Bwd_neg (M : ℕ) (a b : ℤ)
    (ha : a % 5 = 1 ∨ a % 5 = 4) (hb : b % 5 = 2 ∨ b % 5 = 3)
    (heq : a ^ 2 + b ^ 2 = (((5 * M : ℕ)) : ℤ))
    (h : ¬ ((a : ZMod 5)) = 3 * ((b : ZMod 5))) :
    opcPart2Bwd M a b ha hb heq
      = ⟨⟨(b, a), opc_bwd_eq_swap M a b heq, opc_bwd_hba a b ha hb h⟩,
        opc_bwd_hna a ha⟩ := by
  unfold opcPart2Bwd
  exact dite_eq_right h

/-- The off-diagonal part of `opcT M` is the support of `b * c`. -/
private def opcPart2 (M : ℕ) :
    {t : opcT M // ¬ (5 : ℤ) ∣ t.val.2} ≃
      opcSq (fun x => x % 5 = 1 ∨ x % 5 = 4)
        (fun x => x % 5 = 2 ∨ x % 5 = 3) (5 * M) where
  toFun t := opcPart2Fwd M t.val.val.1 t.val.val.2
    t.val.property.1 t.val.property.2 t.property
  invFun s := opcPart2Bwd M s.val.1 s.val.2
    s.property.1 s.property.2.1 s.property.2.2
  left_inv t := by
    obtain ⟨⟨⟨x, y⟩, heq, hmod⟩, hny⟩ := t
    dsimp only
    by_cases hcase : y % 5 = 2 ∨ y % 5 = 3
    · rw [opcPart2Fwd_pos M x y heq hmod hny hcase,
        opcPart2Bwd_pos M x y _ _ heq hmod]
    · have hneg : ¬ ((y : ZMod 5)) = 3 * ((x : ZMod 5)) := by
        intro hcon
        exact hny (opc_no_collide x y hmod hcon)
      rw [opcPart2Fwd_neg M x y heq hmod hny hcase,
        opcPart2Bwd_neg M y x _ _ _ hneg]
  right_inv s := by
    obtain ⟨⟨a, b⟩, ha, hb, heq⟩ := s
    dsimp only
    by_cases h : ((a : ZMod 5)) = 3 * ((b : ZMod 5))
    · rw [opcPart2Bwd_pos M a b ha hb heq h,
        opcPart2Fwd_pos M a b heq h _ hb]
    · have hneg : ¬ (a % 5 = 2 ∨ a % 5 = 3) := by omega
      rw [opcPart2Bwd_neg M a b ha hb heq h,
        opcPart2Fwd_neg M b a _ _ _ hneg]

/-- Splitting the count of `opcT M` into the `a²` and `b * c` parts. -/
private theorem opc_card_split (M : ℕ) : Nat.card (opcT M)
    = Nat.card (opcSq (fun x => x % 5 = 0) (fun x => x % 5 = 0) (5 * M))
      + Nat.card (opcSq (fun x => x % 5 = 1 ∨ x % 5 = 4)
        (fun x => x % 5 = 2 ∨ x % 5 = 3) (5 * M)) := by
  have hfin : Finite (opcSq (fun _ => True) (fun _ => True) M) :=
    opc_finite_sqFiber _ _ M
  have hT : Finite (opcT M) := Finite.of_equiv _ (opcPhi M)
  have hdiv : Finite {t : opcT M // (5 : ℤ) ∣ t.val.2} :=
    Finite.of_injective Subtype.val Subtype.val_injective
  have hndiv : Finite {t : opcT M // ¬ (5 : ℤ) ∣ t.val.2} :=
    Finite.of_injective Subtype.val Subtype.val_injective
  have eT := Equiv.sumCompl (fun t : opcT M => (5 : ℤ) ∣ t.val.2)
  rw [← Nat.card_congr eT, Nat.card_sum, Nat.card_congr (opcPart1 M),
    Nat.card_congr (opcPart2 M)]

/-- `a² + b * c` is the 5-expansion of `θ²`. -/
private theorem opc_dissection_sq_add_mul_eq_expand :
    opcA ^ 2 + opcB * opcC
      = PowerSeries.expand 5 (by decide : (5 : ℕ) ≠ 0) (opcTheta ^ 2) := by
  apply PowerSeries.ext
  intro N
  have hLHS : PowerSeries.coeff N (opcA ^ 2 + opcB * opcC)
      = ((Nat.card (opcSq (fun x => x % 5 = 0) (fun x => x % 5 = 0) N) : ℕ) : ℤ)
        + ((Nat.card (opcSq (fun x => x % 5 = 1 ∨ x % 5 = 4)
            (fun x => x % 5 = 2 ∨ x % 5 = 3) N) : ℕ) : ℤ) := by
    unfold opcA opcB opcC
    rw [map_add, pow_two, opc_coeff_mul_thetaOn, opc_coeff_mul_thetaOn]
  rw [hLHS]
  by_cases hd : (5 : ℕ) ∣ N
  · obtain ⟨M, rfl⟩ := hd
    rw [PowerSeries.coeff_expand_mul]
    have hRHS : PowerSeries.coeff M (opcTheta ^ 2)
        = ((Nat.card (opcSq (fun _ => True) (fun _ => True) M) : ℕ) : ℤ) := by
      unfold opcTheta
      rw [pow_two, opc_coeff_mul_thetaOn]
    rw [hRHS, Nat.card_congr (opcPhi M), opc_card_split M, Nat.cast_add]
  · rw [PowerSeries.coeff_expand_of_not_dvd _ _ _ hd,
      opc_card_sq_eq_zero _ _ _ (fun x y hx hy =>
        opc_sq_add_zero_of_zero x y hx hy) hd,
      opc_card_sq_eq_zero _ _ _ (fun x y hx hy =>
        opc_sq_add_zero_of_mem x y hx hy) hd]
    simp

/-- `5 ≠ 0`, shared proof term for `expand 5` uses. -/
private theorem opc_five_ne_zero : (5 : ℕ) ≠ 0 := by decide

/-- The 5-dissection of `θ⁴`. -/
private theorem opc_theta_pow_four_decomp :
    ∃ W R₁ R₂ R₃ R₄ : ℤ⟦X⟧,
      opcSupportedMod ℤ 5 1 R₁ ∧ opcSupportedMod ℤ 5 2 R₂ ∧
        opcSupportedMod ℤ 5 3 R₃ ∧ opcSupportedMod ℤ 5 4 R₄ ∧
        opcTheta ^ 4 = PowerSeries.expand 5 opc_five_ne_zero (opcTheta ^ 4)
          + 5 • W + (R₁ + R₂ + R₃ + R₄) := by
  have mAA : opcSupportedMod ℤ 5 0 (opcA * opcA) :=
    opc_supportedMod_mul 5 0 0 _ _ opc_supportA opc_supportA
  have mAAA : opcSupportedMod ℤ 5 0 (opcA * opcA * opcA) :=
    opc_supportedMod_mul 5 0 0 _ _ mAA opc_supportA
  have mAAAB : opcSupportedMod ℤ 5 1 (opcA * opcA * opcA * opcB) :=
    opc_supportedMod_mul 5 0 1 _ _ mAAA opc_supportB
  have mBB : opcSupportedMod ℤ 5 2 (opcB * opcB) :=
    opc_supportedMod_mul 5 1 1 _ _ opc_supportB opc_supportB
  have mABB : opcSupportedMod ℤ 5 2 (opcA * (opcB * opcB)) :=
    opc_supportedMod_mul 5 0 2 _ _ opc_supportA mBB
  have mABBC : opcSupportedMod ℤ 5 1 (opcA * (opcB * opcB) * opcC) :=
    opc_supportedMod_mul 5 2 4 _ _ mABB opc_supportC
  have mCC : opcSupportedMod ℤ 5 3 (opcC * opcC) :=
    opc_supportedMod_mul 5 4 4 _ _ opc_supportC opc_supportC
  have mCCC : opcSupportedMod ℤ 5 2 (opcC * opcC * opcC) :=
    opc_supportedMod_mul 5 3 4 _ _ mCC opc_supportC
  have mCCCC : opcSupportedMod ℤ 5 1 (opcC * opcC * opcC * opcC) :=
    opc_supportedMod_mul 5 2 4 _ _ mCCC opc_supportC
  have mBBB : opcSupportedMod ℤ 5 3 (opcB * opcB * opcB) :=
    opc_supportedMod_mul 5 2 1 _ _ mBB opc_supportB
  have mAABB : opcSupportedMod ℤ 5 2 (opcA * opcA * (opcB * opcB)) :=
    opc_supportedMod_mul 5 0 2 _ _ mAA mBB
  have mBBBC : opcSupportedMod ℤ 5 2 (opcB * opcB * opcB * opcC) :=
    opc_supportedMod_mul 5 3 4 _ _ mBBB opc_supportC
  have mACCC : opcSupportedMod ℤ 5 2 (opcA * (opcC * opcC * opcC)) :=
    opc_supportedMod_mul 5 0 2 _ _ opc_supportA mCCC
  have mACC : opcSupportedMod ℤ 5 3 (opcA * opcA * (opcC * opcC)) :=
    opc_supportedMod_mul 5 0 3 _ _ mAA mCC
  have mBCCC : opcSupportedMod ℤ 5 3 (opcB * (opcC * opcC * opcC)) :=
    opc_supportedMod_mul 5 1 2 _ _ opc_supportB mCCC
  have mABBB : opcSupportedMod ℤ 5 3 (opcA * (opcB * opcB * opcB)) :=
    opc_supportedMod_mul 5 0 3 _ _ opc_supportA mBBB
  have mAAAC : opcSupportedMod ℤ 5 4 (opcA * opcA * opcA * opcC) :=
    opc_supportedMod_mul 5 0 4 _ _ mAAA opc_supportC
  have mAB : opcSupportedMod ℤ 5 1 (opcA * opcB) :=
    opc_supportedMod_mul 5 0 1 _ _ opc_supportA opc_supportB
  have mABCC : opcSupportedMod ℤ 5 4 (opcA * opcB * (opcC * opcC)) :=
    opc_supportedMod_mul 5 1 3 _ _ mAB mCC
  have mBBBB : opcSupportedMod ℤ 5 4 (opcB * opcB * opcB * opcB) :=
    opc_supportedMod_mul 5 3 1 _ _ mBBB opc_supportB
  refine ⟨2 • (opcA * opcA * opcB * opcC) + opcB * opcB * (opcC * opcC),
    4 • (opcA * opcA * opcA * opcB) + 12 • (opcA * (opcB * opcB) * opcC)
      + opcC * opcC * opcC * opcC,
    6 • (opcA * opcA * (opcB * opcB)) + 4 • (opcB * opcB * opcB * opcC)
      + 4 • (opcA * (opcC * opcC * opcC)),
    6 • (opcA * opcA * (opcC * opcC)) + 4 • (opcB * (opcC * opcC * opcC))
      + 4 • (opcA * (opcB * opcB * opcB)),
    4 • (opcA * opcA * opcA * opcC) + 12 • (opcA * opcB * (opcC * opcC))
      + opcB * opcB * opcB * opcB,
    ?_, ?_, ?_, ?_, ?_⟩
  · refine opc_supportedMod_add 5 1 _ _ ?_ ?_
    · refine opc_supportedMod_add 5 1 _ _ ?_ ?_
      · exact opc_supportedMod_nsmul 5 1 _ 4 mAAAB
      · exact opc_supportedMod_nsmul 5 1 _ 12 mABBC
    · exact mCCCC
  · refine opc_supportedMod_add 5 2 _ _ ?_ ?_
    · refine opc_supportedMod_add 5 2 _ _ ?_ ?_
      · exact opc_supportedMod_nsmul 5 2 _ 6 mAABB
      · exact opc_supportedMod_nsmul 5 2 _ 4 mBBBC
    · exact opc_supportedMod_nsmul 5 2 _ 4 mACCC
  · refine opc_supportedMod_add 5 3 _ _ ?_ ?_
    · refine opc_supportedMod_add 5 3 _ _ ?_ ?_
      · exact opc_supportedMod_nsmul 5 3 _ 6 mACC
      · exact opc_supportedMod_nsmul 5 3 _ 4 mBCCC
    · exact opc_supportedMod_nsmul 5 3 _ 4 mABBB
  · refine opc_supportedMod_add 5 4 _ _ ?_ ?_
    · refine opc_supportedMod_add 5 4 _ _ ?_ ?_
      · exact opc_supportedMod_nsmul 5 4 _ 4 mAAAC
      · exact opc_supportedMod_nsmul 5 4 _ 12 mABCC
    · exact mBBBB
  · have hpow : ((opcTheta ^ 2) ^ 2 : ℤ⟦X⟧) = opcTheta ^ 4 := by ring
    have hsq : (opcA ^ 2 + opcB * opcC) ^ 2
        = PowerSeries.expand 5 opc_five_ne_zero (opcTheta ^ 4) := by
      rw [opc_dissection_sq_add_mul_eq_expand, ← map_pow, hpow]
    conv_lhs => rw [opc_theta_eq_dissection]
    rw [← hsq]
    ring

-- Gauss's identity via the analytic Jacobi triple product.
-- Stubs first; proofs to follow.

/-- Analytic Gauss identity: the `z = 1` specialization of JTP. -/
private theorem opc_tsum_sq_mul_eulerFunction_sq (q : ℂ) (hq : ‖q‖ < 1) :
    (∑' n : ℤ, q ^ (n * n).toNat) * eulerFunction (q ^ 2)
      = eulerFunction (-q) ^ 2 := by
  have hJ := MetaMathlibExt.Analysis.SpecialFunctions.JacobiTripleProduct.jacobi_triple_product
    1 q one_ne_zero hq
  obtain ⟨hs, hm, heq⟩ := hJ
  have hgeo : Summable fun n : ℕ => ‖q‖ ^ n :=
    summable_geometric_of_lt_one (norm_nonneg _) hq
  have hVnorm : Summable fun n : ℕ => ‖q ^ (2 * n + 1)‖ := by
    refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) ?_ hgeo
    intro n
    rw [norm_pow]
    exact pow_le_pow_of_le_one (norm_nonneg _) (le_of_lt hq) (by omega)
  have hUnorm : Summable fun n : ℕ => ‖q ^ (2 * n + 2)‖ := by
    refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) ?_ hgeo
    intro n
    rw [norm_pow]
    exact pow_le_pow_of_le_one (norm_nonneg _) (le_of_lt hq) (by omega)
  have mV : Multipliable fun n : ℕ => (1 + q ^ (2 * n + 1)) :=
    multipliable_one_add_of_summable hVnorm
  have mU : Multipliable fun n : ℕ => (1 - q ^ (2 * n + 2)) := by
    have hUneg : Summable fun n : ℕ => ‖-(q ^ (2 * n + 2))‖ :=
      (summable_congr (fun n : ℕ => norm_neg _)).mpr hUnorm
    have h := multipliable_one_add_of_summable
      (f := fun n : ℕ => (-(q ^ (2 * n + 2)))) hUneg
    have eU : ∀ n : ℕ, (1 + (-(q ^ (2 * n + 2)))) = (1 - q ^ (2 * n + 2)) :=
      fun n => by ring
    exact (multipliable_congr eU).mp h
  have mA : Multipliable fun n : ℕ =>
      ((1 - q ^ (2 * n + 2)) * (1 + q ^ (2 * n + 1))
        * (1 + q ^ (2 * n + 1))) :=
    (mU.mul mV).mul mV
  have eEven : ∀ k : ℕ, (1 + q ^ (2 * k + 1)) = (1 - (-q) ^ (2 * k + 1)) :=
    fun k => by rw [Odd.neg_pow ⟨k, rfl⟩ _, sub_neg_eq_add]
  have mEven : Multipliable fun k : ℕ => (1 - (-q) ^ (2 * k + 1)) :=
    (multipliable_congr eEven).mp mV
  have eOdd : ∀ k : ℕ, (1 - q ^ (2 * k + 2)) = (1 - (-q) ^ (2 * k + 1 + 1)) :=
    fun k => by
      rw [show (2 * k + 1) + 1 = 2 * k + 2 from by ring,
        Even.neg_pow ⟨k + 1, by ring⟩ _]
  have mOdd : Multipliable fun k : ℕ => (1 - (-q) ^ (2 * k + 1 + 1)) :=
    (multipliable_congr eOdd).mp mU
  have htsum : (∑' n : ℤ, q ^ (n * n).toNat)
      = ∏' n : ℕ, ((1 - q ^ (2 * n + 2)) * (1 + q ^ (2 * n + 1))
        * (1 + q ^ (2 * n + 1))) := by
    have e1 : (∑' n : ℤ, q ^ (n * n).toNat)
        = ∑' n : ℤ, (1 : ℂ) ^ n * q ^ (n * n).toNat :=
      tsum_congr fun n => by simp
    have e2 : (∏' n : ℕ, (1 - q ^ (2 * n + 2))
          * (1 + (1 : ℂ) * q ^ (2 * n + 1))
          * (1 + (1 : ℂ)⁻¹ * q ^ (2 * n + 1)))
        = ∏' n : ℕ, ((1 - q ^ (2 * n + 2)) * (1 + q ^ (2 * n + 1))
          * (1 + q ^ (2 * n + 1))) :=
      tprod_congr fun n => by simp
    rw [e1, heq]
    exact e2
  have hq2 : ‖q ^ 2‖ < 1 := by
    rw [norm_pow]
    exact pow_lt_one₀ (norm_nonneg _) hq two_ne_zero
  have hmq : ‖-q‖ < 1 := by rwa [norm_neg]
  have eE2 : eulerFunction (q ^ 2)
      = ∏' n : ℕ, (1 - q ^ (2 * n + 2)) := by
    rw [eulerFunction_eq_tprod hq2]
    apply tprod_congr
    intro n
    have e : 2 * (n + 1) = 2 * n + 2 := by ring
    rw [← pow_mul, e]
  have hsplit := tprod_even_mul_odd
    (f := fun m : ℕ => (1 - (-q) ^ (m + 1))) mEven mOdd
  have eEm : eulerFunction (-q)
      = (∏' n : ℕ, (1 + q ^ (2 * n + 1)))
        * (∏' n : ℕ, (1 - q ^ (2 * n + 2))) := by
    rw [eulerFunction_eq_tprod hmq, hsplit.symm]
    congr 1
    · exact tprod_congr (fun k : ℕ => by
        rw [Odd.neg_pow ⟨k, rfl⟩ _, sub_neg_eq_add])
    · exact tprod_congr (fun k : ℕ => by
        rw [show (2 * k + 1) + 1 = 2 * k + 2 from by ring,
          Even.neg_pow ⟨k + 1, by ring⟩ _])
  have mVU := mV.mul mU
  calc (∑' n : ℤ, q ^ (n * n).toNat) * eulerFunction (q ^ 2)
      = (∏' n : ℕ, ((1 - q ^ (2 * n + 2)) * (1 + q ^ (2 * n + 1))
          * (1 + q ^ (2 * n + 1))))
        * (∏' n : ℕ, (1 - q ^ (2 * n + 2))) := by rw [htsum, eE2]
    _ = ∏' n : ℕ, (((1 - q ^ (2 * n + 2)) * (1 + q ^ (2 * n + 1))
          * (1 + q ^ (2 * n + 1))) * (1 - q ^ (2 * n + 2))) :=
        (Multipliable.tprod_mul mA mU).symm
    _ = ∏' n : ℕ, (((1 + q ^ (2 * n + 1)) * (1 - q ^ (2 * n + 2)))
          * ((1 + q ^ (2 * n + 1)) * (1 - q ^ (2 * n + 2)))) :=
        tprod_congr (fun n : ℕ => by ring)
    _ = (∏' n : ℕ, ((1 + q ^ (2 * n + 1)) * (1 - q ^ (2 * n + 2))))
        * (∏' n : ℕ, ((1 + q ^ (2 * n + 1)) * (1 - q ^ (2 * n + 2)))) :=
        Multipliable.tprod_mul mVU mVU
    _ = ((∏' n : ℕ, (1 + q ^ (2 * n + 1)))
          * (∏' n : ℕ, (1 - q ^ (2 * n + 2))))
        * ((∏' n : ℕ, (1 + q ^ (2 * n + 1)))
          * (∏' n : ℕ, (1 - q ^ (2 * n + 2)))) := by
        rw [Multipliable.tprod_mul mV mU]
    _ = eulerFunction (-q) ^ 2 := by
        have e : (∏' n : ℕ, (1 + q ^ (2 * n + 1)))
            * (∏' n : ℕ, (1 - q ^ (2 * n + 2))) = eulerFunction (-q) :=
          eEm.symm
        rw [e]
        exact (pow_two _).symm

/-- Cauchy product for evaluations of integer power series. -/
private theorem opc_hasSum_mul_of_abs_summable (F G : ℤ⟦X⟧) (q : ℂ)
    (hF : Summable fun n : ℕ => ‖(((((F.coeff n : ℤ))) : ℂ)) * q ^ n‖)
    (hG : Summable fun n : ℕ => ‖(((((G.coeff n : ℤ))) : ℂ)) * q ^ n‖) :
    HasSum (fun n : ℕ => ((((((F * G).coeff n : ℤ))) : ℂ)) * q ^ n)
      ((∑' n : ℕ, (((((F.coeff n : ℤ))) : ℂ)) * q ^ n)
        * (∑' n : ℕ, (((((G.coeff n : ℤ))) : ℂ)) * q ^ n))
      ∧ Summable fun n : ℕ => ‖((((((F * G).coeff n : ℤ))) : ℂ)) * q ^ n‖ := by
  have hterm : ∀ n : ℕ, (∑ kl ∈ Finset.antidiagonal n,
        (((((F.coeff kl.1 : ℤ))) : ℂ)) * q ^ kl.1
          * ((((((G.coeff kl.2 : ℤ))) : ℂ)) * q ^ kl.2))
      = ((((((F * G).coeff n : ℤ))) : ℂ)) * q ^ n := by
    intro n
    rw [PowerSeries.coeff_mul, Int.cast_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun kl hkl => ?_)
    obtain ⟨i, k⟩ := kl
    have hmem : i + k = n := Finset.mem_antidiagonal.mp hkl
    have hpair : (((((F.coeff i : ℤ))) : ℂ)) * q ^ i
          * ((((((G.coeff k : ℤ))) : ℂ)) * q ^ k)
        = (((((F.coeff i * G.coeff k : ℤ))) : ℂ)) * q ^ (i + k) := by
      rw [Int.cast_mul, pow_add]
      ring
    rw [← hmem]
    exact hpair
  have hnorm := summable_norm_sum_mul_antidiagonal_of_summable_norm hF hG
  have htsum := tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm hF hG
  have hHas : HasSum (fun n : ℕ => ((((((F * G).coeff n : ℤ))) : ℂ)) * q ^ n)
      ((∑' n : ℕ, (((((F.coeff n : ℤ))) : ℂ)) * q ^ n)
        * (∑' n : ℕ, (((((G.coeff n : ℤ))) : ℂ)) * q ^ n)) := by
    have h2 := hnorm.of_norm.hasSum.congr_fun (fun n => (hterm n).symm)
    rwa [← htsum] at h2
  exact ⟨hHas, hHas.summable.norm⟩

/-- Norm summability from a uniform coefficient bound. -/
private theorem opc_summable_norm_series (F : ℤ⟦X⟧) (C : ℝ) (q : ℂ)
    (hq : ‖q‖ < 1) (hC : ∀ n : ℕ, ‖(((((F.coeff n : ℤ))) : ℂ))‖ ≤ C) :
    Summable fun n : ℕ => ‖(((((F.coeff n : ℤ))) : ℂ)) * q ^ n‖ := by
  have hgeo : Summable fun n : ℕ => C * ‖q‖ ^ n :=
    (summable_geometric_of_lt_one (norm_nonneg _) hq).mul_left C
  have h1 : Summable fun n : ℕ => ‖(((((F.coeff n : ℤ))) : ℂ)) * q ^ n‖ := by
    refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) ?_ hgeo
    intro n
    have e1 : ‖(((((F.coeff n : ℤ))) : ℂ)) * q ^ n‖
        = ‖(((((F.coeff n : ℤ))) : ℂ))‖ * ‖q‖ ^ n := by
      rw [norm_mul, norm_pow]
    rw [e1]
    exact mul_le_mul_of_nonneg_right (hC n) (pow_nonneg (norm_nonneg _) n)
  exact h1

/-- The exponent `(x * x).toNat` on `ℤ` equals `x.natAbs ^ 2`. -/
private theorem opc_sq_toNat (x : ℤ) : (x * x).toNat = x.natAbs ^ 2 := by
  have hnn : 0 ≤ x * x := mul_self_nonneg x
  have h : (((x * x).toNat : ℕ) : ℤ) = (((x.natAbs ^ 2 : ℕ)) : ℤ) := by
    rw [Int.toNat_of_nonneg hnn, Nat.cast_pow, Int.natAbs_sq, ← pow_two]
  exact_mod_cast h

/-- The `ℤ`-indexed square-power family is summable inside the unit disk. -/
private theorem opc_summable_sq_pow (q : ℂ) (hq : ‖q‖ < 1) :
    Summable fun x : ℤ => q ^ (x * x).toNat := by
  have hgeo : Summable fun n : ℕ => ‖q‖ ^ n :=
    summable_geometric_of_lt_one (norm_nonneg _) hq
  have hside : Summable fun x : ℤ => ‖q‖ ^ x.natAbs := by
    apply Summable.of_nat_of_neg
    · simpa using hgeo
    · simpa using hgeo
  refine Summable.of_norm_bounded hside ?_
  intro x
  rw [opc_sq_toNat, norm_pow]
  have hle : x.natAbs ≤ x.natAbs ^ 2 := Nat.le_self_pow (by norm_num) _
  exact pow_le_pow_of_le_one (norm_nonneg _) hq.le hle

/-- Theta fibers over `ℤ` match the `True`-subtype fibers. -/
private def opcThetaFiber (m : ℕ) :
    {x : Subtype (fun _ : ℤ => True) // x.val.natAbs ^ 2 = m} ≃
      {x : ℤ // x.natAbs ^ 2 = m} where
  toFun x := ⟨x.val.val, x.property⟩
  invFun x := ⟨⟨x.val, trivial⟩, x.property⟩
  left_inv x := by obtain ⟨⟨_, _⟩, _⟩ := x; rfl
  right_inv x := by obtain ⟨_, _⟩ := x; rfl

/-- Theta coefficients count square fibers. -/
private theorem opc_theta_coeff_eq_card (m : ℕ) :
    opcTheta.coeff m = ((Nat.card {x : ℤ // x.natAbs ^ 2 = m} : ℕ) : ℤ) := by
  unfold opcTheta opcThetaOn opcWeight
  rw [PowerSeries.coeff_mk]
  exact congrArg _ (Nat.card_congr (opcThetaFiber m))

/-- Each theta fiber sums to the theta coefficient times `q ^ m`. -/
private theorem opc_fiber_hasSum (q : ℂ) (m : ℕ) :
    HasSum (fun x : {x : ℤ // x.natAbs ^ 2 = m} => q ^ (x.val * x.val).toNat)
      (((((opcTheta.coeff m : ℤ)) : ℂ)) * q ^ m) := by
  have hfin := opc_finite_intFiber m
  have hFT : Fintype {x : ℤ // x.natAbs ^ 2 = m} := Fintype.ofFinite _
  have hterm : ∀ x : {x : ℤ // x.natAbs ^ 2 = m},
      q ^ (x.val * x.val).toNat = q ^ m := by
    intro x
    congr 1
    rw [opc_sq_toNat]
    exact x.property
  have hsum : (∑ x : {x : ℤ // x.natAbs ^ 2 = m}, q ^ (x.val * x.val).toNat)
      = (((((opcTheta.coeff m : ℤ)) : ℂ)) * q ^ m) := by
    simp_rw [hterm, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    congr 1
    rw [opc_theta_coeff_eq_card, Nat.card_eq_fintype_card, Int.cast_natCast]
  rw [← hsum]
  exact hasSum_fintype _

/-- The sigma of square fibers over `ℕ` is `ℤ`. -/
private def opcSigmaTheta : (Σ _m : ℕ, {x : ℤ // x.natAbs ^ 2 = _m}) ≃ ℤ where
  toFun p := p.2.val
  invFun x := ⟨x.natAbs ^ 2, x, rfl⟩
  left_inv p := by obtain ⟨m, x, rfl⟩ := p; rfl
  right_inv x := rfl

/-- Evaluation of the theta series. -/
private theorem opc_eval_thetaSeries (q : ℂ) (hq : ‖q‖ < 1) :
    (∑' n : ℕ, (((((opcTheta.coeff n : ℤ))) : ℂ)) * q ^ n)
      = ∑' n : ℤ, q ^ (n * n).toNat := by
  have hbase := (opc_summable_sq_pow q hq).hasSum
  have hsig := (Equiv.hasSum_iff opcSigmaTheta).mpr hbase
  have hmain : HasSum (fun n : ℕ => (((((opcTheta.coeff n : ℤ))) : ℂ)) * q ^ n)
      (∑' n : ℤ, q ^ (n * n).toNat) :=
    HasSum.sigma hsig (fun m => opc_fiber_hasSum q m)
  exact hmain.tsum_eq

/-- The coefficients of `pentagonalSeries ℂ` are casts of the `ℤ` ones. -/
private theorem opc_coeff_pent_complex_eq (n : ℕ) :
    (PowerSeries.pentagonalSeries ℂ).coeff n
      = ((((PowerSeries.pentagonalSeries ℤ).coeff n : ℤ)) : ℂ) := by
  by_cases hn : n ∈ Set.range pentagonal
  · obtain ⟨k, rfl⟩ := hn
    have h1 : (PowerSeries.pentagonalSeries ℂ).coeff (pentagonal k)
        = (-1 : ℂ) ^ k.natAbs := by
      rw [PowerSeries.coeff_pentagonalSeries_pentagonal, Int.coe_negOnePow]
    have h2 : ((((PowerSeries.pentagonalSeries ℤ).coeff (pentagonal k) : ℤ)) : ℂ)
        = (-1 : ℂ) ^ k.natAbs := by
      rw [PowerSeries.coeff_pentagonalSeries_pentagonal, Int.coe_negOnePow,
        Int.cast_pow, Int.cast_neg, Int.cast_one]
    rw [h1, h2]
  · rw [PowerSeries.coeff_pentagonalSeries_eq_zero ℂ hn,
      PowerSeries.coeff_pentagonalSeries_eq_zero ℤ hn, Int.cast_zero]

/-- The cast coefficients of `pentagonalSeries ℤ` are bounded by one in norm. -/
private theorem opc_norm_pentCoeff_le_one (n : ℕ) :
    ‖(((((PowerSeries.pentagonalSeries ℤ).coeff n : ℤ)) : ℂ))‖ ≤ 1 := by
  by_cases hn : n ∈ Set.range pentagonal
  · obtain ⟨k, rfl⟩ := hn
    rw [PowerSeries.coeff_pentagonalSeries_pentagonal, Int.coe_negOnePow,
      Int.cast_pow, Int.cast_neg, Int.cast_one, norm_pow]
    simp
  · rw [PowerSeries.coeff_pentagonalSeries_eq_zero ℤ hn, Int.cast_zero, norm_zero]
    exact zero_le_one

/-- Evaluation of the 2-expansion of the Euler product. -/
private theorem opc_eval_expand_two (q : ℂ) (hq : ‖q‖ < 1) :
    (∑' n : ℕ, ((((((PowerSeries.expand 2 two_ne_zero
        (PowerSeries.pentagonalSeries ℤ)).coeff n : ℤ))) : ℂ)) * q ^ n)
      = eulerFunction (q ^ 2) := by
  have hq2 : ‖q ^ 2‖ < 1 := by
    rw [norm_pow]
    exact pow_lt_one₀ (norm_nonneg _) hq two_ne_zero
  have heuler := hasSum_eulerFunction_pentagonalSeries hq2
  have hinj : Function.Injective (fun k : ℕ => 2 * k) := by
    intro a b h
    dsimp only at h
    omega
  have hsupp : Function.support (fun n : ℕ => (((((PowerSeries.expand 2
      two_ne_zero (PowerSeries.pentagonalSeries ℤ)).coeff n : ℤ))) : ℂ) * q ^ n)
      ⊆ Set.range (fun k : ℕ => 2 * k) := by
    intro n hn
    rw [Function.mem_support] at hn
    by_cases hd : 2 ∣ n
    · obtain ⟨k, hk⟩ := hd
      exact ⟨k, hk.symm⟩
    · exfalso
      apply hn
      rw [PowerSeries.coeff_expand_of_not_dvd _ _ _ hd, Int.cast_zero, zero_mul]
  have hterm : ∀ k : ℕ, (((((PowerSeries.expand 2 two_ne_zero
      (PowerSeries.pentagonalSeries ℤ)).coeff (2 * k) : ℤ))) : ℂ) * q ^ (2 * k)
        = (PowerSeries.pentagonalSeries ℂ).coeff k * (q ^ 2) ^ k := by
    intro k
    rw [PowerSeries.coeff_expand_mul, ← opc_coeff_pent_complex_eq, pow_mul]
  rw [← hinj.tsum_eq hsupp, tsum_congr hterm]
  exact heuler.tsum_eq

/-- Evaluation of the sign-twisted Euler product. -/
private theorem opc_eval_rescale_neg (q : ℂ) (hq : ‖q‖ < 1) :
    (∑' n : ℕ, ((((((PowerSeries.rescale (-1 : ℤ)
        (PowerSeries.pentagonalSeries ℤ)).coeff n : ℤ))) : ℂ)) * q ^ n)
      = eulerFunction (-q) := by
  have hmq : ‖-q‖ < 1 := by rwa [norm_neg]
  have heuler := hasSum_eulerFunction_pentagonalSeries hmq
  have hterm : ∀ n : ℕ, (((((PowerSeries.rescale (-1 : ℤ)
      (PowerSeries.pentagonalSeries ℤ)).coeff n : ℤ))) : ℂ) * q ^ n
        = (PowerSeries.pentagonalSeries ℂ).coeff n * (-q) ^ n := by
    intro n
    rw [PowerSeries.coeff_rescale, Int.cast_mul, Int.cast_pow, Int.cast_neg,
      Int.cast_one, ← opc_coeff_pent_complex_eq]
    ring
  rw [tsum_congr hterm]
  exact heuler.tsum_eq

/-- Identity theorem for convergent power series. -/
private theorem opc_coeff_eq_zero_of_tsum_eq_zero (c : ℕ → ℂ) (r : ℝ)
    (hr : 0 < r) (hs : Summable fun n : ℕ => ‖c n‖ * r ^ n)
    (hz : ∀ q : ℂ, ‖q‖ < r → (∑' n : ℕ, c n * q ^ n) = 0) :
    ∀ n : ℕ, c n = 0 := by
  have hnorm : ∀ n : ℕ,
      ‖FormalMultilinearSeries.ofScalars ℂ c n‖ = ‖c n‖ :=
    fun n => FormalMultilinearSeries.ofScalars_norm ℂ c n
  set rnn : NNReal := ⟨r, hr.le⟩
  have hrr : (rnn : ℝ) = r := rfl
  have hs' : Summable fun n : ℕ =>
      ‖FormalMultilinearSeries.ofScalars ℂ c n‖ * (rnn : ℝ) ^ n := by
    rw [hrr]
    simp_rw [hnorm]
    exact hs
  have hle : ((rnn : ENNReal)) ≤ (FormalMultilinearSeries.ofScalars ℂ c).radius :=
    FormalMultilinearSeries.le_radius_of_summable_norm _ hs'
  have hpos : (0 : ENNReal) < ((rnn : ENNReal)) := by
    have h0 : (0 : NNReal) < rnn := hr
    exact_mod_cast h0
  have hrad : 0 < (FormalMultilinearSeries.ofScalars ℂ c).radius :=
    lt_of_lt_of_le hpos hle
  have hAt : HasFPowerSeriesAt (FormalMultilinearSeries.ofScalars ℂ c).sum
      (FormalMultilinearSeries.ofScalars ℂ c) 0 :=
    (FormalMultilinearSeries.hasFPowerSeriesOnBall _ hrad).hasFPowerSeriesAt
  have hval : ∀ q : ℂ, (FormalMultilinearSeries.ofScalars ℂ c).sum q
      = ∑' n : ℕ, c n * q ^ n := by
    intro q
    have e := FormalMultilinearSeries.ofScalars_sum_eq c q
    simp only [smul_eq_mul] at e
    exact e
  have hev : (FormalMultilinearSeries.ofScalars ℂ c).sum =ᶠ[nhds (0 : ℂ)] 0 := by
    filter_upwards [Metric.ball_mem_nhds (0 : ℂ) hr] with q hq
    have hqr : ‖q‖ < r := by
      have hmem : dist q 0 < r := hq
      rwa [dist_zero_right] at hmem
    rw [hval q]
    exact hz q hqr
  have hpeq : FormalMultilinearSeries.ofScalars ℂ c = 0 :=
    hAt.eq_zero_of_eventually hev
  intro n
  have h0n : FormalMultilinearSeries.ofScalars ℂ c n = 0 := by
    rw [hpeq]
    rfl
  exact (FormalMultilinearSeries.ofScalars_eq_zero (E := ℂ) n).mp h0n

/-- Theta coefficients are bounded by two in norm. -/
private theorem opc_theta_coeff_bound (m : ℕ) :
    ‖(((((opcTheta.coeff m : ℤ))) : ℂ))‖ ≤ 2 := by
  have hcard2 : Nat.card {x : ℤ // x.natAbs ^ 2 = m} ≤ 2 := by
    by_cases hne : Nonempty {x : ℤ // x.natAbs ^ 2 = m}
    · obtain ⟨a₀⟩ := hne
      have hmem : ∀ x : {x : ℤ // x.natAbs ^ 2 = m},
          x.val = a₀.val ∨ x.val = -a₀.val := by
        intro x
        have e1 : x.val.natAbs ^ 2 = a₀.val.natAbs ^ 2 := by
          rw [x.property, a₀.property]
        have e2 : x.val ^ 2 = a₀.val ^ 2 := by
          have hx : ((((x.val.natAbs ^ 2 : ℕ))) : ℤ) = x.val ^ 2 := by
            rw [Nat.cast_pow, Int.natAbs_sq]
          have ha : ((((a₀.val.natAbs ^ 2 : ℕ))) : ℤ) = a₀.val ^ 2 := by
            rw [Nat.cast_pow, Int.natAbs_sq]
          have e1c : ((((x.val.natAbs ^ 2 : ℕ))) : ℤ)
              = ((((a₀.val.natAbs ^ 2 : ℕ))) : ℤ) := by rw [e1]
          rw [hx, ha] at e1c
          exact e1c
        exact (sq_eq_sq_iff_eq_or_eq_neg (a := x.val) (b := a₀.val)).mp e2
      classical
      have hinj : Function.Injective (fun x : {x : ℤ // x.natAbs ^ 2 = m} =>
          if x.val = a₀.val then (0 : Fin 2) else 1) := by
        intro x y hxy
        by_cases hx : x.val = a₀.val <;> by_cases hy : y.val = a₀.val
        · exact Subtype.ext (by rw [hx, hy])
        · simp [hx, hy] at hxy
        · simp [hx, hy] at hxy
        · have hx' := (hmem x).resolve_left hx
          have hy' := (hmem y).resolve_left hy
          exact Subtype.ext (by rw [hx', hy'])
      have hfinT := opc_finite_intFiber m
      have hFT : Fintype {x : ℤ // x.natAbs ^ 2 = m} := Fintype.ofFinite _
      calc Nat.card {x : ℤ // x.natAbs ^ 2 = m}
          = Fintype.card {x : ℤ // x.natAbs ^ 2 = m} :=
            Nat.card_eq_fintype_card
        _ ≤ Fintype.card (Fin 2) := Fintype.card_le_of_injective _ hinj
        _ = 2 := Fintype.card_fin 2
    · have h0 : Nat.card {x : ℤ // x.natAbs ^ 2 = m} = 0 :=
        Nat.card_eq_zero.mpr (Or.inl ⟨fun t => hne ⟨t⟩⟩)
      omega
  rw [opc_theta_coeff_eq_card, Int.cast_natCast, Complex.norm_natCast]
  exact_mod_cast hcard2

/-- Norm bound for 2-expansion coefficients. -/
private theorem opc_norm_expand_coeff_le_one (n : ℕ) :
    ‖(((PowerSeries.expand 2 two_ne_zero
      (PowerSeries.pentagonalSeries ℤ)).coeff n : ℂ))‖ ≤ 1 := by
  by_cases hd : 2 ∣ n
  · obtain ⟨k, rfl⟩ := hd
    rw [PowerSeries.coeff_expand_mul]
    exact opc_norm_pentCoeff_le_one k
  · rw [PowerSeries.coeff_expand_of_not_dvd _ _ _ hd, Int.cast_zero, norm_zero]
    exact zero_le_one

/-- Norm bound for rescaled Euler coefficients. -/
private theorem opc_norm_rescale_coeff_le_one (n : ℕ) :
    ‖(((PowerSeries.rescale (-1 : ℤ)
      (PowerSeries.pentagonalSeries ℤ)).coeff n : ℂ))‖ ≤ 1 := by
  rw [PowerSeries.coeff_rescale, Int.cast_mul, Int.cast_pow, Int.cast_neg,
    Int.cast_one, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
  exact opc_norm_pentCoeff_le_one n

/-- Summability for the Gauss-identity difference at radius `1 / 2`. -/
private theorem opc_gauss_diff_summable :
    Summable fun n : ℕ => ‖((((opcTheta * PowerSeries.expand 2 two_ne_zero
      (PowerSeries.pentagonalSeries ℤ)).coeff n : ℤ)) : ℂ)
      - ((((PowerSeries.rescale (-1 : ℤ) (PowerSeries.pentagonalSeries ℤ)
        * PowerSeries.rescale (-1 : ℤ)
        (PowerSeries.pentagonalSeries ℤ)).coeff n : ℤ)) : ℂ)‖
      * (1 / 2 : ℝ) ^ n := by
  have hq0 : ‖(((1 / 2 : ℝ)) : ℂ)‖ = 1 / 2 := by
    rw [Complex.norm_real]
    norm_num
  have hq0lt : ‖(((1 / 2 : ℝ)) : ℂ)‖ < 1 := by rw [hq0]; norm_num
  have hTh := opc_summable_norm_series opcTheta 2 _ hq0lt
    (fun n => opc_theta_coeff_bound n)
  have hExp := opc_summable_norm_series _ 1 _ hq0lt
    (fun n => opc_norm_expand_coeff_le_one n)
  have hRe := opc_summable_norm_series _ 1 _ hq0lt
    (fun n => opc_norm_rescale_coeff_le_one n)
  obtain ⟨hLHS, hLHSn⟩ := opc_hasSum_mul_of_abs_summable _ _ _ hTh hExp
  obtain ⟨hRHS, hRHSn⟩ := opc_hasSum_mul_of_abs_summable _ _ _ hRe hRe
  have hsum := hLHSn.add hRHSn
  have hq0n : ∀ n : ℕ, ‖(((1 / 2 : ℝ)) : ℂ) ^ n‖ = (1 / 2 : ℝ) ^ n := by
    intro n
    rw [norm_pow, hq0]
  refine Summable.of_nonneg_of_le
    (fun n => mul_nonneg (norm_nonneg _) (pow_nonneg (by norm_num) _)) ?_ hsum
  intro n
  have hle : ‖((((opcTheta * PowerSeries.expand 2 two_ne_zero
        (PowerSeries.pentagonalSeries ℤ)).coeff n : ℤ)) : ℂ)
        - ((((PowerSeries.rescale (-1 : ℤ) (PowerSeries.pentagonalSeries ℤ)
          * PowerSeries.rescale (-1 : ℤ)
          (PowerSeries.pentagonalSeries ℤ)).coeff n : ℤ)) : ℂ)‖
        ≤ ‖((((opcTheta * PowerSeries.expand 2 two_ne_zero
          (PowerSeries.pentagonalSeries ℤ)).coeff n : ℤ)) : ℂ)‖
          + ‖((((PowerSeries.rescale (-1 : ℤ) (PowerSeries.pentagonalSeries ℤ)
          * PowerSeries.rescale (-1 : ℤ)
          (PowerSeries.pentagonalSeries ℤ)).coeff n : ℤ)) : ℂ)‖ :=
    norm_sub_le _ _
  calc ‖((((opcTheta * PowerSeries.expand 2 two_ne_zero
          (PowerSeries.pentagonalSeries ℤ)).coeff n : ℤ)) : ℂ)
          - ((((PowerSeries.rescale (-1 : ℤ) (PowerSeries.pentagonalSeries ℤ)
          * PowerSeries.rescale (-1 : ℤ)
          (PowerSeries.pentagonalSeries ℤ)).coeff n : ℤ)) : ℂ)‖
          * (1 / 2 : ℝ) ^ n
        ≤ (‖((((opcTheta * PowerSeries.expand 2 two_ne_zero
          (PowerSeries.pentagonalSeries ℤ)).coeff n : ℤ)) : ℂ)‖
          + ‖((((PowerSeries.rescale (-1 : ℤ) (PowerSeries.pentagonalSeries ℤ)
          * PowerSeries.rescale (-1 : ℤ)
          (PowerSeries.pentagonalSeries ℤ)).coeff n : ℤ)) : ℂ)‖)
          * (1 / 2 : ℝ) ^ n :=
        mul_le_mul_of_nonneg_right hle (pow_nonneg (by norm_num) _)
      _ = ‖((((opcTheta * PowerSeries.expand 2 two_ne_zero
          (PowerSeries.pentagonalSeries ℤ)).coeff n : ℤ)) : ℂ)‖
          * ‖(((1 / 2 : ℝ)) : ℂ) ^ n‖
          + ‖((((PowerSeries.rescale (-1 : ℤ) (PowerSeries.pentagonalSeries ℤ)
          * PowerSeries.rescale (-1 : ℤ)
          (PowerSeries.pentagonalSeries ℤ)).coeff n : ℤ)) : ℂ)‖
          * ‖(((1 / 2 : ℝ)) : ℂ) ^ n‖ := by
        rw [hq0n n]
        ring
      _ = ‖((((opcTheta * PowerSeries.expand 2 two_ne_zero
          (PowerSeries.pentagonalSeries ℤ)).coeff n : ℤ)) : ℂ)
          * (((1 / 2 : ℝ)) : ℂ) ^ n‖
          + ‖((((PowerSeries.rescale (-1 : ℤ) (PowerSeries.pentagonalSeries ℤ)
          * PowerSeries.rescale (-1 : ℤ)
          (PowerSeries.pentagonalSeries ℤ)).coeff n : ℤ)) : ℂ)
          * (((1 / 2 : ℝ)) : ℂ) ^ n‖ := by
        rw [norm_mul, norm_mul]

/-- The Gauss-identity difference evaluates to zero inside radius `1 / 2`. -/
private theorem opc_gauss_diff_tsum_eq_zero (q : ℂ) (hq : ‖q‖ < 1 / 2) :
    (∑' n : ℕ, (((((opcTheta * PowerSeries.expand 2 two_ne_zero
      (PowerSeries.pentagonalSeries ℤ)).coeff n : ℤ)) : ℂ)
      - ((((PowerSeries.rescale (-1 : ℤ) (PowerSeries.pentagonalSeries ℤ)
        * PowerSeries.rescale (-1 : ℤ)
        (PowerSeries.pentagonalSeries ℤ)).coeff n : ℤ)) : ℂ)) * q ^ n) = 0 := by
  have hq1 : ‖q‖ < 1 := lt_trans hq (by norm_num)
  have hTh := opc_summable_norm_series opcTheta 2 q hq1
    (fun n => opc_theta_coeff_bound n)
  have hExp := opc_summable_norm_series _ 1 q hq1
    (fun n => opc_norm_expand_coeff_le_one n)
  have hRe := opc_summable_norm_series _ 1 q hq1
    (fun n => opc_norm_rescale_coeff_le_one n)
  obtain ⟨hLHS, -⟩ := opc_hasSum_mul_of_abs_summable _ _ q hTh hExp
  obtain ⟨hRHS, -⟩ := opc_hasSum_mul_of_abs_summable _ _ q hRe hRe
  have h := hLHS.sub hRHS
  rw [opc_eval_thetaSeries q hq1, opc_eval_expand_two q hq1,
    opc_eval_rescale_neg q hq1] at h
  have hN4 := opc_tsum_sq_mul_eulerFunction_sq q hq1
  have h0 : (∑' n : ℤ, q ^ (n * n).toNat) * eulerFunction (q ^ 2)
      - eulerFunction (-q) * eulerFunction (-q) = 0 := by
    linear_combination hN4
  rw [h0] at h
  have h2 := h.congr_fun (fun n => sub_mul _ _ _)
  exact h2.tsum_eq

/-- Formal Gauss identity. -/
private theorem opc_theta_mul_expand_two :
    opcTheta * PowerSeries.expand 2 two_ne_zero (PowerSeries.pentagonalSeries ℤ)
      = (PowerSeries.rescale (-1 : ℤ)
        (PowerSeries.pentagonalSeries ℤ)) ^ 2 := by
  have hpow : (PowerSeries.rescale (-1 : ℤ) (PowerSeries.pentagonalSeries ℤ)) ^ 2
      = (PowerSeries.rescale (-1 : ℤ) (PowerSeries.pentagonalSeries ℤ))
        * (PowerSeries.rescale (-1 : ℤ) (PowerSeries.pentagonalSeries ℤ)) :=
    pow_two _
  rw [hpow]
  apply PowerSeries.ext
  intro n
  apply Int.cast_injective (α := ℂ)
  have hcz := opc_coeff_eq_zero_of_tsum_eq_zero
    (fun n : ℕ => ((((opcTheta * PowerSeries.expand 2 two_ne_zero
      (PowerSeries.pentagonalSeries ℤ)).coeff n : ℤ)) : ℂ)
      - ((((PowerSeries.rescale (-1 : ℤ) (PowerSeries.pentagonalSeries ℤ)
        * PowerSeries.rescale (-1 : ℤ)
        (PowerSeries.pentagonalSeries ℤ)).coeff n : ℤ)) : ℂ))
    (1 / 2 : ℝ) (by norm_num) opc_gauss_diff_summable
    (fun q hq => opc_gauss_diff_tsum_eq_zero q hq)
  have h0 := hcz n
  exact sub_eq_zero.mp h0

/-- The constant coefficient of the Euler product is one. -/
private theorem opc_pent_coeff_zero :
    (PowerSeries.pentagonalSeries ℤ).coeff 0 = 1 := by
  have h0 : pentagonal (0 : ℤ) = 0 := by
    rw [pentagonal_def]
    norm_num
  have h1 : Int.negOnePow (0 : ℤ) = 1 := by decide
  have h := PowerSeries.coeff_pentagonalSeries_pentagonal (R := ℤ) (0 : ℤ)
  rw [h0, h1] at h
  exact h

/-- Rescaling by `−1` fixes the 2-expansion of the Euler product. -/
private theorem opc_rescale_expand_two :
    PowerSeries.rescale (-1 : ℤ)
      (PowerSeries.expand 2 two_ne_zero (PowerSeries.pentagonalSeries ℤ))
      = PowerSeries.expand 2 two_ne_zero
        (PowerSeries.pentagonalSeries ℤ) := by
  apply PowerSeries.ext
  intro n
  rw [PowerSeries.coeff_rescale]
  by_cases hd : 2 ∣ n
  · obtain ⟨k, rfl⟩ := hd
    have h1 : (-1 : ℤ) ^ (2 * k) = 1 := Even.neg_one_pow ⟨k, by ring⟩
    rw [h1, one_mul]
  · have h0 : (PowerSeries.expand 2 two_ne_zero
        (PowerSeries.pentagonalSeries ℤ)).coeff n = 0 :=
      PowerSeries.coeff_expand_of_not_dvd _ _ _ hd
    rw [h0, mul_zero]

/-- Theta times the twisted overpartition series is one. -/
private theorem opc_theta_mul_rescale_genFun :
    opcTheta * PowerSeries.rescale (-1 : ℤ)
        (Nat.Partition.genFun (fun _ _ ↦ (2 : ℤ))) = 1 := by
  have hmap := congrArg (PowerSeries.rescale (-1 : ℤ))
    opc_genFun_two_mul_pentagonalSeries_sq
  rw [map_mul, map_pow, opc_rescale_expand_two] at hmap
  have hmul := congrArg (opcTheta * ·) hmap
  rw [← mul_assoc, opc_theta_mul_expand_two] at hmul
  have hbase : PowerSeries.rescale (-1 : ℤ)
      (PowerSeries.pentagonalSeries ℤ) ≠ 0 := by
    intro hcon
    have h0 : (PowerSeries.rescale (-1 : ℤ)
        (PowerSeries.pentagonalSeries ℤ)).coeff 0 = 0 := by
      rw [hcon]
      simp
    rw [PowerSeries.coeff_rescale, pow_zero, one_mul,
      opc_pent_coeff_zero] at h0
    exact one_ne_zero h0
  have hC : (PowerSeries.rescale (-1 : ℤ)
      (PowerSeries.pentagonalSeries ℤ)) ^ 2 ≠ 0 :=
    pow_ne_zero 2 hbase
  have hmul2 : (opcTheta * PowerSeries.rescale (-1 : ℤ)
        (Nat.Partition.genFun (fun _ _ ↦ (2 : ℤ))))
        * (PowerSeries.rescale (-1 : ℤ)
          (PowerSeries.pentagonalSeries ℤ)) ^ 2
        = 1 * (PowerSeries.rescale (-1 : ℤ)
          (PowerSeries.pentagonalSeries ℤ)) ^ 2 := by
    rw [one_mul]
    exact hmul
  exact mul_right_cancel₀ hC hmul2

/-- The mod-5 theta series. -/
private noncomputable def opcPhi5 : (ZMod 5)⟦X⟧ :=
  PowerSeries.map (Int.castRingHom (ZMod 5)) opcTheta

/-- The mod-5 twisted overpartition series. -/
private noncomputable def opcQ5 : (ZMod 5)⟦X⟧ :=
  PowerSeries.map (Int.castRingHom (ZMod 5)) (PowerSeries.rescale (-1 : ℤ)
    (Nat.Partition.genFun (fun _ _ ↦ (2 : ℤ))))


end MetaMathlibExt

end

@[expose] public section

namespace MetaMathlibExt

/--
**Overpartitions of $5n$ modulo $5$, explicit form.** For every integer $n \ge 1$, the number of
pairs $(P, S)$, where $P$ is a finite multiset of positive integers with sum $5n$ and $S$ is a
finite set of natural numbers each belonging to $P$, is congruent modulo $5$ to $(-1)^n$ times the
number of ordered triples $(x, y, z)$ of integers with $x^2 + y^2 + z^2 = n$.

These pairs encode the overpartitions of $5n$: $P$ is the multiset of parts and $S$ is the set of
overlined part sizes.

Proves `Wanted` entry `overpartition_mul_five_mod_five`.

Source: Liuquan Wang, "Another Proof of a Conjecture by Hirschhorn and Sellers on Overpartitions,"
Journal of Integer Sequences 17 (2014), Article 14.9.8,
Theorem (label thm1), lines 110–114.
`https://cs.uwaterloo.ca/journals/JIS/VOL17/Wang2/wang15.tex`
-/
public theorem overpartition_mul_five_mod_five
    (n : ℕ) (hn : 1 ≤ n) :
    Int.ModEq 5
      (Nat.card {
        p : Multiset ℕ × Finset ℕ //
          (∀ a ∈ p.1, 0 < a) ∧
          p.1.sum = 5 * n ∧
          ∀ a ∈ p.2, a ∈ p.1
      })
      (((-1 : ℤ) ^ n) * Nat.card {
        x : ℤ × ℤ × ℤ //
          x.1 ^ 2 + x.2.1 ^ 2 + x.2.2 ^ 2 = n
      }) := by
  obtain ⟨W, R₁, R₂, R₃, R₄, hR1, hR2, hR3, hR4, hdecomp⟩ :=
    opc_theta_pow_four_decomp
  have hfact : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hmap8 : opcPhi5 * opcQ5 = 1 := by
    have h := congrArg (PowerSeries.map (Int.castRingHom (ZMod 5)))
      opc_theta_mul_rescale_genFun
    rwa [map_mul, map_one] at h
  have hFrob : PowerSeries.expand 5 opc_five_ne_zero opcQ5 = opcQ5 ^ 5 := by
    have h0 : ((PowerSeries.expand 5 opc_five_ne_zero opcQ5).map
        (frobenius (ZMod 5) 5)) = opcQ5 ^ 5 :=
      PowerSeries.map_frobenius_expand 5 opc_five_ne_zero
    rw [ZMod.frobenius_zmod 5, PowerSeries.map_id] at h0
    exact h0
  have hQ : opcPhi5 ^ 4 * PowerSeries.expand 5 opc_five_ne_zero opcQ5
      = opcQ5 := by
    have h4 : opcPhi5 ^ 4 * opcQ5 ^ 5 = opcQ5 * (opcPhi5 * opcQ5) ^ 4 := by
      ring
    rw [hFrob, h4, hmap8, one_pow, mul_one]
  have hmap12 : opcPhi5 ^ 4
        = PowerSeries.expand 5 opc_five_ne_zero (opcPhi5 ^ 4)
          + (((PowerSeries.map (Int.castRingHom (ZMod 5)) R₁
            + PowerSeries.map (Int.castRingHom (ZMod 5)) R₂)
            + PowerSeries.map (Int.castRingHom (ZMod 5)) R₃)
            + PowerSeries.map (Int.castRingHom (ZMod 5)) R₄) := by
    have h := congrArg (PowerSeries.map (Int.castRingHom (ZMod 5))) hdecomp
    simp only [map_add, PowerSeries.map_expand, map_nsmul] at h
    rw [map_pow] at h
    have h5W : (5 : ℕ) • PowerSeries.map (Int.castRingHom (ZMod 5)) W
        = 0 := by
      have h5c : ∀ c : ZMod 5, (5 : ℕ) • c = 0 := by
        intro c
        rw [nsmul_eq_mul, ZMod.natCast_self, zero_mul]
      apply PowerSeries.ext
      intro k
      rw [map_nsmul]
      exact h5c _
    rw [h5W, add_zero] at h
    exact h
  have hz : ∀ (S : PowerSeries (ZMod 5)) (k : ZMod 5),
      opcSupportedMod (ZMod 5) 5 k S → k ≠ 0 →
        PowerSeries.coeff (5 * n)
          (S * PowerSeries.expand 5 opc_five_ne_zero opcQ5) = 0 := by
    intro S k hS hk
    have hE : opcSupportedMod (ZMod 5) 5 0
        (PowerSeries.expand 5 opc_five_ne_zero opcQ5) :=
      opc_supportedMod_expand 5 opc_five_ne_zero opcQ5
    have hP := opc_supportedMod_mul 5 k 0 _ _ hS hE
    have hk0 : k + 0 ≠ 0 := by simpa using hk
    have hNe : NeZero 5 := ⟨opc_five_ne_zero⟩
    exact opc_supportedMod_coeff_eq_zero 5 (k + 0) _ hP hk0 n
  have hk1 : (1 : ZMod 5) ≠ 0 := by
    intro h
    have h1 : (((1 : ℕ)) : ZMod 5) = 0 := by
      rw [Nat.cast_one]
      exact h
    exact absurd ((ZMod.natCast_eq_zero_iff 1 5).mp h1) (by omega)
  have hk2 : (2 : ZMod 5) ≠ 0 := by
    intro h
    have h2 : (((2 : ℕ)) : ZMod 5) = 0 := by simpa using h
    exact absurd ((ZMod.natCast_eq_zero_iff 2 5).mp h2) (by omega)
  have hk3 : (3 : ZMod 5) ≠ 0 := by
    intro h
    have h3 : (((3 : ℕ)) : ZMod 5) = 0 := by simpa using h
    exact absurd ((ZMod.natCast_eq_zero_iff 3 5).mp h3) (by omega)
  have hk4 : (4 : ZMod 5) ≠ 0 := by
    intro h
    have h4 : (((4 : ℕ)) : ZMod 5) = 0 := by simpa using h
    exact absurd ((ZMod.natCast_eq_zero_iff 4 5).mp h4) (by omega)
  have hz1 := hz _ (1 : ZMod 5)
    (opc_supportedMod_map (Int.castRingHom (ZMod 5)) 5 1 _ hR1) hk1
  have hz2 := hz _ (2 : ZMod 5)
    (opc_supportedMod_map (Int.castRingHom (ZMod 5)) 5 2 _ hR2) hk2
  have hz3 := hz _ (3 : ZMod 5)
    (opc_supportedMod_map (Int.castRingHom (ZMod 5)) 5 3 _ hR3) hk3
  have hz4 := hz _ (4 : ZMod 5)
    (opc_supportedMod_map (Int.castRingHom (ZMod 5)) 5 4 _ hR4) hk4
  have h43 : opcPhi5 ^ 4 * opcQ5 = opcPhi5 ^ 3 := by
    have e : opcPhi5 ^ 4 * opcQ5 = opcPhi5 ^ 3 * (opcPhi5 * opcQ5) := by
      ring
    rw [e, hmap8, mul_one]
  have e3 : PowerSeries.expand 5 opc_five_ne_zero (opcPhi5 ^ 4)
        * PowerSeries.expand 5 opc_five_ne_zero opcQ5
        = PowerSeries.expand 5 opc_five_ne_zero (opcPhi5 ^ 3) := by
    rw [← map_mul, h43]
  have hQeq : opcQ5 = PowerSeries.expand 5 opc_five_ne_zero (opcPhi5 ^ 3)
      + (((PowerSeries.map (Int.castRingHom (ZMod 5)) R₁
        * PowerSeries.expand 5 opc_five_ne_zero opcQ5
        + PowerSeries.map (Int.castRingHom (ZMod 5)) R₂
        * PowerSeries.expand 5 opc_five_ne_zero opcQ5)
        + PowerSeries.map (Int.castRingHom (ZMod 5)) R₃
        * PowerSeries.expand 5 opc_five_ne_zero opcQ5)
        + PowerSeries.map (Int.castRingHom (ZMod 5)) R₄
        * PowerSeries.expand 5 opc_five_ne_zero opcQ5) := by
    conv_lhs => rw [← hQ, hmap12]
    linear_combination e3
  have hcoeff : PowerSeries.coeff (5 * n) opcQ5
      = PowerSeries.coeff n (opcPhi5 ^ 3) := by
    rw [hQeq, map_add, map_add, map_add, map_add, hz1, hz2, hz3, hz4,
      PowerSeries.coeff_expand_mul]
    simp
  have hsign : (-1 : ZMod 5) ^ (5 * n) = (-1) ^ n := by
    rw [pow_mul, show ((-1 : ZMod 5) ^ 5) = -1 from Odd.neg_one_pow ⟨2, rfl⟩]
  have hLHS : PowerSeries.coeff (5 * n) opcQ5
      = (-1 : ZMod 5) ^ n
        * (Int.castRingHom (ZMod 5)) (PowerSeries.coeff (5 * n)
          (Nat.Partition.genFun (fun _ _ ↦ (2 : ℤ)))) := by
    unfold opcQ5
    rw [PowerSeries.coeff_map, PowerSeries.coeff_rescale, map_mul, map_pow,
      map_neg, map_one, hsign]
  have hRHS : PowerSeries.coeff n (opcPhi5 ^ 3)
      = (Int.castRingHom (ZMod 5)) (PowerSeries.coeff n (opcTheta ^ 3)) := by
    unfold opcPhi5
    rw [← map_pow, PowerSeries.coeff_map]
  have hN1 := opc_overpartition_card_eq_coeff_genFun (5 * n)
  have hN3 := opc_coeff_theta_cube n
  rw [← hN1] at hLHS
  rw [hN3] at hRHS
  -- hLHS : coeff-Q = (-1)^n * π ↑(card (opcOver (5n)))
  -- hRHS : coeff-Φ³ = π ↑(card three-sq)
  have hcomb : (-1 : ZMod 5) ^ n
        * (Int.castRingHom (ZMod 5))
          ((Nat.card (opcOver (5 * n)) : ℕ) : ℤ)
      = (Int.castRingHom (ZMod 5))
        ((Nat.card {x : ℤ × ℤ × ℤ //
          x.1 ^ 2 + x.2.1 ^ 2 + x.2.2 ^ 2 = (n : ℤ)} : ℕ) : ℤ) := by
    rw [← hLHS, ← hRHS]
    exact hcoeff
  have h2n : (-1 : ZMod 5) ^ n * (-1) ^ n = 1 := by
    rw [← pow_add, show n + n = 2 * n from by ring, pow_mul,
      show ((-1 : ZMod 5) ^ 2) = 1 from Even.neg_one_pow ⟨1, rfl⟩, one_pow]
  have hmain : (Int.castRingHom (ZMod 5))
        ((Nat.card (opcOver (5 * n)) : ℕ) : ℤ)
      = (-1 : ZMod 5) ^ n * (Int.castRingHom (ZMod 5))
        ((Nat.card {x : ℤ × ℤ × ℤ //
          x.1 ^ 2 + x.2.1 ^ 2 + x.2.2 ^ 2 = (n : ℤ)} : ℕ) : ℤ) := by
    calc (Int.castRingHom (ZMod 5))
            ((Nat.card (opcOver (5 * n)) : ℕ) : ℤ)
        = ((-1 : ZMod 5) ^ n * (-1) ^ n)
          * (Int.castRingHom (ZMod 5))
            ((Nat.card (opcOver (5 * n)) : ℕ) : ℤ) := by
          rw [h2n, one_mul]
      _ = (-1 : ZMod 5) ^ n * (((-1 : ZMod 5) ^ n
          * (Int.castRingHom (ZMod 5))
            ((Nat.card (opcOver (5 * n)) : ℕ) : ℤ))) := by
          rw [mul_assoc]
      _ = _ := by rw [← hcomb]
  have hOverEq : opcOver (5 * n) = { p : Multiset ℕ × Finset ℕ //
      (∀ a ∈ p.1, 0 < a) ∧ p.1.sum = 5 * n ∧ ∀ a ∈ p.2, a ∈ p.1 } := rfl
  have hcard : ((Nat.card { p : Multiset ℕ × Finset ℕ //
      (∀ a ∈ p.1, 0 < a) ∧ p.1.sum = 5 * n ∧ ∀ a ∈ p.2, a ∈ p.1 } : ℕ) : ℤ)
      = ((Nat.card (opcOver (5 * n)) : ℕ) : ℤ) := by
    rw [← hOverEq]
  have eNeg : (-1 : ZMod 5) ^ n
      = (Int.castRingHom (ZMod 5)) (((-1 : ℤ) ^ n)) := by
    rw [map_pow, map_neg, map_one]
  have hfin : ((((Nat.card (opcOver (5 * n)) : ℕ)) : ZMod 5))
      = ((((-1 : ℤ) ^ n * ((Nat.card {x : ℤ × ℤ × ℤ //
          x.1 ^ 2 + x.2.1 ^ 2 + x.2.2 ^ 2 = (n : ℤ)} : ℕ) : ℤ) : ℤ))
        : ZMod 5) := by
    have h := hmain
    rw [eNeg, ← map_mul] at h
    exact h
  rw [hcard]
  exact (ZMod.intCast_eq_intCast_iff _ _ _).mp hfin

end MetaMathlibExt

namespace Nat
namespace Overpartition

/-- **Overpartitions as pairs of a multiset and a set.** For every natural number $m$, the number
of overpartitions of $m$ equals the number of pairs $(P, S)$ in which $P$ is a finite multiset of
positive integers with sum $m$ and $S$ is a finite set of natural numbers each belonging to $P$. -/
public lemma natCard_eq_card_subtype (m : ℕ) :
    Nat.card (Nat.Overpartition m) =
      Nat.card { p : Multiset ℕ × Finset ℕ //
        (∀ a ∈ p.1, 0 < a) ∧ p.1.sum = m ∧ ∀ a ∈ p.2, a ∈ p.1 } := by
  apply Nat.card_congr
  exact
    { toFun := fun O =>
        ⟨(O.toPartition.parts, O.overlines), fun a ha => O.toPartition.parts_pos ha,
          O.toPartition.parts_sum,
          fun a ha => Multiset.mem_toFinset.mp (O.overlines_subset ha)⟩
      invFun := fun p =>
        { toPartition :=
            { parts := p.val.1
              parts_pos := fun {a} ha => p.property.1 a ha
              parts_sum := p.property.2.1 }
          overlines := p.val.2
          overlines_subset := fun a ha =>
            Multiset.mem_toFinset.mpr (p.property.2.2 a ha) }
      left_inv := fun O => by
        obtain ⟨P, S, hsub⟩ := O
        obtain ⟨M, hpos, hsum⟩ := P
        apply Nat.Overpartition.ext
        · apply Nat.Partition.ext
          rfl
        · rfl
      right_inv := fun p => by
        obtain ⟨⟨M, S⟩, hpos, hsum, hsub⟩ := p
        apply Subtype.ext
        apply Prod.ext
        · rfl
        · rfl }

end Overpartition
end Nat

namespace Nat

/-- **The three-square count counts all integer solutions.** For every natural number $n$, the
three-square representation count $r_3(n)$ equals the number of ordered triples $(x, y, z)$ of
integers with $x^2 + y^2 + z^2 = n$. -/
public lemma threeSquareRepresentationCount_eq_natCard (n : ℕ) :
    threeSquareRepresentationCount n =
      Nat.card { x : ℤ × ℤ × ℤ //
        x.1 ^ 2 + x.2.1 ^ 2 + x.2.2 ^ 2 = (n : ℤ) } := by
  have single : ∀ w y z : ℤ, w ^ 2 + y ^ 2 + z ^ 2 = (n : ℤ) →
      w ∈ Finset.Icc (-(n : ℤ)) (n : ℤ) := by
    intro w y z h
    rw [Finset.mem_Icc]
    have hby : 0 ≤ y ^ 2 := sq_nonneg y
    have hbz : 0 ≤ z ^ 2 := sq_nonneg z
    have hle : w ^ 2 ≤ (n : ℤ) := by omega
    have h1 : w ≤ w ^ 2 := Int.le_self_sq w
    have h2 : -w ≤ (-w) ^ 2 := Int.le_self_sq (-w)
    have hneg : (-w) ^ 2 = w ^ 2 := by ring
    rw [hneg] at h2
    constructor <;> omega
  have hbound : ∀ p : (ℤ × ℤ) × ℤ,
      p.1.1 ^ 2 + p.1.2 ^ 2 + p.2 ^ 2 = (n : ℤ) →
      p.1.1 ∈ Finset.Icc (-(n : ℤ)) (n : ℤ) ∧
        p.1.2 ∈ Finset.Icc (-(n : ℤ)) (n : ℤ) ∧
        p.2 ∈ Finset.Icc (-(n : ℤ)) (n : ℤ) := by
    intro p h
    refine ⟨single p.1.1 p.1.2 p.2 h, ?_, ?_⟩
    · have h' : p.1.2 ^ 2 + p.1.1 ^ 2 + p.2 ^ 2 = (n : ℤ) := by
        linear_combination h
      exact single p.1.2 p.1.1 p.2 h'
    · have h'' : p.2 ^ 2 + p.1.1 ^ 2 + p.1.2 ^ 2 = (n : ℤ) := by
        linear_combination h
      exact single p.2 p.1.1 p.1.2 h''
  have eAssoc : { x : ℤ × ℤ × ℤ //
        x.1 ^ 2 + x.2.1 ^ 2 + x.2.2 ^ 2 = (n : ℤ) } ≃
      { p : (ℤ × ℤ) × ℤ //
        p.1.1 ^ 2 + p.1.2 ^ 2 + p.2 ^ 2 = (n : ℤ) } :=
    (Equiv.subtypeEquiv (Equiv.prodAssoc ℤ ℤ ℤ) (fun p => Iff.rfl)).symm
  have eFilter : { p : (ℤ × ℤ) × ℤ //
        p.1.1 ^ 2 + p.1.2 ^ 2 + p.2 ^ 2 = (n : ℤ) } ≃
      ↥(Finset.filter
        (fun p : (ℤ × ℤ) × ℤ =>
          p.1.1 ^ 2 + p.1.2 ^ 2 + p.2 ^ 2 = (n : ℤ))
        (Finset.product
          (Finset.product
            (Finset.Icc (-(n : ℤ)) (n : ℤ))
            (Finset.Icc (-(n : ℤ)) (n : ℤ)))
          (Finset.Icc (-(n : ℤ)) (n : ℤ)))) := by
    apply Equiv.subtypeEquiv (Equiv.refl _)
    intro p
    simp only [Equiv.refl_apply]
    constructor
    · intro h
      rw [Finset.mem_filter]
      obtain ⟨ha, hb, hc⟩ := hbound p h
      refine ⟨?_, h⟩
      exact Finset.mem_product.mpr
        ⟨Finset.mem_product.mpr ⟨ha, hb⟩, hc⟩
    · intro h
      exact (Finset.mem_filter.mp h).2
  unfold threeSquareRepresentationCount
  rw [← Nat.card_eq_finsetCard]
  exact Nat.card_congr (eFilter.symm.trans eAssoc.symm)

end Nat

namespace MetaMathlibExt

/-- **Overpartitions of $5n$ modulo $5$.** For every integer $n \ge 1$, the number of
overpartitions of $5n$ is congruent modulo $5$ to $(-1)^n r_3(n)$, where $r_3(n)$ is the number of
ordered triples $(x, y, z)$ of integers with $x^2 + y^2 + z^2 = n$. -/
public theorem overpartition_card_mul_five_modEq (n : ℕ) (hn : 1 ≤ n) :
    Int.ModEq 5 (Nat.card (Nat.Overpartition (5 * n)))
      (((-1 : ℤ) ^ n) * Nat.threeSquareRepresentationCount n) := by
  rw [Nat.Overpartition.natCard_eq_card_subtype,
    Nat.threeSquareRepresentationCount_eq_natCard]
  exact overpartition_mul_five_mod_five n hn

end MetaMathlibExt
