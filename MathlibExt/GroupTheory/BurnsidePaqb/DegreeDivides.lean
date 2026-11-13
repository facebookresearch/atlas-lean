/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.GroupTheory.BurnsidePaqb.KillingLemma

/-!
Degree-divides-order stage of the complete Burnside proof.

Authors: Muse Spark 1.3, @toskua, Avocado
Source archive: genai_web_search/tree/users/akiezun/burnside_proof.zip
SHA-256: d9da7df82e467d9fa587892eeef9f51e2b83df0588175653bd1d16264b09dd00

This module is mechanically ported from the audited source `extracted/Burnside/DegreeDivides.lean`.
-/

namespace BurnsidePaqb

@[expose] public section

variable {G : Type*} [Group G] [Fintype G]

/-- **Self-orthogonality of an irreducible character.** Let $\rho$ be an irreducible representation
of a finite group $G$ on a finite-dimensional complex vector space, with character $\chi$. Then
$\sum_{g \in G} \chi(g)\chi(g^{-1}) = |G|$. -/
theorem self_pair_sum {V : Type*} [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] (ρ : Representation ℂ G V)
    [Representation.IsIrreducible ρ] :
    ∑ g : G, ρ.character g * ρ.character g⁻¹ = (Nat.card G : ℂ) := by
  classical
  have : Nonempty G := ⟨1⟩
  have hpos : 0 < Nat.card G := Nat.card_pos
  have hc : (Nat.card G : ℂ) ≠ 0 := by exact_mod_cast hpos.ne'
  have : Invertible (Nat.card G : ℂ) := invertibleOfNonzero hc
  have hne : Nonempty (ρ.Equiv ρ) := ⟨Representation.Equiv.refl ρ⟩
  have h := Representation.char_orthonormal ρ ρ
  rw [ite_eq_left hne] at h
  have key : (Nat.card G : ℂ)⁻¹ * (∑ g : G, ρ.character g * ρ.character g⁻¹) = 1 := by
    simpa using h
  calc ∑ g : G, ρ.character g * ρ.character g⁻¹
      = (Nat.card G : ℂ)
          * ((Nat.card G : ℂ)⁻¹ * ∑ g : G, ρ.character g * ρ.character g⁻¹) := by
        rw [← mul_assoc, mul_inv_cancel₀ hc, one_mul]
    _ = (Nat.card G : ℂ) := by rw [key, mul_one]

open Classical in
/-- **Splitting a sum over conjugacy classes.** For a finite group $G$ and every function
$f : G \to \mathbb{C}$, $\sum_{g \in G} f(g) = \sum_{l} \sum_{x \in l} f(x)$, where $l$ runs over
the conjugacy classes of $G$. -/
theorem sum_over_classes (f : G → ℂ) :
    ∑ g : G, f g
      = ∑ l : ConjClasses G, ∑ x ∈ (ConjClasses.carrier l).toFinset, f x := by
  let fiberEquiv (l : ConjClasses G) :
      ↥((ConjClasses.carrier l).toFinset) ≃ {x : G // ConjClasses.mk x = l} :=
    Set.equivOfEq (by
      ext x
      simp [ConjClasses.carrier_eq_preimage_mk]
      rfl)
  let e : (Σ l : ConjClasses G,
      ↥((ConjClasses.carrier l).toFinset)) ≃ G :=
    (Equiv.sigmaCongrRight fiberEquiv).trans
      (Equiv.sigmaFiberEquiv ConjClasses.mk)
  have h1 : ∑ p : (Σ l : ConjClasses G,
      ↥((ConjClasses.carrier l).toFinset)), f p.2.1 = ∑ g : G, f g := by
    exact Fintype.sum_equiv e (fun p => f p.2.1) f (fun p => by rfl)
  rw [← h1, Fintype.sum_sigma]
  refine Finset.sum_congr rfl (fun l _ => ?_)
  exact Finset.sum_coe_sort _ _

open Classical in
/-- **Members of a conjugacy class are conjugate to its representative.** Let $l$ be a conjugacy
class of a finite group $G$ and $g_l$ its chosen representative. For every $x \in l$ there is
$c \in G$ with $c x c^{-1} = g_l$. -/
theorem conj_to_rep (l : ConjClasses G) (x : G)
    (hx : x ∈ (ConjClasses.carrier l).toFinset) :
    ∃ c : G, c * x * c⁻¹ = classRep l := by
  have hmem : x ∈ ConjClasses.carrier l := Set.mem_toFinset.mp hx
  have hmk : ConjClasses.mk x = l := ConjClasses.mem_carrier_iff_mk_eq.mp hmem
  have hrep : ConjClasses.mk (classRep l) = l := classRep_spec l
  have hconj : IsConj x (classRep l) :=
    ConjClasses.mk_eq_mk_iff_isConj.mp (by rw [hmk, hrep])
  exact isConj_iff.mp hconj

open Classical in
/-- **Characters are constant on conjugacy classes.** Let $\rho$ be a representation of a finite
group $G$ on a finite-dimensional complex vector space, with character $\chi$, and let $g_l$ be the
chosen representative of a conjugacy class $l$ of $G$. Then $\chi(x) = \chi(g_l)$ for every
$x \in l$. -/
theorem char_eq_of_mem_carrier {V : Type*} [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] (ρ : Representation ℂ G V) (l : ConjClasses G)
    (x : G) (hx : x ∈ (ConjClasses.carrier l).toFinset) :
    ρ.character x = ρ.character (classRep l) := by
  obtain ⟨c, hc⟩ := conj_to_rep l x hx
  have hcc := Representation.char_conj ρ x c
  rw [hc] at hcc
  exact hcc.symm

open Classical in
/-- **Characters at inverses are constant on conjugacy classes.** Let $\rho$ be a representation
of a finite group $G$ on a finite-dimensional complex vector space, with character $\chi$, and let
$g_l$ be the chosen representative of a conjugacy class $l$ of $G$. Then
$\chi(x^{-1}) = \chi(g_l^{-1})$ for every $x \in l$. -/
theorem char_inv_eq_of_mem_carrier {V : Type*} [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] (ρ : Representation ℂ G V) (l : ConjClasses G)
    (x : G) (hx : x ∈ (ConjClasses.carrier l).toFinset) :
    ρ.character x⁻¹ = ρ.character (classRep l)⁻¹ := by
  obtain ⟨c, hc⟩ := conj_to_rep l x hx
  have hinv : c * x⁻¹ * c⁻¹ = (classRep l)⁻¹ := by rw [← hc]; group
  have hcc := Representation.char_conj ρ x⁻¹ c
  rw [hinv] at hcc
  exact hcc.symm

open Classical in
/-- **Contribution of a conjugacy class to the self-pairing sum.** Let $\rho$ be an irreducible
representation of a finite group $G$ on a finite-dimensional complex vector space $V$, with
character $\chi$. For a conjugacy class $l$ of $G$, let $g_l$ be its chosen representative and
$\omega(l)$ the central scalar of $l$, the scalar by which the class sum of $l$ acts on $V$. Then
$\sum_{x \in l} \chi(x)\chi(x^{-1}) = (\dim_{\mathbb{C}} V)\,\omega(l)\,\chi(g_l^{-1})$. -/
theorem class_inner_sum {V : Type*} [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] (ρ : Representation ℂ G V)
    [Representation.IsIrreducible ρ] (l : ConjClasses G) :
    ∑ x ∈ (ConjClasses.carrier l).toFinset, ρ.character x * ρ.character x⁻¹
      = (Module.finrank ℂ V : ℂ)
        * (centralScalar ρ l * ρ.character (classRep l)⁻¹) := by
  have h1 : ∀ x ∈ (ConjClasses.carrier l).toFinset,
      ρ.character x * ρ.character x⁻¹
        = ρ.character (classRep l) * ρ.character (classRep l)⁻¹ := by
    intro x hx
    rw [char_eq_of_mem_carrier ρ l x hx, char_inv_eq_of_mem_carrier ρ l x hx]
  have hsum : ∑ x ∈ (ConjClasses.carrier l).toFinset, ρ.character x
      = ((ConjClasses.carrier l).toFinset.card : ℂ) * ρ.character (classRep l) := by
    rw [Finset.sum_congr rfl (fun x hx => char_eq_of_mem_carrier ρ l x hx),
      Finset.sum_const, nsmul_eq_mul]
  have htrace := centralScalar_trace ρ l
  rw [hsum] at htrace
  calc ∑ x ∈ (ConjClasses.carrier l).toFinset, ρ.character x * ρ.character x⁻¹
      = ∑ _x ∈ (ConjClasses.carrier l).toFinset,
          (ρ.character (classRep l) * ρ.character (classRep l)⁻¹) :=
        Finset.sum_congr rfl h1
    _ = ((ConjClasses.carrier l).toFinset.card : ℂ)
          * (ρ.character (classRep l) * ρ.character (classRep l)⁻¹) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ = (Module.finrank ℂ V : ℂ)
          * (centralScalar ρ l * ρ.character (classRep l)⁻¹) := by
        have h2 : ((ConjClasses.carrier l).toFinset.card : ℂ)
              * ρ.character (classRep l)
            = centralScalar ρ l * Module.finrank ℂ V := htrace.symm
        linear_combination h2 * ρ.character (classRep l)⁻¹

/-- **Degrees of irreducible representations divide the group order.** Let $\rho$ be an
irreducible representation of a finite group $G$ on a nonzero finite-dimensional complex vector
space $V$. Then $\dim_{\mathbb{C}} V$ divides $|G|$.

Source: Bielefeld Corollary 2. -/
theorem degree_dvd_card {V : Type*} [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] [Nontrivial V] (ρ : Representation ℂ G V)
    [Representation.IsIrreducible ρ] :
    Module.finrank ℂ V ∣ Fintype.card G := by
  classical
  have hpos : 0 < Module.finrank ℂ V := Module.finrank_pos
  have hdC : (Module.finrank ℂ V : ℂ) ≠ 0 := by exact_mod_cast hpos.ne'
  have hST : (Nat.card G : ℂ) = (Module.finrank ℂ V : ℂ) *
      (∑ l : ConjClasses G, centralScalar ρ l * ρ.character (classRep l)⁻¹) := by
    have hself : ∑ g : G, ρ.character g * ρ.character g⁻¹ = (Nat.card G : ℂ) :=
      self_pair_sum ρ
    have hdecomp := sum_over_classes (fun g => ρ.character g * ρ.character g⁻¹)
    rw [← hself, hdecomp, Finset.mul_sum]
    exact Finset.sum_congr rfl (fun l _ => class_inner_sum ρ l)
  have hTint : IsIntegral ℤ
      (∑ l : ConjClasses G, centralScalar ρ l * ρ.character (classRep l)⁻¹) :=
    IsIntegral.sum _ (fun l _ =>
      (centralScalar_isIntegral ρ l).mul (character_isIntegral ρ _))
  have hdiv : (∑ l : ConjClasses G, centralScalar ρ l * ρ.character (classRep l)⁻¹)
      = (Nat.card G : ℂ) / (Module.finrank ℂ V : ℂ) := by
    have h1 : (∑ l : ConjClasses G, centralScalar ρ l * ρ.character (classRep l)⁻¹)
        * (Module.finrank ℂ V : ℂ) = (Nat.card G : ℂ) := by
      rw [mul_comm]
      exact hST.symm
    exact (eq_div_iff hdC).mpr h1
  set q : ℚ := (Nat.card G : ℚ) / (Module.finrank ℂ V : ℚ) with hqdef
  have hqC : ((q : ℚ) : ℂ)
      = (∑ l : ConjClasses G, centralScalar ρ l * ρ.character (classRep l)⁻¹) := by
    rw [hqdef]
    push_cast
    exact hdiv.symm
  have hqintC : IsIntegral ℤ ((q : ℚ) : ℂ) := by
    rw [hqC]
    exact hTint
  have : IsScalarTower ℤ ℚ ℂ := IsScalarTower.of_algebraMap_eq fun x => by simp
  have hqint : IsIntegral ℤ q :=
    (isIntegral_algebraMap_iff (R := ℤ) (A := ℚ) (B := ℂ)).mp (by simpa using hqintC)
  have : IsIntegrallyClosed ℤ := GCDMonoid.toIsIntegrallyClosed
  obtain ⟨n, hn⟩ := (isIntegrallyClosed_iff ℚ).mp inferInstance hqint
  have hcast : (n : ℚ) = q := by simpa using hn
  have hdq : (Module.finrank ℂ V : ℚ) ≠ 0 := by exact_mod_cast hpos.ne'
  have hmul : (n : ℚ) * (Module.finrank ℂ V : ℚ) = (Nat.card G : ℚ) := by
    rw [hcast, hqdef, div_mul_cancel₀ _ hdq]
  have hmulZ : n * (Module.finrank ℂ V : ℤ) = (Nat.card G : ℤ) := by
    exact_mod_cast hmul
  have hdvd : (Module.finrank ℂ V : ℤ) ∣ (Nat.card G : ℤ) :=
    ⟨n, by rw [mul_comm]; exact hmulZ.symm⟩
  have hfin : Module.finrank ℂ V ∣ Nat.card G := Int.natCast_dvd_natCast.mp hdvd
  rwa [Fintype.card_eq_nat_card]

end

end BurnsidePaqb
