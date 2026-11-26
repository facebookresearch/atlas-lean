/-
Copyright (c) 2026 Avocado. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Avocado
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.Algebra.GradedMonoid
public import Mathlib.CategoryTheory.Monoidal.Closed.Braided
public import MathlibExt.Algebra.Homology.GradedPairingHomology

/-!
# Unit and associativity laws of homology pairings

For a graded pairing of natural-index module cochain complexes, the pairing of cycle classes
is the homology class of their cycle pairing. The inclusion of that cycle pairing in the
target chain term agrees with the chain-level pairing.

A degree-zero cycle gives a homology unit class. If it satisfies left and right unit
identities on cycles, its class satisfies those identities in the graded homology family.
Associativity on chain terms, with the degree-transport isomorphism for natural addition,
descends to associativity of the graded homology pairing.
-/

@[expose] public section

open CategoryTheory Limits MonoidalCategory

noncomputable section

universe u

namespace HomologicalComplex.CochainGradedPairing

variable (R : Type u) [CommRing R]

/-- Homology pairing of cycle classes is the paired cycle class.

For cycles `x` in degree `p` and `y` in degree `q`, pairing their homology classes equals the
homology projection of `P.pairCycles p q (x ⊗ y)` in degree `p + q`. -/
@[simp]
lemma pairHomology_π_apply
    {K₁ K₂ K₃ : CochainComplex (ModuleCat.{u} R) ℕ}
    (P : CochainGradedPairing K₁ K₂ K₃) (p q : ℕ)
    (x : K₁.cycles p) (y : K₂.cycles q) :
    (P.pairHomology p q).hom
        ((K₁.homologyπ p).hom x ⊗ₜ[R] (K₂.homologyπ q).hom y) =
      (K₃.homologyπ (p + q)).hom ((P.pairCycles p q).hom (x ⊗ₜ[R] y)) := by
  have h := ConcreteCategory.congr_hom
    (tensor_homologyπ_comp_pairHomology P p q) (x ⊗ₜ[R] y)
  exact h

/-- Cycle pairing agrees with the chain pairing after inclusion.

Include the paired cycles in the target term of degree `p + q`. This equals the chain pairing
applied to the two cycle inclusions. -/
@[simp]
lemma pairCycles_i_apply
    {K₁ K₂ K₃ : CochainComplex (ModuleCat.{u} R) ℕ}
    (P : CochainGradedPairing K₁ K₂ K₃) (p q : ℕ)
    (x : K₁.cycles p) (y : K₂.cycles q) :
    (K₃.iCycles (p + q)).hom ((P.pairCycles p q).hom (x ⊗ₜ[R] y)) =
      (P.pair p q).hom ((K₁.iCycles p).hom x ⊗ₜ[R] (K₂.iCycles q).hom y) := by
  have h := ConcreteCategory.congr_hom (P.pairCycles_i p q) (x ⊗ₜ[R] y)
  exact h

/-- Homology class of a degree-zero cycle.

For `e : K.cycles 0`, `homologyUnitClass R e` is the image of `e` under the degree-zero
homology projection. -/
noncomputable def homologyUnitClass
    {K : CochainComplex (ModuleCat.{u} R) ℕ} (e : K.cycles 0) : K.homology 0 :=
  (K.homologyπ 0).hom e

/-- Degree-zero cycle classes commute with cochain maps.

For a cochain map `f : K ⟶ L`, its degree-zero homology map sends the class of `e` to the
class of `cyclesMap f 0 e`. -/
@[simp]
lemma homologyUnitClass_map {K L : CochainComplex (ModuleCat.{u} R) ℕ}
    (f : K ⟶ L) (e : K.cycles 0) :
    (homologyMap f 0).hom (homologyUnitClass R e) =
      homologyUnitClass R ((cyclesMap f 0).hom e) := by
  change (homologyMap f 0).hom ((K.homologyπ 0).hom e) =
    (L.homologyπ 0).hom ((cyclesMap f 0).hom e)
  exact ConcreteCategory.congr_hom (homologyπ_naturality f 0) e

private noncomputable def cyclesTransportAddHom
    {K : CochainComplex (ModuleCat.{u} R) ℕ} {p q : ℕ} (h : p = q) :
    K.cycles p →+ K.cycles q where
  toFun x := cast (congrArg (fun n => ↥(K.cycles n)) h) x
  map_zero' := by subst h; rfl
  map_add' x y := by subst h; rfl

private noncomputable def homologyTransportAddHom
    {K : CochainComplex (ModuleCat.{u} R) ℕ} {p q : ℕ} (h : p = q) :
    K.homology p →+ K.homology q where
  toFun x := cast (congrArg (fun n => ↥(K.homology n)) h) x
  map_zero' := by subst h; rfl
  map_add' x y := by subst h; rfl

private lemma homologyπ_transport
    {K : CochainComplex (ModuleCat.{u} R) ℕ} {p q : ℕ} (h : p = q)
    (x : K.cycles p) :
    (homologyTransportAddHom R (K := K) h) ((K.homologyπ p).hom x) =
      (K.homologyπ q).hom ((cyclesTransportAddHom R h) x) := by
  cases h
  rfl

private lemma iCycles_transport
    {K : CochainComplex (ModuleCat.{u} R) ℕ} {p q : ℕ} (h : p = q)
    (x : K.cycles p) :
    (K.iCycles q).hom ((cyclesTransportAddHom R (K := K) h) x) =
      (K.XIsoOfEq h).hom.hom ((K.iCycles p).hom x) := by
  subst h
  simp [cyclesTransportAddHom]

/-- Left cycle unit gives a left unit on graded homology classes.

If a degree-zero cycle `e` is a left unit for the chain pairing on every cycle, after `0 + q =
q` transport, then pairing its homology class with any degree-`q` class gives that class in
the graded homology family. -/
lemma pairHomology_one_mul_mk
    {K : CochainComplex (ModuleCat.{u} R) ℕ}
    (P : CochainGradedPairing K K K)
    (e : K.cycles 0)
    (hleft : ∀ (q : ℕ) (y : K.cycles q),
      (K.XIsoOfEq (Nat.zero_add q)).hom.hom
          ((P.pair 0 q).hom ((K.iCycles 0).hom e ⊗ₜ[R] (K.iCycles q).hom y)) =
        (K.iCycles q).hom y)
    (q : ℕ) (y : K.homology q) :
    (GradedMonoid.mk (0 + q)
        ((P.pairHomology 0 q).hom (homologyUnitClass R e ⊗ₜ[R] y)) :
      GradedMonoid (fun n ↦ K.homology n)) =
      GradedMonoid.mk q y := by
  obtain ⟨y₀, rfl⟩ := (ModuleCat.epi_iff_surjective (K.homologyπ q)).mp inferInstance y
  have h_eq : (0 + q) = q := Nat.zero_add q
  have h_pair : (P.pairHomology 0 q).hom
        (homologyUnitClass R e ⊗ₜ[R] (K.homologyπ q).hom y₀) =
      (K.homologyπ (0 + q)).hom ((P.pairCycles 0 q).hom (e ⊗ₜ[R] y₀)) := by
    unfold homologyUnitClass
    exact pairHomology_π_apply R P 0 q e y₀
  have h_cyc : (cyclesTransportAddHom R h_eq)
      ((P.pairCycles 0 q).hom (e ⊗ₜ[R] y₀)) = y₀ := by
    apply (ModuleCat.mono_iff_injective (f := K.iCycles q)).mp inferInstance
    rw [iCycles_transport R h_eq]
    rw [pairCycles_i_apply R]
    exact hleft q y₀
  have h_hom : (homologyTransportAddHom R h_eq)
      ((P.pairHomology 0 q).hom
        (homologyUnitClass R e ⊗ₜ[R] (K.homologyπ q).hom y₀)) =
      (K.homologyπ q).hom y₀ := by
    rw [h_pair, homologyπ_transport R h_eq, h_cyc]
  have h_heq : HEq
      ((P.pairHomology 0 q).hom
        (homologyUnitClass R e ⊗ₜ[R] (K.homologyπ q).hom y₀))
      ((K.homologyπ q).hom y₀) := by
    have h2 : HEq
        ((P.pairHomology 0 q).hom
          (homologyUnitClass R e ⊗ₜ[R] (K.homologyπ q).hom y₀))
        ((homologyTransportAddHom R h_eq)
          ((P.pairHomology 0 q).hom
            (homologyUnitClass R e ⊗ₜ[R] (K.homologyπ q).hom y₀))) :=
      (cast_heq (congrArg (fun n => ↥(K.homology n)) h_eq)
        ((P.pairHomology 0 q).hom
          (homologyUnitClass R e ⊗ₜ[R] (K.homologyπ q).hom y₀))).symm
    exact HEq.trans h2 (heq_of_eq h_hom)
  exact Sigma.ext h_eq h_heq

/-- Right cycle unit gives a right unit on graded homology classes.

If a degree-zero cycle `e` is a right unit for the chain pairing on every cycle, after `p + 0
= p` transport, then pairing any degree-`p` homology class with the class of `e` gives the
same graded element. -/
lemma pairHomology_mul_one_mk
    {K : CochainComplex (ModuleCat.{u} R) ℕ}
    (P : CochainGradedPairing K K K)
    (e : K.cycles 0)
    (hright : ∀ (p : ℕ) (x : K.cycles p),
      (K.XIsoOfEq (Nat.add_zero p)).hom.hom
          ((P.pair p 0).hom ((K.iCycles p).hom x ⊗ₜ[R] (K.iCycles 0).hom e)) =
        (K.iCycles p).hom x)
    (p : ℕ) (x : K.homology p) :
    (GradedMonoid.mk (p + 0)
        ((P.pairHomology p 0).hom (x ⊗ₜ[R] homologyUnitClass R e)) :
      GradedMonoid (fun n ↦ K.homology n)) =
      GradedMonoid.mk p x := by
  obtain ⟨x₀, rfl⟩ := (ModuleCat.epi_iff_surjective (K.homologyπ p)).mp inferInstance x
  have h_eq : (p + 0) = p := Nat.add_zero p
  have h_pair : (P.pairHomology p 0).hom
        ((K.homologyπ p).hom x₀ ⊗ₜ[R] homologyUnitClass R e) =
      (K.homologyπ (p + 0)).hom ((P.pairCycles p 0).hom (x₀ ⊗ₜ[R] e)) := by
    unfold homologyUnitClass
    exact pairHomology_π_apply R P p 0 x₀ e
  have h_cyc : (cyclesTransportAddHom R h_eq)
      ((P.pairCycles p 0).hom (x₀ ⊗ₜ[R] e)) = x₀ := by
    apply (ModuleCat.mono_iff_injective (f := K.iCycles p)).mp inferInstance
    rw [iCycles_transport R h_eq]
    rw [pairCycles_i_apply R]
    exact hright p x₀
  have h_hom : (homologyTransportAddHom R h_eq)
      ((P.pairHomology p 0).hom
        ((K.homologyπ p).hom x₀ ⊗ₜ[R] homologyUnitClass R e)) =
      (K.homologyπ p).hom x₀ := by
    rw [h_pair, homologyπ_transport R h_eq, h_cyc]
  have h_heq : HEq
      ((P.pairHomology p 0).hom
        ((K.homologyπ p).hom x₀ ⊗ₜ[R] homologyUnitClass R e))
      ((K.homologyπ p).hom x₀) := by
    have h2 : HEq
        ((P.pairHomology p 0).hom
          ((K.homologyπ p).hom x₀ ⊗ₜ[R] homologyUnitClass R e))
        ((homologyTransportAddHom R h_eq)
          ((P.pairHomology p 0).hom
            ((K.homologyπ p).hom x₀ ⊗ₜ[R] homologyUnitClass R e))) :=
      (cast_heq (congrArg (fun n => ↥(K.homology n)) h_eq)
        ((P.pairHomology p 0).hom
          ((K.homologyπ p).hom x₀ ⊗ₜ[R] homologyUnitClass R e))).symm
    exact HEq.trans h2 (heq_of_eq h_hom)
  exact Sigma.ext h_eq h_heq

private theorem pairHomology_assoc_mk
    {K : CochainComplex (ModuleCat.{u} R) ℕ}
    (P : CochainGradedPairing K K K)
    (h_assoc : ∀ (p q r : ℕ) (x : K.cycles p) (y : K.cycles q) (z : K.cycles r),
      (cyclesTransportAddHom R (Nat.add_assoc p q r))
          ((P.pairCycles (p + q) r).hom
            ((P.pairCycles p q).hom (x ⊗ₜ[R] y) ⊗ₜ[R] z)) =
        (P.pairCycles p (q + r)).hom
          (x ⊗ₜ[R] (P.pairCycles q r).hom (y ⊗ₜ[R] z)))
    (p q r : ℕ) (x : K.homology p) (y : K.homology q) (z : K.homology r) :
    (GradedMonoid.mk ((p + q) + r)
        ((P.pairHomology (p + q) r).hom
          ((P.pairHomology p q).hom (x ⊗ₜ[R] y) ⊗ₜ[R] z)) :
      GradedMonoid (fun n ↦ K.homology n)) =
      GradedMonoid.mk (p + (q + r))
        ((P.pairHomology p (q + r)).hom
          (x ⊗ₜ[R] (P.pairHomology q r).hom (y ⊗ₜ[R] z))) := by
  obtain ⟨x₀, rfl⟩ := (ModuleCat.epi_iff_surjective (K.homologyπ p)).mp inferInstance x
  obtain ⟨y₀, rfl⟩ := (ModuleCat.epi_iff_surjective (K.homologyπ q)).mp inferInstance y
  obtain ⟨z₀, rfl⟩ := (ModuleCat.epi_iff_surjective (K.homologyπ r)).mp inferInstance z
  have h_eq : ((p + q) + r) = (p + (q + r)) := Nat.add_assoc p q r
  have h_left : (P.pairHomology (p + q) r).hom
        ((P.pairHomology p q).hom
          ((K.homologyπ p).hom x₀ ⊗ₜ[R] (K.homologyπ q).hom y₀) ⊗ₜ[R]
            (K.homologyπ r).hom z₀) =
      (K.homologyπ ((p + q) + r)).hom
        ((P.pairCycles (p + q) r).hom
          ((P.pairCycles p q).hom (x₀ ⊗ₜ[R] y₀) ⊗ₜ[R] z₀)) := by
    rw [pairHomology_π_apply R P p q x₀ y₀,
      pairHomology_π_apply R P (p + q) r ((P.pairCycles p q).hom (x₀ ⊗ₜ[R] y₀)) z₀]
  have h_right : (P.pairHomology p (q + r)).hom
        ((K.homologyπ p).hom x₀ ⊗ₜ[R]
          (P.pairHomology q r).hom
            ((K.homologyπ q).hom y₀ ⊗ₜ[R] (K.homologyπ r).hom z₀)) =
      (K.homologyπ (p + (q + r))).hom
        ((P.pairCycles p (q + r)).hom
          (x₀ ⊗ₜ[R] (P.pairCycles q r).hom (y₀ ⊗ₜ[R] z₀))) := by
    rw [pairHomology_π_apply R P q r y₀ z₀,
      pairHomology_π_apply R P p (q + r) x₀ ((P.pairCycles q r).hom (y₀ ⊗ₜ[R] z₀))]
  have h_hom : (homologyTransportAddHom R h_eq)
        ((P.pairHomology (p + q) r).hom
          ((P.pairHomology p q).hom
            ((K.homologyπ p).hom x₀ ⊗ₜ[R] (K.homologyπ q).hom y₀) ⊗ₜ[R]
              (K.homologyπ r).hom z₀)) =
      (P.pairHomology p (q + r)).hom
        ((K.homologyπ p).hom x₀ ⊗ₜ[R]
          (P.pairHomology q r).hom
            ((K.homologyπ q).hom y₀ ⊗ₜ[R] (K.homologyπ r).hom z₀)) := by
    rw [h_left, h_right, homologyπ_transport R h_eq, h_assoc p q r x₀ y₀ z₀]
  have h2 : HEq
      ((P.pairHomology (p + q) r).hom
        ((P.pairHomology p q).hom
          ((K.homologyπ p).hom x₀ ⊗ₜ[R] (K.homologyπ q).hom y₀) ⊗ₜ[R]
            (K.homologyπ r).hom z₀))
      ((homologyTransportAddHom R h_eq)
        ((P.pairHomology (p + q) r).hom
          ((P.pairHomology p q).hom
            ((K.homologyπ p).hom x₀ ⊗ₜ[R] (K.homologyπ q).hom y₀) ⊗ₜ[R]
              (K.homologyπ r).hom z₀))) :=
    (cast_heq (congrArg (fun n => ↥(K.homology n)) h_eq)
      ((P.pairHomology (p + q) r).hom
        ((P.pairHomology p q).hom
          ((K.homologyπ p).hom x₀ ⊗ₜ[R] (K.homologyπ q).hom y₀) ⊗ₜ[R]
            (K.homologyπ r).hom z₀))).symm
  have h_heq := HEq.trans h2 (heq_of_eq h_hom)
  exact Sigma.ext h_eq h_heq

/-- Associative chain pairing gives associative graded homology products.

Assume the two iterated chain pairings agree on all terms after the degree transport `(p + q)
+ r = p + (q + r)`. Then the corresponding iterated homology pairings give equal elements of
the graded homology family. -/
theorem pairHomology_assoc_mk_of_pair
    {K : CochainComplex (ModuleCat.{u} R) ℕ}
    (P : CochainGradedPairing K K K)
    (h_assoc : ∀ (p q r : ℕ) (x : K.X p) (y : K.X q) (z : K.X r),
      (K.XIsoOfEq (Nat.add_assoc p q r)).hom.hom
          ((P.pair (p + q) r).hom ((P.pair p q).hom (x ⊗ₜ[R] y) ⊗ₜ[R] z)) =
        (P.pair p (q + r)).hom (x ⊗ₜ[R] (P.pair q r).hom (y ⊗ₜ[R] z)))
    (p q r : ℕ) (x : K.homology p) (y : K.homology q) (z : K.homology r) :
    (GradedMonoid.mk ((p + q) + r)
        ((P.pairHomology (p + q) r).hom
          ((P.pairHomology p q).hom (x ⊗ₜ[R] y) ⊗ₜ[R] z)) :
      GradedMonoid (fun n ↦ K.homology n)) =
      GradedMonoid.mk (p + (q + r))
        ((P.pairHomology p (q + r)).hom
          (x ⊗ₜ[R] (P.pairHomology q r).hom (y ⊗ₜ[R] z))) := by
  apply pairHomology_assoc_mk R P
  intro p q r x y z
  apply (ModuleCat.mono_iff_injective (f := K.iCycles (p + (q + r)))).mp inferInstance
  rw [iCycles_transport R]
  simp only [pairCycles_i_apply R]
  exact h_assoc p q r ((K.iCycles p).hom x) ((K.iCycles q).hom y) ((K.iCycles r).hom z)

end HomologicalComplex.CochainGradedPairing
