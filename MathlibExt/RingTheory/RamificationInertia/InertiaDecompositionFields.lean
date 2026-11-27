/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.NumberTheory.RamificationInertia.HilbertTheory
public import Mathlib.FieldTheory.Galois.Basic

/-!
# Ramification and inertia degrees against inertia and decomposition fields

In a Galois extension `L / K` with Dedekind domains `A ⊆ B` (`A` with fraction
field `K`, `B` the integral closure of `A` in `L`), an intermediate field `E`
lies below the inertia field of a prime `𝔓` of `B` exactly when the
ramification index of `𝔓 ∩ 𝓞_E` over `𝔓 ∩ A` is `1`, and below the
decomposition field exactly when both the ramification index and the residue
degree are `1`.

## Source correspondence

This is ATLAS `NumberTheoryI`, Corollary 7.14. The v1 formalization is
`e_ef_eq_one_iff_le_inertiaField_decompositionField` in
`v1/Atlas/NumberTheoryI/code/GaloisExtensions.lean`, proved there from the
tower formulas for inertia-group and decomposition-group cardinalities.
The proofs here follow that argument: the ramification index of
`𝔓_E / 𝔭` times the size of the inertia group of `𝔓` inside the fixing
subgroup of `E` equals the size of the full inertia group, and similarly
for `e * f` and the decomposition group (the stabilizer of `𝔓`). The
biconditionals then follow from a group-theoretic cardinality argument:
a subgroup whose intersection has the same cardinality as the whole group
is the whole group.

The statements use Mathlib's `Ideal.inertia` for the inertia group and
`MulAction.stabilizer` for the decomposition group, and
`IntermediateField.fixedField` for the inertia and decomposition fields.
They use current Mathlib's `Ideal.ramificationIdx q R` /
`Ideal.inertiaDeg q R` (prime first, base ring second), and the residue-field
separability hypotheses are stated as `Algebra.HasSeparableResidueFieldsAt`,
the form Mathlib's inertia/decomposition cardinality lemmas use.
-/

@[expose] public section

namespace Subgroup

/-- **Equal cardinality of an intersection forces containment.** Let $H$ and $K$ be subgroups of
a group $G$ with $H$ finite. If $H \cap K$ has as many elements as $H$, then $H \le K$. -/
theorem le_of_card_subgroupOf_eq {G : Type*} [Group G] {H K : Subgroup G}
    [Finite H]
    (h : Nat.card (H.subgroupOf K) = Nat.card H) :
    H ≤ K := by
  intro x hx
  let f : (H.subgroupOf K) → H := fun ⟨⟨g, _⟩, hg⟩ => ⟨g, Subgroup.mem_subgroupOf.mp hg⟩
  have hf_inj : Function.Injective f := by
    intro ⟨⟨g₁, _⟩, _⟩ ⟨⟨g₂, _⟩, _⟩ heq
    simp only [f, Subtype.mk.injEq] at heq
    exact Subtype.ext (Subtype.ext heq)
  have hf_bij := hf_inj.bijective_of_nat_card_le (h ▸ le_refl _)
  obtain ⟨⟨⟨g, hg_K⟩, hg_H⟩, hg_eq⟩ := hf_bij.2 ⟨x, hx⟩
  simp only [f, Subtype.mk.injEq] at hg_eq
  rw [← hg_eq]; exact hg_K

end Subgroup

namespace Ideal

section UnramifiedSplitCharacterization

variable (K L : Type*) {B : Type*} [Field K] [Field L] [Algebra K L]
  [CommRing B] [MulSemiringAction (L ≃ₐ[K] L) B]

/-- **Tower formula for inertia groups.**
Let $L/K$ be a finite Galois extension with Galois group $G$. Let $A$ and $B$ be Dedekind domains
with $B$ a finite torsion-free $A$-algebra, and let $G$ act on $B$ by ring automorphisms as a
Galois group of $B$ over $A$: faithfully, fixing the image of $A$, and with every element of $B$
fixed by $G$ in the image of $A$. Let $E$ be an intermediate field of $L/K$ and $H \le G$ the
subgroup fixing $E$ pointwise. Let $C$ be a Dedekind domain and a torsion-free $A$-algebra, and
give $E$ an $A$-algebra structure and an injective ring map $C \to E$ whose image is the set of
elements of $E$ integral over $A$ (the composite $A \to C \to E$ need not be the given map
$A \to E$). Suppose $B$ is also a finite torsion-free $C$-algebra, with $A \to C \to B$ equal to
$A \to B$, and that $H$, acting on $B$ by restriction, is a Galois group of $B$ over $C$. Let
$\mathfrak p$, $\mathfrak P_E$ and $\mathfrak P$ be maximal ideals of $A$, $C$ and $B$ such that
$\mathfrak P$ lies over $\mathfrak p$ and over $\mathfrak P_E$ and $\mathfrak P_E$ lies over
$\mathfrak p$, and suppose that every prime of $B$ over $\mathfrak p$, and every prime of $B$
over $\mathfrak P_E$, has a separable residue field extension. For a subgroup $S \le G$ write
$I_S(\mathfrak P)$ for the inertia group of $\mathfrak P$ in $S$, the set of $\sigma \in S$ with
$\sigma(x) - x \in \mathfrak P$ for all $x \in B$. Then
$e(\mathfrak P_E \mid \mathfrak p) \cdot |I_H(\mathfrak P)| = |I_G(\mathfrak P)|$, where
$e(\mathfrak P_E \mid \mathfrak p)$ is the ramification index of $\mathfrak P_E$ over
$\mathfrak p$. -/
theorem card_inertia_tower_formula
    {K L : Type*} {B : Type*} [Field K] [Field L] [Algebra K L]
    [CommRing B] [MulSemiringAction (L ≃ₐ[K] L) B]
    [IsDedekindDomain B] [FaithfulSMul (L ≃ₐ[K] L) B]
    {A : Type*} [CommRing A] [IsDedekindDomain A] [Algebra A B]
    (P : Ideal B) [IsGalois K L] [FiniteDimensional K L] [P.IsMaximal]
    (p : Ideal A) [p.IsMaximal]
    (E : IntermediateField K L)
    (C_E : Type*) [CommRing C_E] [IsDedekindDomain C_E] [Algebra A C_E]
    [Algebra A ↥E] [Algebra C_E ↥E] [IsIntegralClosure C_E A ↥E]
    (P_E : Ideal C_E) [P_E.IsMaximal] [P_E.LiesOver p]
    [Algebra C_E B] [IsScalarTower A C_E B]
    [Module.Finite A B] [Module.IsTorsionFree A B]
    [Module.Finite C_E B] [Module.IsTorsionFree C_E B]
    [Module.IsTorsionFree A C_E]
    [P.LiesOver p] [P.LiesOver P_E]
    [Algebra.HasSeparableResidueFieldsAt A B p]
    [Algebra.HasSeparableResidueFieldsAt C_E B P_E]
    [IsGaloisGroup (L ≃ₐ[K] L) A B]
    [IsGaloisGroup (↥E.fixingSubgroup) C_E B]
    :
    P_E.ramificationIdx A *
      Nat.card (P.inertia (↥E.fixingSubgroup)) =
    Nat.card (P.inertia (L ≃ₐ[K] L)) := by
  have h_full := Ideal.card_inertia_eq_ramificationIdxIn (G := (L ≃ₐ[K] L)) p P
  rw [Ideal.ramificationIdxIn_eq_ramificationIdx p P (L ≃ₐ[K] L)] at h_full
  have h_sub := Ideal.card_inertia_eq_ramificationIdxIn (G := ↥E.fixingSubgroup) P_E P
  rw [Ideal.ramificationIdxIn_eq_ramificationIdx P_E P ↥E.fixingSubgroup] at h_sub
  have h_tower := Ideal.ramificationIdx_tower (R := A) P_E P
  rw [h_sub, ← h_tower]
  exact h_full.symm

/-- **Tower formula for inertia groups, intersected with the fixing group.**
Let $L/K$ be a finite Galois extension with Galois group $G$. Let $A$ and $B$ be Dedekind domains
with $B$ a finite torsion-free $A$-algebra, and let $G$ act on $B$ by ring automorphisms as a
Galois group of $B$ over $A$: faithfully, fixing the image of $A$, and with every element of $B$
fixed by $G$ in the image of $A$. Let $E$ be an intermediate field of $L/K$ and $H \le G$ the
subgroup fixing $E$ pointwise. Let $C$ be a Dedekind domain and a torsion-free $A$-algebra, and
give $E$ an $A$-algebra structure and an injective ring map $C \to E$ whose image is the set of
elements of $E$ integral over $A$ (the composite $A \to C \to E$ need not be the given map
$A \to E$). Suppose $B$ is also a finite torsion-free $C$-algebra, with $A \to C \to B$ equal to
$A \to B$, and that $H$, acting on $B$ by restriction, is a Galois group of $B$ over $C$. Let
$\mathfrak p$, $\mathfrak P_E$ and $\mathfrak P$ be maximal ideals of $A$, $C$ and $B$ such that
$\mathfrak P$ lies over $\mathfrak p$ and over $\mathfrak P_E$ and $\mathfrak P_E$ lies over
$\mathfrak p$, and suppose that every prime of $B$ over $\mathfrak p$, and every prime of $B$
over $\mathfrak P_E$, has a separable residue field extension. Let $I(\mathfrak P)$ be the
inertia group of $\mathfrak P$, the set of $\sigma \in G$ with $\sigma(x) - x \in \mathfrak P$
for all $x \in B$. Then
$e(\mathfrak P_E \mid \mathfrak p) \cdot |I(\mathfrak P) \cap H| = |I(\mathfrak P)|$, where
$e(\mathfrak P_E \mid \mathfrak p)$ is the ramification index of $\mathfrak P_E$ over
$\mathfrak p$. -/
theorem ramificationIdx_mul_card_inertia_subgroupOf
    {K L : Type*} {B : Type*} [Field K] [Field L] [Algebra K L]
    [CommRing B] [MulSemiringAction (L ≃ₐ[K] L) B]
    [IsDedekindDomain B] [FaithfulSMul (L ≃ₐ[K] L) B]
    {A : Type*} [CommRing A] [IsDedekindDomain A] [Algebra A B]
    (P : Ideal B) [IsGalois K L] [FiniteDimensional K L] [P.IsMaximal]
    (p : Ideal A) [p.IsMaximal]
    (E : IntermediateField K L)
    (C_E : Type*) [CommRing C_E] [IsDedekindDomain C_E] [Algebra A C_E]
    [Algebra A ↥E] [Algebra C_E ↥E] [IsIntegralClosure C_E A ↥E]
    (P_E : Ideal C_E) [P_E.IsMaximal] [P_E.LiesOver p]
    [Algebra C_E B] [IsScalarTower A C_E B]
    [Module.Finite A B] [Module.IsTorsionFree A B]
    [Module.Finite C_E B] [Module.IsTorsionFree C_E B]
    [Module.IsTorsionFree A C_E]
    [P.LiesOver p] [P.LiesOver P_E]
    [Algebra.HasSeparableResidueFieldsAt A B p]
    [Algebra.HasSeparableResidueFieldsAt C_E B P_E]
    [IsGaloisGroup (L ≃ₐ[K] L) A B]
    [IsGaloisGroup (↥E.fixingSubgroup) C_E B]
    :
    P_E.ramificationIdx A *
      Nat.card ((P.inertia (L ≃ₐ[K] L)).subgroupOf E.fixingSubgroup) =
    Nat.card (P.inertia (L ≃ₐ[K] L)) := by
  rw [show (P.inertia (L ≃ₐ[K] L)).subgroupOf E.fixingSubgroup =
    P.inertia E.fixingSubgroup from
    AddSubgroup.subgroupOf_inertia P.toAddSubgroup E.fixingSubgroup]
  exact card_inertia_tower_formula P p E C_E P_E

/-- **Ramification index one and the inertia group.**
Let $L/K$ be a finite Galois extension with Galois group $G$. Let $A$ and $B$ be Dedekind domains
with $B$ a finite torsion-free $A$-algebra, and let $G$ act on $B$ by ring automorphisms as a
Galois group of $B$ over $A$: faithfully, fixing the image of $A$, and with every element of $B$
fixed by $G$ in the image of $A$. Let $E$ be an intermediate field of $L/K$ and $H \le G$ the
subgroup fixing $E$ pointwise. Let $C$ be a Dedekind domain and a torsion-free $A$-algebra, and
give $E$ an $A$-algebra structure and an injective ring map $C \to E$ whose image is the set of
elements of $E$ integral over $A$ (the composite $A \to C \to E$ need not be the given map
$A \to E$). Suppose $B$ is also a finite torsion-free $C$-algebra, with $A \to C \to B$ equal to
$A \to B$, and that $H$, acting on $B$ by restriction, is a Galois group of $B$ over $C$. Let
$\mathfrak p$, $\mathfrak P_E$ and $\mathfrak P$ be maximal ideals of $A$, $C$ and $B$ such that
$\mathfrak P$ lies over $\mathfrak p$ and over $\mathfrak P_E$ and $\mathfrak P_E$ lies over
$\mathfrak p$, and suppose that every prime of $B$ over $\mathfrak p$, and every prime of $B$
over $\mathfrak P_E$, has a separable residue field extension. Let $I(\mathfrak P)$ be the
inertia group of $\mathfrak P$, the set of $\sigma \in G$ with $\sigma(x) - x \in \mathfrak P$
for all $x \in B$. Then the ramification index $e(\mathfrak P_E \mid \mathfrak p)$ of
$\mathfrak P_E$ over $\mathfrak p$ equals $1$ if and only if $I(\mathfrak P) \le H$. -/
theorem ramificationIdx_eq_one_iff_inertia_le_fixingSubgroup
    [IsDedekindDomain B] [FaithfulSMul (L ≃ₐ[K] L) B]
    {A : Type*} [CommRing A] [IsDedekindDomain A] [Algebra A B]
    (P : Ideal B) [IsGalois K L] [FiniteDimensional K L] [P.IsMaximal]
    (p : Ideal A) [p.IsMaximal]
    (E : IntermediateField K L)
    (C_E : Type*) [CommRing C_E] [IsDedekindDomain C_E] [Algebra A C_E]
    [Algebra A ↥E] [Algebra C_E ↥E] [IsIntegralClosure C_E A ↥E]
    (P_E : Ideal C_E) [P_E.IsMaximal] [P_E.LiesOver p]
    [Algebra C_E B] [IsScalarTower A C_E B]
    [Module.Finite A B] [Module.IsTorsionFree A B]
    [Module.Finite C_E B] [Module.IsTorsionFree C_E B]
    [Module.IsTorsionFree A C_E]
    [P.LiesOver p] [P.LiesOver P_E]
    [Algebra.HasSeparableResidueFieldsAt A B p]
    [Algebra.HasSeparableResidueFieldsAt C_E B P_E]
    [IsGaloisGroup (L ≃ₐ[K] L) A B]
    [IsGaloisGroup (↥E.fixingSubgroup) C_E B]
    :
    P_E.ramificationIdx A = 1 ↔
      P.inertia (L ≃ₐ[K] L) ≤ E.fixingSubgroup := by
  have htower := ramificationIdx_mul_card_inertia_subgroupOf P p E C_E P_E
  constructor
  · intro he
    rw [he, one_mul] at htower
    exact Subgroup.le_of_card_subgroupOf_eq htower
  · intro hle
    have hcard_eq : Nat.card ((P.inertia (L ≃ₐ[K] L)).subgroupOf E.fixingSubgroup) =
        Nat.card (P.inertia (L ≃ₐ[K] L)) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv
    rw [hcard_eq] at htower
    exact mul_right_cancel₀ (Nat.pos_iff_ne_zero.mp Nat.card_pos)
      (htower.trans (one_mul _).symm)

/-- **Ramification index one and the inertia field.**
Let $L/K$ be a finite Galois extension with Galois group $G$. Let $A$ and $B$ be Dedekind domains
with $B$ a finite torsion-free $A$-algebra, and let $G$ act on $B$ by ring automorphisms as a
Galois group of $B$ over $A$: faithfully, fixing the image of $A$, and with every element of $B$
fixed by $G$ in the image of $A$. Let $E$ be an intermediate field of $L/K$ and $H \le G$ the
subgroup fixing $E$ pointwise. Let $C$ be a Dedekind domain and a torsion-free $A$-algebra, and
give $E$ an $A$-algebra structure and an injective ring map $C \to E$ whose image is the set of
elements of $E$ integral over $A$ (the composite $A \to C \to E$ need not be the given map
$A \to E$). Suppose $B$ is also a finite torsion-free $C$-algebra, with $A \to C \to B$ equal to
$A \to B$, and that $H$, acting on $B$ by restriction, is a Galois group of $B$ over $C$. Let
$\mathfrak p$, $\mathfrak P_E$ and $\mathfrak P$ be maximal ideals of $A$, $C$ and $B$ such that
$\mathfrak P$ lies over $\mathfrak p$ and over $\mathfrak P_E$ and $\mathfrak P_E$ lies over
$\mathfrak p$, and suppose that every prime of $B$ over $\mathfrak p$, and every prime of $B$
over $\mathfrak P_E$, has a separable residue field extension. Let $I(\mathfrak P)$ be the
inertia group of $\mathfrak P$, the set of $\sigma \in G$ with $\sigma(x) - x \in \mathfrak P$
for all $x \in B$, and let $L^{I(\mathfrak P)}$ be its fixed field in $L$. Then the ramification
index $e(\mathfrak P_E \mid \mathfrak p)$ of $\mathfrak P_E$ over $\mathfrak p$ equals $1$ if and
only if $E \subseteq L^{I(\mathfrak P)}$. -/
theorem ramificationIdx_eq_one_iff_le_inertiaField
    [IsDedekindDomain B] [FaithfulSMul (L ≃ₐ[K] L) B]
    {A : Type*} [CommRing A] [IsDedekindDomain A] [Algebra A B]
    (P : Ideal B) [IsGalois K L] [FiniteDimensional K L] [P.IsMaximal]
    (p : Ideal A) [p.IsMaximal]
    (E : IntermediateField K L)
    (C_E : Type*) [CommRing C_E] [IsDedekindDomain C_E] [Algebra A C_E]
    [Algebra A ↥E] [Algebra C_E ↥E] [IsIntegralClosure C_E A ↥E]
    (P_E : Ideal C_E) [P_E.IsMaximal] [P_E.LiesOver p]
    [Algebra C_E B] [IsScalarTower A C_E B]
    [Module.Finite A B] [Module.IsTorsionFree A B]
    [Module.Finite C_E B] [Module.IsTorsionFree C_E B]
    [Module.IsTorsionFree A C_E]
    [P.LiesOver p] [P.LiesOver P_E]
    [Algebra.HasSeparableResidueFieldsAt A B p]
    [Algebra.HasSeparableResidueFieldsAt C_E B P_E]
    [IsGaloisGroup (L ≃ₐ[K] L) A B]
    [IsGaloisGroup (↥E.fixingSubgroup) C_E B]
    :
    P_E.ramificationIdx A = 1 ↔
      E ≤ IntermediateField.fixedField (P.inertia (L ≃ₐ[K] L)) := by
  rw [ramificationIdx_eq_one_iff_inertia_le_fixingSubgroup K L P p E C_E P_E]
  exact (IntermediateField.le_iff_le (P.inertia (L ≃ₐ[K] L)) E).symm

set_option maxHeartbeats 400000 in
/-- **Tower formula for decomposition groups.**
Let $L/K$ be a finite Galois extension with Galois group $G$. Let $A$ and $B$ be Dedekind domains
with $B$ a finite torsion-free $A$-algebra, and let $G$ act on $B$ by ring automorphisms as a
Galois group of $B$ over $A$: faithfully, fixing the image of $A$, and with every element of $B$
fixed by $G$ in the image of $A$. Let $E$ be an intermediate field of $L/K$ and $H \le G$ the
subgroup fixing $E$ pointwise. Let $C$ be a Dedekind domain and a torsion-free $A$-algebra, and
give $E$ an $A$-algebra structure and an injective ring map $C \to E$ whose image is the set of
elements of $E$ integral over $A$ (the composite $A \to C \to E$ need not be the given map
$A \to E$). Suppose $B$ is also a finite torsion-free $C$-algebra, with $A \to C \to B$ equal to
$A \to B$, and that $H$, acting on $B$ by restriction, is a Galois group of $B$ over $C$. Let
$\mathfrak p$, $\mathfrak P_E$ and $\mathfrak P$ be maximal ideals of $A$, $C$ and $B$ such that
$\mathfrak P$ lies over $\mathfrak p$ and over $\mathfrak P_E$ and $\mathfrak P_E$ lies over
$\mathfrak p$, and suppose that every prime of $B$ over $\mathfrak p$, and every prime of $B$
over $\mathfrak P_E$, has a separable residue field extension. Let $D(\mathfrak P)$ be the
decomposition group of $\mathfrak P$, the set of $\sigma \in G$ with
$\sigma(\mathfrak P) = \mathfrak P$, and let $e$ and $f$ be the ramification index and the
inertia degree of $\mathfrak P_E$ over $\mathfrak p$. Then
$e f \cdot |D(\mathfrak P) \cap H| = |D(\mathfrak P)|$. -/
theorem ramificationIdx_mul_inertiaDeg_mul_card_stabilizer_subgroupOf
    [IsDedekindDomain B] [FaithfulSMul (L ≃ₐ[K] L) B]
    {A : Type*} [CommRing A] [IsDedekindDomain A] [Algebra A B]
    (P : Ideal B) [IsGalois K L] [FiniteDimensional K L] [P.IsMaximal]
    (p : Ideal A) [p.IsMaximal]
    (E : IntermediateField K L)
    (C_E : Type*) [CommRing C_E] [IsDedekindDomain C_E] [Algebra A C_E]
    [Algebra A ↥E] [Algebra C_E ↥E] [IsIntegralClosure C_E A ↥E]
    (P_E : Ideal C_E) [P_E.IsMaximal] [P_E.LiesOver p]
    [Algebra C_E B] [IsScalarTower A C_E B]
    [Module.Finite A B] [Module.IsTorsionFree A B]
    [Module.Finite C_E B] [Module.IsTorsionFree C_E B]
    [Module.IsTorsionFree A C_E]
    [P.LiesOver p] [P.LiesOver P_E]
    [Algebra.HasSeparableResidueFieldsAt A B p]
    [Algebra.HasSeparableResidueFieldsAt C_E B P_E]
    [IsGaloisGroup (L ≃ₐ[K] L) A B]
    [IsGaloisGroup (↥E.fixingSubgroup) C_E B]
    :
    (P_E.ramificationIdx A * P_E.inertiaDeg A) *
      Nat.card ((@MulAction.stabilizer (L ≃ₐ[K] L) (Ideal B) _
        Ideal.pointwiseMulSemiringAction.toMulAction P).subgroupOf E.fixingSubgroup) =
    Nat.card (@MulAction.stabilizer (L ≃ₐ[K] L) (Ideal B) _
        Ideal.pointwiseMulSemiringAction.toMulAction P) := by
  rw [show (@MulAction.stabilizer (L ≃ₐ[K] L) (Ideal B) _
      Ideal.pointwiseMulSemiringAction.toMulAction P).subgroupOf E.fixingSubgroup =
      @MulAction.stabilizer (↥E.fixingSubgroup) (Ideal B) _
        Ideal.pointwiseMulSemiringAction.toMulAction P from by
    ext ⟨h, hH⟩
    simp only [Subgroup.mem_subgroupOf, MulAction.mem_stabilizer_iff]
    rfl]
  have h_full := Ideal.card_stabilizer_eq (G := (L ≃ₐ[K] L)) p P
  rw [Ideal.ramificationIdxIn_eq_ramificationIdx p P (L ≃ₐ[K] L),
      Ideal.inertiaDegIn_eq_inertiaDeg p P (L ≃ₐ[K] L)] at h_full
  have h_sub := Ideal.card_stabilizer_eq (G := ↥E.fixingSubgroup) P_E P
  rw [Ideal.ramificationIdxIn_eq_ramificationIdx P_E P ↥E.fixingSubgroup,
      Ideal.inertiaDegIn_eq_inertiaDeg P_E P ↥E.fixingSubgroup] at h_sub
  have h_e_tower := Ideal.ramificationIdx_tower (R := A) P_E P
  have h_f_tower := Ideal.inertiaDeg_tower (R := A) P_E P
  rw [h_sub, h_full, h_e_tower, h_f_tower]
  ring

/-- **Ramification index and inertia degree one and the decomposition group.**
Let $L/K$ be a finite Galois extension with Galois group $G$. Let $A$ and $B$ be Dedekind domains
with $B$ a finite torsion-free $A$-algebra, and let $G$ act on $B$ by ring automorphisms as a
Galois group of $B$ over $A$: faithfully, fixing the image of $A$, and with every element of $B$
fixed by $G$ in the image of $A$. Let $E$ be an intermediate field of $L/K$ and $H \le G$ the
subgroup fixing $E$ pointwise. Let $C$ be a Dedekind domain and a torsion-free $A$-algebra, and
give $E$ an $A$-algebra structure and an injective ring map $C \to E$ whose image is the set of
elements of $E$ integral over $A$ (the composite $A \to C \to E$ need not be the given map
$A \to E$). Suppose $B$ is also a finite torsion-free $C$-algebra, with $A \to C \to B$ equal to
$A \to B$, and that $H$, acting on $B$ by restriction, is a Galois group of $B$ over $C$. Let
$\mathfrak p$, $\mathfrak P_E$ and $\mathfrak P$ be maximal ideals of $A$, $C$ and $B$ such that
$\mathfrak P$ lies over $\mathfrak p$ and over $\mathfrak P_E$ and $\mathfrak P_E$ lies over
$\mathfrak p$, and suppose that every prime of $B$ over $\mathfrak p$, and every prime of $B$
over $\mathfrak P_E$, has a separable residue field extension. Let $D(\mathfrak P)$ be the
decomposition group of $\mathfrak P$, the set of $\sigma \in G$ with
$\sigma(\mathfrak P) = \mathfrak P$, and let $e$ and $f$ be the ramification index and the
inertia degree of $\mathfrak P_E$ over $\mathfrak p$. Then $e = 1$ and $f = 1$ if and only if
$D(\mathfrak P) \le H$. -/
theorem ramificationIdx_inertiaDeg_eq_one_iff_stabilizer_le_fixingSubgroup
    [IsDedekindDomain B] [FaithfulSMul (L ≃ₐ[K] L) B]
    {A : Type*} [CommRing A] [IsDedekindDomain A] [Algebra A B]
    (P : Ideal B) [IsGalois K L] [FiniteDimensional K L] [P.IsMaximal]
    (p : Ideal A) [p.IsMaximal]
    (E : IntermediateField K L)
    (C_E : Type*) [CommRing C_E] [IsDedekindDomain C_E] [Algebra A C_E]
    [Algebra A ↥E] [Algebra C_E ↥E] [IsIntegralClosure C_E A ↥E]
    (P_E : Ideal C_E) [P_E.IsMaximal] [P_E.LiesOver p]
    [Algebra C_E B] [IsScalarTower A C_E B]
    [Module.Finite A B] [Module.IsTorsionFree A B]
    [Module.Finite C_E B] [Module.IsTorsionFree C_E B]
    [Module.IsTorsionFree A C_E]
    [P.LiesOver p] [P.LiesOver P_E]
    [Algebra.HasSeparableResidueFieldsAt A B p]
    [Algebra.HasSeparableResidueFieldsAt C_E B P_E]
    [IsGaloisGroup (L ≃ₐ[K] L) A B]
    [IsGaloisGroup (↥E.fixingSubgroup) C_E B]
    :
    (P_E.ramificationIdx A = 1 ∧ P_E.inertiaDeg A = 1) ↔
      (@MulAction.stabilizer (L ≃ₐ[K] L) (Ideal B) _
        Ideal.pointwiseMulSemiringAction.toMulAction P) ≤ E.fixingSubgroup := by
  have htower := ramificationIdx_mul_inertiaDeg_mul_card_stabilizer_subgroupOf K L P p E C_E P_E
  constructor
  · intro ⟨he, hf⟩
    rw [he, hf, mul_one, one_mul] at htower
    exact Subgroup.le_of_card_subgroupOf_eq htower
  · intro hle
    have hcard_eq : Nat.card ((@MulAction.stabilizer (L ≃ₐ[K] L) (Ideal B) _
          Ideal.pointwiseMulSemiringAction.toMulAction P).subgroupOf E.fixingSubgroup) =
        Nat.card (@MulAction.stabilizer (L ≃ₐ[K] L) (Ideal B) _
          Ideal.pointwiseMulSemiringAction.toMulAction P) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv
    rw [hcard_eq] at htower
    have hef : P_E.ramificationIdx A * P_E.inertiaDeg A = 1 :=
      mul_right_cancel₀ (Nat.pos_iff_ne_zero.mp Nat.card_pos)
        (htower.trans (one_mul _).symm)
    exact mul_eq_one.mp hef

/-- **Ramification index and inertia degree one and the decomposition field.**
Let $L/K$ be a finite Galois extension with Galois group $G$. Let $A$ and $B$ be Dedekind domains
with $B$ a finite torsion-free $A$-algebra, and let $G$ act on $B$ by ring automorphisms as a
Galois group of $B$ over $A$: faithfully, fixing the image of $A$, and with every element of $B$
fixed by $G$ in the image of $A$. Let $E$ be an intermediate field of $L/K$ and $H \le G$ the
subgroup fixing $E$ pointwise. Let $C$ be a Dedekind domain and a torsion-free $A$-algebra, and
give $E$ an $A$-algebra structure and an injective ring map $C \to E$ whose image is the set of
elements of $E$ integral over $A$ (the composite $A \to C \to E$ need not be the given map
$A \to E$). Suppose $B$ is also a finite torsion-free $C$-algebra, with $A \to C \to B$ equal to
$A \to B$, and that $H$, acting on $B$ by restriction, is a Galois group of $B$ over $C$. Let
$\mathfrak p$, $\mathfrak P_E$ and $\mathfrak P$ be maximal ideals of $A$, $C$ and $B$ such that
$\mathfrak P$ lies over $\mathfrak p$ and over $\mathfrak P_E$ and $\mathfrak P_E$ lies over
$\mathfrak p$, and suppose that every prime of $B$ over $\mathfrak p$, and every prime of $B$
over $\mathfrak P_E$, has a separable residue field extension. Let $D(\mathfrak P)$ be the
decomposition group of $\mathfrak P$, the set of $\sigma \in G$ with
$\sigma(\mathfrak P) = \mathfrak P$, and let $L^{D(\mathfrak P)}$ be its fixed field in $L$. Let
$e$ and $f$ be the ramification index and the inertia degree of $\mathfrak P_E$ over
$\mathfrak p$. Then $e = 1$ and $f = 1$ if and only if $E \subseteq L^{D(\mathfrak P)}$. -/
theorem ramificationIdx_inertiaDeg_eq_one_iff_le_decompositionField
    [IsDedekindDomain B] [FaithfulSMul (L ≃ₐ[K] L) B]
    {A : Type*} [CommRing A] [IsDedekindDomain A] [Algebra A B]
    (P : Ideal B) [IsGalois K L] [FiniteDimensional K L] [P.IsMaximal]
    (p : Ideal A) [p.IsMaximal]
    (E : IntermediateField K L)
    (C_E : Type*) [CommRing C_E] [IsDedekindDomain C_E] [Algebra A C_E]
    [Algebra A ↥E] [Algebra C_E ↥E] [IsIntegralClosure C_E A ↥E]
    (P_E : Ideal C_E) [P_E.IsMaximal] [P_E.LiesOver p]
    [Algebra C_E B] [IsScalarTower A C_E B]
    [Module.Finite A B] [Module.IsTorsionFree A B]
    [Module.Finite C_E B] [Module.IsTorsionFree C_E B]
    [Module.IsTorsionFree A C_E]
    [P.LiesOver p] [P.LiesOver P_E]
    [Algebra.HasSeparableResidueFieldsAt A B p]
    [Algebra.HasSeparableResidueFieldsAt C_E B P_E]
    [IsGaloisGroup (L ≃ₐ[K] L) A B]
    [IsGaloisGroup (↥E.fixingSubgroup) C_E B]
    :
    (P_E.ramificationIdx A = 1 ∧ P_E.inertiaDeg A = 1) ↔
      E ≤ IntermediateField.fixedField
        (@MulAction.stabilizer (L ≃ₐ[K] L) (Ideal B) _
          Ideal.pointwiseMulSemiringAction.toMulAction P) := by
  rw [IntermediateField.le_iff_le]
  exact ramificationIdx_inertiaDeg_eq_one_iff_stabilizer_le_fixingSubgroup K L P p E C_E P_E

/-- **Fields below the inertia and decomposition fields.**
Let $L/K$ be a finite Galois extension with Galois group $G$. Let $A$ and $B$ be Dedekind domains
with $B$ a finite torsion-free $A$-algebra, and let $G$ act on $B$ by ring automorphisms as a
Galois group of $B$ over $A$: faithfully, fixing the image of $A$, and with every element of $B$
fixed by $G$ in the image of $A$. Let $E$ be an intermediate field of $L/K$ and $H \le G$ the
subgroup fixing $E$ pointwise. Let $C$ be a Dedekind domain and a torsion-free $A$-algebra, and
give $E$ an $A$-algebra structure and an injective ring map $C \to E$ whose image is the set of
elements of $E$ integral over $A$ (the composite $A \to C \to E$ need not be the given map
$A \to E$). Suppose $B$ is also a finite torsion-free $C$-algebra, with $A \to C \to B$ equal to
$A \to B$, and that $H$, acting on $B$ by restriction, is a Galois group of $B$ over $C$. Let
$\mathfrak p$, $\mathfrak P_E$ and $\mathfrak P$ be maximal ideals of $A$, $C$ and $B$ such that
$\mathfrak P$ lies over $\mathfrak p$ and over $\mathfrak P_E$ and $\mathfrak P_E$ lies over
$\mathfrak p$, and suppose that every prime of $B$ over $\mathfrak p$, and every prime of $B$
over $\mathfrak P_E$, has a separable residue field extension. Let $I(\mathfrak P)$ be the
inertia group of $\mathfrak P$, the set of $\sigma \in G$ with $\sigma(x) - x \in \mathfrak P$
for all $x \in B$, and $D(\mathfrak P)$ its decomposition group, the set of $\sigma \in G$ with
$\sigma(\mathfrak P) = \mathfrak P$; let $L^{I(\mathfrak P)}$ and $L^{D(\mathfrak P)}$ be their
fixed fields in $L$, and let $e$ and $f$ be the ramification index and the inertia degree of
$\mathfrak P_E$ over $\mathfrak p$. Then $e = 1$ if and only if $E \subseteq L^{I(\mathfrak P)}$,
and $e = f = 1$ if and only if $E \subseteq L^{D(\mathfrak P)}$.

Source: ATLAS NumberTheoryI, Corollary 7.14. -/
theorem ramificationIdx_inertiaDeg_eq_one_iff_le_inertiaField_decompositionField
    [IsDedekindDomain B] [FaithfulSMul (L ≃ₐ[K] L) B]
    {A : Type*} [CommRing A] [IsDedekindDomain A] [Algebra A B]
    (P : Ideal B) [IsGalois K L] [FiniteDimensional K L] [P.IsMaximal]
    (p : Ideal A) [p.IsMaximal]
    (E : IntermediateField K L)
    (C_E : Type*) [CommRing C_E] [IsDedekindDomain C_E] [Algebra A C_E]
    [Algebra A ↥E] [Algebra C_E ↥E] [IsIntegralClosure C_E A ↥E]
    (P_E : Ideal C_E) [P_E.IsMaximal] [P_E.LiesOver p]
    [Algebra C_E B] [IsScalarTower A C_E B]
    [Module.Finite A B] [Module.IsTorsionFree A B]
    [Module.Finite C_E B] [Module.IsTorsionFree C_E B]
    [Module.IsTorsionFree A C_E]
    [P.LiesOver p] [P.LiesOver P_E]
    [Algebra.HasSeparableResidueFieldsAt A B p]
    [Algebra.HasSeparableResidueFieldsAt C_E B P_E]
    [IsGaloisGroup (L ≃ₐ[K] L) A B]
    [IsGaloisGroup (↥E.fixingSubgroup) C_E B]
    :
    (P_E.ramificationIdx A = 1 ↔
      E ≤ IntermediateField.fixedField (P.inertia (L ≃ₐ[K] L))) ∧
    ((P_E.ramificationIdx A = 1 ∧ P_E.inertiaDeg A = 1) ↔
      E ≤ IntermediateField.fixedField
        (@MulAction.stabilizer (L ≃ₐ[K] L) (Ideal B) _
          Ideal.pointwiseMulSemiringAction.toMulAction P)) :=
  ⟨ramificationIdx_eq_one_iff_le_inertiaField K L P p E C_E P_E,
   ramificationIdx_inertiaDeg_eq_one_iff_le_decompositionField K L P p E C_E P_E⟩

end UnramifiedSplitCharacterization

end Ideal
