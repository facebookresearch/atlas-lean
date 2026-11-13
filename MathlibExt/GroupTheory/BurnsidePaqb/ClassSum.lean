/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Group.ConjFinite
public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.Data.Complex.Basic
public import MathlibExt.GroupTheory.BurnsidePaqbReduction

/-!
Conjugacy-class-algebra stage of the complete Burnside proof.

Authors: Muse Spark 1.3
Source archive: genai_web_search/tree/users/akiezun/burnside_proof.zip
SHA-256: d9da7df82e467d9fa587892eeef9f51e2b83df0588175653bd1d16264b09dd00

This module is the conjugacy-class-algebra stage of the complete Burnside proof,
mechanically ported from the audited source `extracted/Burnside/ClassSum.lean`.
-/

namespace BurnsidePaqb

@[expose] public section

variable {G : Type*} [Group G] [Fintype G]

/-- **Class sum of a finite subset.** Let $G$ be a group. The class sum of a finite subset
$C \subseteq G$ is the element $\widehat{C} = \sum_{x \in C} x$ of the complex group algebra
$\mathbb{C}[G]$. -/
noncomputable def classSum (C : Finset G) : MonoidAlgebra ℂ G :=
  ∑ x ∈ C, MonoidAlgebra.of ℂ G x

/-- **Class sums commute with group elements.** Let $G$ be a finite group, let $g \in G$, and let
$\widehat{C_g} = \sum_{x \in C_g} x$ be the sum, in the complex group algebra $\mathbb{C}[G]$, of
the elements of the conjugacy class $C_g$ of $g$. Then $\widehat{C_g} h = h \widehat{C_g}$ for
every $h \in G$, where $h$ is viewed as a basis element of $\mathbb{C}[G]$. -/
theorem classSum_central (g h : G) :
    classSum (conjClass g) * MonoidAlgebra.of ℂ G h =
      MonoidAlgebra.of ℂ G h * classSum (conjClass g) := by
  simp only [classSum, Finset.sum_mul, Finset.mul_sum, ← map_mul]
  refine Finset.sum_bij (fun x _ => h⁻¹ * x * h) ?_ ?_ ?_ ?_
  · intro x hx
    simpa using conj_mem_conjClass g h⁻¹ x hx
  · intro a₁ _ a₂ _ heq
    have h2 : h * (h⁻¹ * a₁ * h) * h⁻¹ = h * (h⁻¹ * a₂ * h) * h⁻¹ :=
      congrArg (fun y => h * y * h⁻¹) heq
    have e1 : h * (h⁻¹ * a₁ * h) * h⁻¹ = a₁ := by group
    have e2 : h * (h⁻¹ * a₂ * h) * h⁻¹ = a₂ := by group
    rw [e1, e2] at h2
    exact h2
  · intro y hy
    refine ⟨h * y * h⁻¹, conj_mem_conjClass g h y hy, ?_⟩
    show h⁻¹ * (h * y * h⁻¹) * h = y
    group
  · intro x hx
    show MonoidAlgebra.of ℂ G (x * h) = MonoidAlgebra.of ℂ G (h * (h⁻¹ * x * h))
    congr 1
    group

/-- **The class sum of the conjugacy class of an element is central.** Let $G$ be a finite group,
let $g \in G$, and let $\widehat{C_g} = \sum_{x \in C_g} x$ be the sum, in the complex group
algebra $\mathbb{C}[G]$, of the elements of the conjugacy class $C_g$ of $g$. Then
$w \widehat{C_g} = \widehat{C_g} w$ for every $w \in \mathbb{C}[G]$. -/
theorem classSum_central' (g : G) (w : MonoidAlgebra ℂ G) :
    w * classSum (conjClass g) = classSum (conjClass g) * w := by
  have hsingle : ∀ m r, MonoidAlgebra.single m r = r • MonoidAlgebra.of ℂ G m := by
    intro m r
    rw [MonoidAlgebra.of_apply, MonoidAlgebra.smul_single', mul_one]
  induction w using MonoidAlgebra.induction with
  | zero => simp
  | single_add m r x _ _ ih =>
    rw [add_mul, mul_add, ih]
    have h1 : MonoidAlgebra.single m r * classSum (conjClass g)
        = classSum (conjClass g) * MonoidAlgebra.single m r := by
      rw [hsingle m r, smul_mul_assoc, (classSum_central g m).symm,
        ← mul_smul_comm, ← hsingle m r]
    rw [h1]

/-- **Chosen representative of a conjugacy class.** For each conjugacy class $K$ of a group $G$,
the representative of $K$ is an element $g_K \in G$, fixed once and for all by choice, whose
conjugacy class is $K$. -/
noncomputable def classRep (l : ConjClasses G) : G :=
  Classical.choose (ConjClasses.mk_surjective l)

omit [Fintype G] in
theorem classRep_spec (l : ConjClasses G) : ConjClasses.mk (classRep l) = l :=
  Classical.choose_spec (ConjClasses.mk_surjective l)

open Classical in
/-- **Conjugacy class of the chosen representative.** Let $G$ be a finite group. For every
conjugacy class $K$ of $G$, the set of elements of $K$ equals the conjugacy class of the chosen
representative of $K$. -/
theorem carrier_toFinset (l : ConjClasses G) :
    (ConjClasses.carrier l).toFinset = conjClass (classRep l) := by
  rw [conjClass, Set.toFinset_inj, ConjAct.orbit_eq_carrier_conjClasses,
    classRep_spec l]

open Classical in
/-- **Structure constants of a pair of subsets.** Let $G$ be a finite group. For finite subsets
$C_i, C_j \subseteq G$ and an element $z \in G$, the structure constant is the number of pairs
$(x, y) \in C_i \times C_j$ with $xy = z$. -/
noncomputable def structConst (Ci Cj : Finset G) (z : G) : ℕ :=
  ((Ci.product Cj).filter (fun p => p.1 * p.2 = z)).card

/-- **Class structure constants are class functions.** Let $G$ be a finite group, let
$g_i, g_j \in G$ with conjugacy classes $C_{g_i}$ and $C_{g_j}$, and for $z \in G$ let $a(z)$ be
the number of pairs $(x, y) \in C_{g_i} \times C_{g_j}$ with $x y = z$. If $u, z \in G$ are
conjugate, then $a(u) = a(z)$. -/
theorem structConst_conj (gi gj u z : G) (h : IsConj u z) :
    structConst (conjClass gi) (conjClass gj) u =
      structConst (conjClass gi) (conjClass gj) z := by
  classical
  obtain ⟨c, hc⟩ := isConj_iff.mp h
  have hc' : c⁻¹ * z * c = u := by
    have h2 : c⁻¹ * (c * u * c⁻¹) * c = c⁻¹ * z * c :=
      congrArg (fun w => c⁻¹ * w * c) hc
    have e : c⁻¹ * (c * u * c⁻¹) * c = u := by group
    rw [e] at h2
    exact h2.symm
  unfold structConst
  refine Finset.card_bij' (fun p _ => (c * p.1 * c⁻¹, c * p.2 * c⁻¹))
    (fun p _ => (c⁻¹ * p.1 * c, c⁻¹ * p.2 * c)) ?_ ?_ ?_ ?_
  · intro p hp
    obtain ⟨hpmem, hpeq⟩ := Finset.mem_filter.mp hp
    obtain ⟨hx, hy⟩ := Finset.mem_product.mp hpmem
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_product.mpr ⟨?_, ?_⟩, ?_⟩
    · simpa using conj_mem_conjClass gi c p.1 hx
    · simpa using conj_mem_conjClass gj c p.2 hy
    · change (c * p.1 * c⁻¹) * (c * p.2 * c⁻¹) = z
      have e : (c * p.1 * c⁻¹) * (c * p.2 * c⁻¹) = c * (p.1 * p.2) * c⁻¹ := by group
      rw [e, hpeq, hc]
  · intro p hp
    obtain ⟨hpmem, hpeq⟩ := Finset.mem_filter.mp hp
    obtain ⟨hx, hy⟩ := Finset.mem_product.mp hpmem
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_product.mpr ⟨?_, ?_⟩, ?_⟩
    · simpa using conj_mem_conjClass gi c⁻¹ p.1 hx
    · simpa using conj_mem_conjClass gj c⁻¹ p.2 hy
    · change (c⁻¹ * p.1 * c) * (c⁻¹ * p.2 * c) = u
      have e : (c⁻¹ * p.1 * c) * (c⁻¹ * p.2 * c) = c⁻¹ * (p.1 * p.2) * c := by group
      rw [e, hpeq, hc']
  · intro p hp
    change (c⁻¹ * (c * p.1 * c⁻¹) * c, c⁻¹ * (c * p.2 * c⁻¹) * c) = p
    refine Prod.ext_iff.mpr ⟨?_, ?_⟩
    · change c⁻¹ * (c * p.1 * c⁻¹) * c = p.1
      group
    · change c⁻¹ * (c * p.2 * c⁻¹) * c = p.2
      group
  · intro p hp
    change (c * (c⁻¹ * p.1 * c) * c⁻¹, c * (c⁻¹ * p.2 * c) * c⁻¹) = p
    refine Prod.ext_iff.mpr ⟨?_, ?_⟩
    · change c * (c⁻¹ * p.1 * c) * c⁻¹ = p.1
      group
    · change c * (c⁻¹ * p.2 * c) * c⁻¹ = p.2
      group

omit [Fintype G] in
/-- **Coefficients of a product of class sums.** Let $G$ be a group, let $C_i$ and $C_j$ be
finite subsets of $G$, and write $\widehat{C} = \sum_{x \in C} x$ in the complex group algebra
$\mathbb{C}[G]$. For every $u \in G$, the coefficient of $u$ in $\widehat{C_i} \widehat{C_j}$ is
the number of pairs $(x, y) \in C_i \times C_j$ with $x y = u$. -/
theorem coeff_classSum_mul (Ci Cj : Finset G) (u : G) :
    (classSum Ci * classSum Cj).coeff u = (structConst Ci Cj u : ℂ) := by
  classical
  have hmul : classSum Ci * classSum Cj
      = ∑ x ∈ Ci, ∑ y ∈ Cj, MonoidAlgebra.single (x * y) 1 := by
    simp only [classSum]
    rw [Finset.sum_mul]
    simp only [Finset.mul_sum]
    simp only [MonoidAlgebra.of_apply, MonoidAlgebra.single_mul_single, mul_one]
  rw [hmul]
  simp only [MonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply,
    MonoidAlgebra.coeff_single, Finsupp.single_apply]
  have hprod : (∑ p ∈ Ci ×ˢ Cj, (if p.1 * p.2 = u then (1 : ℂ) else 0))
      = ∑ x ∈ Ci, ∑ y ∈ Cj, (if x * y = u then (1 : ℂ) else 0) :=
    Finset.sum_product Ci Cj _
  rw [← hprod, Finset.sum_boole]
  rfl

open Classical in
/-- **Products of class sums expand in class sums.** Let $G$ be a finite group. For a finite
subset $C$ of $G$ write $\widehat{C} = \sum_{x \in C} x$ in the complex group algebra
$\mathbb{C}[G]$, and for $g \in G$ let $C_g$ be its conjugacy class. Let $g_i, g_j \in G$, and for
each conjugacy class $K$ of $G$ with chosen representative $z_K$ let $a_K$ be the number of pairs
$(x, y) \in C_{g_i} \times C_{g_j}$ with $x y = z_K$. Then
$\widehat{C_{g_i}} \widehat{C_{g_j}} = \sum_K a_K \widehat{K}$, the sum running over all
conjugacy classes $K$ of $G$. -/
theorem classSum_mul (gi gj : G) :
    classSum (conjClass gi) * classSum (conjClass gj)
      = ∑ l : ConjClasses G, (structConst (conjClass gi) (conjClass gj) (classRep l) : ℂ)
          • classSum (ConjClasses.carrier l).toFinset := by
  classical
  rw [← MonoidAlgebra.coeff_inj, Finsupp.ext_iff]
  intro u
  rw [coeff_classSum_mul]
  simp only [MonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply,
    MonoidAlgebra.coeff_smul_apply, classSum, MonoidAlgebra.of_apply,
    MonoidAlgebra.coeff_single, Finsupp.single_apply, Finset.sum_ite_eq']
  simp only [smul_eq_mul, mul_ite, mul_one, mul_zero, Set.mem_toFinset,
    ConjClasses.mem_carrier_iff_mk_eq]
  rw [Finset.sum_ite_eq]
  simp only [Finset.mem_univ, ite_true]
  congr 1
  apply structConst_conj
  rw [← ConjClasses.mk_eq_mk_iff_isConj]
  exact (classRep_spec _).symm

/-- **Conjugate elements have the same conjugacy class.** Let $G$ be a finite group. If
$g_1, g_2 \in G$ are conjugate, then the conjugacy class of $g_1$ equals the conjugacy class of
$g_2$. -/
theorem conjClass_eq_of_isConj {g1 g2 : G} (h : IsConj g1 g2) :
    conjClass g1 = conjClass g2 := by
  ext x
  rw [mem_conjClass_iff, mem_conjClass_iff]
  exact ⟨fun hx => hx.trans h, fun hx => hx.trans (isConj_comm.mp h)⟩

open Classical in
/-- **Class sums of conjugacy classes are central.** Let $G$ be a finite group. For every
conjugacy class $K$ of $G$ and every element $w$ of the complex group algebra $\mathbb{C}[G]$,
the class sum $\widehat{K} = \sum_{x \in K} x$ satisfies $w \widehat{K} = \widehat{K} w$. -/
theorem classSum_carrier_central (l : ConjClasses G) (w : MonoidAlgebra ℂ G) :
    w * classSum (ConjClasses.carrier l).toFinset
      = classSum (ConjClasses.carrier l).toFinset * w := by
  rw [carrier_toFinset]
  exact classSum_central' _ w

end

end BurnsidePaqb
