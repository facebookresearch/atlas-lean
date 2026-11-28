/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
-- AI-assisted original formalization: Avocado; responsible human author: @toskua.
module

public import MathlibExt.GroupTheory.SchreierTransversal

/-!
# Schreier decompositions in a subgroup tower

Let H ≤ G and let K be a subgroup of H. If S is a right transversal for K in H and T a right
transversal for H in G, the products st form a right transversal for the image of K in G.
Decomposing stg first through T and then through S gives the same subgroup factor and
representative as decomposing through this product transversal.

For finite tuples, scan first through T to obtain H-valued factors, then scan those factors
through S. The resulting representative pairs and K-valued factor tuple are precisely those of
the product transversal.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open scoped BigOperators

namespace Subgroup.RightTransversal

universe u

variable {G : Type u} [Group G] {H : Subgroup G} {K : Subgroup H}

/-- A representative product in a subgroup tower.

For s ∈ S and t ∈ T, this map sends (s,t) to the ambient product st ∈ G, where S is a
K-transversal in H and T an H-transversal in G. -/
def productRep (S : K.RightTransversal) (T : H.RightTransversal)
    (p : ↥(S : Set H) × ↥(T : Set G)) : G :=
  ((p.1 : H) : G) * (p.2 : G)

/-- Uniqueness of pairs of product representatives.

If st = s′t′ for s,s′ ∈ S and t,t′ ∈ T, then (s,t) = (s′,t′). Thus the representative product
map S × T → G is injective. -/
theorem productRep_injective (S : K.RightTransversal)
    (T : H.RightTransversal) : Function.Injective (productRep S T) := by
  intro p q hpq
  have hpair : ((p.1 : H), p.2) = ((q.1 : H), q.2) :=
    T.2.1 hpq
  have hs : p.1 = q.1 := Subtype.ext
    (congrArg (fun r : H × ↥(T : Set G) => r.1) hpair)
  have ht : p.2 = q.2 :=
    congrArg (fun r : H × ↥(T : Set G) => r.2) hpair
  exact Prod.ext hs ht

/-- The set of product representatives.

This is the subset of G consisting of all st with s ∈ S and t ∈ T. -/
def productSet (S : K.RightTransversal) (T : H.RightTransversal) : Set G :=
  Set.range (productRep S T)

/-- Pair coordinates on the product representative set.

The injective product map identifies S × T with its image {st | s ∈ S, t ∈ T} in G. -/
noncomputable def productRepEquiv (S : K.RightTransversal)
    (T : H.RightTransversal) :
    ↥(S : Set H) × ↥(T : Set G) ≃ ↥(productSet S T : Set G) :=
  Equiv.ofInjective (productRep S T) (productRep_injective S T)

/-- Ambient values of the product-set equivalence.

The representative corresponding to (s,t) has ambient value st ∈ G. -/
@[simp]
theorem productRepEquiv_coe_apply (S : K.RightTransversal)
    (T : H.RightTransversal) (p : ↥(S : Set H) × ↥(T : Set G)) :
    ((productRepEquiv S T p : ↥(productSet S T : Set G)) : G) =
      productRep S T p :=
  rfl

/-- Decomposition through two successive transversals.

This equivalence sends G to the product of the image of K in G and the product representative
set. It decomposes first through T, then decomposes the H-factor through S; its inverse
multiplies the two ambient components. -/
noncomputable def productDecompositionEquiv (S : K.RightTransversal)
    (T : H.RightTransversal) :
    G ≃ (K.map H.subtype) × ↥(productSet S T : Set G) where
  toFun g :=
    let ht := T.2.equiv g
    let hs := S.2.equiv ht.1
    (K.equivMapOfInjective H.subtype H.subtype_injective hs.1,
      productRepEquiv S T (hs.2, ht.2))
  invFun p := (p.1 : G) * (p.2 : G)
  left_inv g := by
    let ht := T.2.equiv g
    let hs := S.2.equiv ht.1
    change (((hs.1 : K) : H) : G) *
        (((hs.2 : H) : G) * (ht.2 : G)) = g
    rw [← mul_assoc]
    have hsMul := S.2.equiv_fst_mul_equiv_snd ht.1
    have htMul := T.2.equiv_fst_mul_equiv_snd g
    rw [show (((hs.1 : K) : H) : G) * ((hs.2 : H) : G) =
        (ht.1 : G) by exact congrArg H.subtype hsMul]
    exact htMul
  right_inv p := by
    let eK := K.equivMapOfInjective H.subtype H.subtype_injective
    let st := (productRepEquiv S T).symm p.2
    let k := eK.symm p.1
    have hk : (eK k : G) = (p.1 : G) := by
      exact congrArg Subtype.val (eK.apply_symm_apply p.1)
    have hst : productRep S T st = (p.2 : G) := by
      exact congrArg Subtype.val ((productRepEquiv S T).apply_symm_apply p.2)
    apply Prod.ext
    · apply Subtype.ext
      change ((eK (S.2.equiv (T.2.equiv ((p.1 : G) * (p.2 : G))).1).1 :
        K.map H.subtype) : G) = (p.1 : G)
      rw [← hk, ← hst]
      rcases st with ⟨s, t⟩
      change ((eK (S.2.equiv
          (T.2.equiv ((((k : K) : H) : G) *
            (((s : H) : G) * (t : G)))).1).1 :
        K.map H.subtype) : G) = (((k : K) : H) : G)
      rw [← mul_assoc]
      rw [show (((k : K) : H) : G) * ((s : H) : G) =
          ((((k : K) : H) * (s : H) : H) : G) by rfl]
      rw [← T.2.equiv_symm_apply
        ((((k : K) : H) * (s : H) : H), t), Equiv.apply_symm_apply]
      rw [← S.2.equiv_symm_apply ((k, s)), Equiv.apply_symm_apply]
      rfl
    · apply Subtype.ext
      change productRep S T
          ((S.2.equiv (T.2.equiv ((p.1 : G) * (p.2 : G))).1).2,
            (T.2.equiv ((p.1 : G) * (p.2 : G))).2) =
        (p.2 : G)
      rw [← hk, ← hst]
      rcases st with ⟨s, t⟩
      change productRep S T
          ((S.2.equiv
              (T.2.equiv ((((k : K) : H) : G) *
                (((s : H) : G) * (t : G)))).1).2,
            (T.2.equiv ((((k : K) : H) : G) *
              (((s : H) : G) * (t : G)))).2) =
        productRep S T (s, t)
      rw [← mul_assoc]
      rw [show (((k : K) : H) : G) * ((s : H) : G) =
          ((((k : K) : H) * (s : H) : H) : G) by rfl]
      rw [← T.2.equiv_symm_apply
        ((((k : K) : H) * (s : H) : H), t), Equiv.apply_symm_apply]
      rw [← S.2.equiv_symm_apply ((k, s)), Equiv.apply_symm_apply]

/-- The product right transversal.

The set of products st with s ∈ S and t ∈ T is a right transversal for K mapped into G along
the subgroup inclusion H → G. -/
noncomputable def product (S : K.RightTransversal)
    (T : H.RightTransversal) : (K.map H.subtype).RightTransversal :=
  ⟨productSet S T, (productDecompositionEquiv S T).symm.bijective⟩

/-- Pair coordinates on the product transversal.

The product transversal for the image of K in G is equivalent to S × T by (s,t) ↦ st. -/
noncomputable def productEquiv (S : K.RightTransversal)
    (T : H.RightTransversal) :
    ↥(S : Set H) × ↥(T : Set G) ≃ ↥((product S T : Set G)) :=
  productRepEquiv S T

/-- Ambient values of product-transversal coordinates.

Under the pair-coordinate equivalence, the element corresponding to (s,t) has value st in G. -/
@[simp]
theorem productEquiv_coe_apply (S : K.RightTransversal)
    (T : H.RightTransversal) (p : ↥(S : Set H) × ↥(T : Set G)) :
    ((productEquiv S T p : ↥((product S T : Set G))) : G) =
      productRep S T p :=
  rfl

/-- The two-step decomposition of a product representative.

Write tg = ht′ using T, and then sh = ks′ using S. The product transversal decomposes stg with
subgroup factor k mapped into G and representative s′t′. -/
theorem product_schreierDecomposition (S : K.RightTransversal)
    (T : H.RightTransversal) (s : (S : Set H)) (t : (T : Set G))
    (g : G) :
    let h := T.schreierFactor t g
    let t' := T.schreierRep t g
    let k := S.schreierFactor s h
    let s' := S.schreierRep s h
    let r := productEquiv S T (s, t)
    ((product S T).schreierFactor r g,
        (product S T).schreierRep r g) =
      (K.equivMapOfInjective H.subtype H.subtype_injective k,
        productEquiv S T (s', t')) := by
  dsimp only
  apply (product S T).2.1
  calc
    ((product S T).schreierFactor (productEquiv S T (s, t)) g : G) *
        ((product S T).schreierRep (productEquiv S T (s, t)) g : G) =
      (productEquiv S T (s, t) : G) * g :=
        (product S T).schreierFactor_mul_schreierRep
          (productEquiv S T (s, t)) g
    _ = ((K.equivMapOfInjective H.subtype H.subtype_injective
          (S.schreierFactor s (T.schreierFactor t g)) :
            K.map H.subtype) : G) *
        (productEquiv S T
          (S.schreierRep s (T.schreierFactor t g),
            T.schreierRep t g) : G) := by
      change (productRep S T (s, t)) * g =
        (((S.schreierFactor s (T.schreierFactor t g) : K) : H) : G) *
          productRep S T
            (S.schreierRep s (T.schreierFactor t g), T.schreierRep t g)
      unfold productRep
      rw [← mul_assoc]
      rw [show
        (((S.schreierFactor s (T.schreierFactor t g) : K) : H) : G) *
            ((S.schreierRep s (T.schreierFactor t g) : H) : G) =
          (((s : H) * T.schreierFactor t g : H) : G) by
            exact congrArg H.subtype
              (S.schreierFactor_mul_schreierRep s (T.schreierFactor t g))]
      simp only [Subgroup.coe_mul]
      rw [mul_assoc, ← T.schreierFactor_mul_schreierRep, ← mul_assoc]

/-- The representative from two successive Schreier steps.

Starting at st, the product-transversal representative after g is the product of
r_S(s,a_T(t,g)) and r_T(t,g). -/
theorem product_schreierRep (S : K.RightTransversal)
    (T : H.RightTransversal) (s : (S : Set H)) (t : (T : Set G))
    (g : G) :
    (product S T).schreierRep (productEquiv S T (s, t)) g =
      productEquiv S T
        (S.schreierRep s (T.schreierFactor t g), T.schreierRep t g) := by
  have h := congrArg
    (fun p : (K.map H.subtype) × ↥(productSet S T : Set G) => p.2)
    (product_schreierDecomposition S T s t g)
  exact h

/-- The subgroup factor from two successive Schreier steps.

Starting at st, the product-transversal factor after g is the image in G of a_S(s,a_T(t,g)) ∈
K. -/
theorem product_schreierFactor (S : K.RightTransversal)
    (T : H.RightTransversal) (s : (S : Set H)) (t : (T : Set G))
    (g : G) :
    (product S T).schreierFactor (productEquiv S T (s, t)) g =
      K.equivMapOfInjective H.subtype H.subtype_injective
        (S.schreierFactor s (T.schreierFactor t g)) := by
  have h := congrArg
    (fun p : (K.map H.subtype) × ↥(productSet S T : Set G) => p.1)
    (product_schreierDecomposition S T s t g)
  exact h

end Subgroup.RightTransversal

namespace Subgroup.RightTransversal

universe u

variable {G : Type u} [Group G] {H : Subgroup G} {K : Subgroup H}

/-- Representative scans through a subgroup tower.

For g : Fin n → G, the product-transversal scan at i is the product-coordinate pair formed by
the S-scan of the T-factor tuple at i and the T-scan of g at i. -/
theorem product_schreierRepScan {n : ℕ}
    (S : K.RightTransversal) (T : H.RightTransversal)
    (s : (S : Set H)) (t : (T : Set G)) (g : Fin n → G)
    (i : Fin (n + 1)) :
    (S.product T).schreierRepScan (S.productEquiv T (s, t)) g i =
      S.productEquiv T
        (S.schreierRepScan s (T.schreierFactorTuple t g) i,
          T.schreierRepScan t g i) := by
  induction i using Fin.induction with
  | zero =>
      simp only [schreierRepScan_get_zero]
  | succ i ih =>
      rw [schreierRepScan_get_succ, ih,
        S.product_schreierRep T,
        schreierRepScan_get_succ, schreierRepScan_get_succ]
      rfl

/-- Factor tuples through a subgroup tower.

The factor tuple of the product transversal is obtained by scanning the T-factor tuple through
S and mapping each resulting K-element into the subgroup image in G. -/
theorem product_schreierFactorTuple {n : ℕ}
    (S : K.RightTransversal) (T : H.RightTransversal)
    (s : (S : Set H)) (t : (T : Set G)) (g : Fin n → G) :
    (S.product T).schreierFactorTuple (S.productEquiv T (s, t)) g =
      fun i ↦ K.equivMapOfInjective H.subtype H.subtype_injective
        (S.schreierFactorTuple s (T.schreierFactorTuple t g) i) := by
  funext i
  unfold schreierFactorTuple
  rw [S.product_schreierRepScan T]
  exact S.product_schreierFactor T
    (S.schreierRepScan s (T.schreierFactorTuple t g) i.castSucc)
    (T.schreierRepScan t g i.castSucc) (g i)

end Subgroup.RightTransversal
