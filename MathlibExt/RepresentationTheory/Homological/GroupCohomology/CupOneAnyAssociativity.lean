/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.RepresentationTheory.Homological.GroupCohomology.CupOneAny
public import MathlibExt.RepresentationTheory.Homological.GroupCohomology.CupProductAssociativity
public import MathlibExt.RepresentationTheory.Homological.GroupCohomology.CupProductDegreeTransport

/-!
# Associativity in degrees one, arbitrary degree, and one

Let `G` be a group, `k` a commutative ring, and `A,B,C` representations. For classes of
degrees `1,q,1`, the cup with target degree written `q + 1` satisfies `α_*((x ∪ y) ∪ z) = x ∪
(y ∪ z)` in `H^{q+2}(G,A ⊗ (B ⊗ C))`. Here `α : (A ⊗ B) ⊗ C → A ⊗ (B ⊗ C)` is the coefficient
associator, and `cupOneAny` uses the canonical identification `1 + q = q + 1`.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false

open CategoryTheory MonoidalCategory

namespace groupCohomology

universe u

variable {k G : Type u} [CommRing k] [Group G]

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
/-- Let `A,B,C` be representations of a group `G` over a commutative ring `k`, `q : ℕ`, and `x ∈
H¹(G,A)`, `y ∈ H^q(G,B)`, `z ∈ H¹(G,C)`. Applying the coefficient associator in degree `q + 2`
to `cup_{q+1,1}(cupOneAny A B q (x ⊗ y) ⊗ z)` equals `cupOneAny A (B ⊗ C) (q + 1) (x ⊗
cup_{q,1}(y ⊗ z))`. Both sides lie in `H^{q+2}(G,A ⊗ (B ⊗ C))`. -/
theorem cupOneAny_assoc_right_one
    (A B C : Rep k G) (q : ℕ)
    (x : groupCohomology A 1) (y : groupCohomology B q)
    (z : groupCohomology C 1) :
    (groupCohomology.map (MonoidHom.id G) (α_ A B C).hom (q + 2)).hom
        ((cup G k (A ⊗ B) C (q + 1) 1).hom
          (cupOneAny A B q (x ⊗ₜ[k] y) ⊗ₜ[k] z)) =
      cupOneAny A (B ⊗ C) (q + 1)
        (x ⊗ₜ[k] (cup G k B C q 1).hom (y ⊗ₜ[k] z)) := by
  let h := Nat.one_add q
  let hLeft := congrArg (fun r => r + 1) h
  let hAssoc := Nat.add_assoc 1 q 1
  let hRight := Nat.one_add (q + 1)
  let u := (cup G k A B 1 q).hom (x ⊗ₜ[k] y)
  let v := (cup G k (A ⊗ B) C (1 + q) 1).hom (u ⊗ₜ[k] z)
  let w := (groupCohomology.map (MonoidHom.id G)
    (α_ A B C).hom ((1 + q) + 1)).hom v
  have houter := ConcreteCategory.congr_hom
    (cup_left_degree_transport (A ⊗ B) C h 1) (u ⊗ₜ[k] z)
  have houter_apply :
      (cup G k (A ⊗ B) C (q + 1) 1).hom
          (((inhomogeneousCochains (A ⊗ B)).homologyIsoOfEq h).hom.hom u
            ⊗ₜ[k] z) =
        ((inhomogeneousCochains ((A ⊗ B) ⊗ C)).homologyIsoOfEq
          hLeft).hom.hom v := by
    convert houter using 1
    simp only [ConcreteCategory.comp_apply,
      ModuleCat.MonoidalCategory.tensorHom_tmul,
      ConcreteCategory.id_apply]
    rfl
  have hnat := ConcreteCategory.congr_hom
    (HomologicalComplex.homologyIsoOfEq_hom_naturality
      (groupCohomology.cochainsMap (MonoidHom.id G) (α_ A B C).hom)
      hLeft) v
  have hnat_apply :
      (groupCohomology.map (MonoidHom.id G) (α_ A B C).hom (q + 2)).hom
          (((inhomogeneousCochains ((A ⊗ B) ⊗ C)).homologyIsoOfEq
            hLeft).hom.hom v) =
        ((inhomogeneousCochains (A ⊗ (B ⊗ C))).homologyIsoOfEq
          hLeft).hom.hom w := by
    exact hnat.symm
  have hassoc := cup_assoc_tmul G k A B C 1 q 1 x y z
  have hassoc_apply :
      ((inhomogeneousCochains (A ⊗ (B ⊗ C))).homologyIsoOfEq
        hAssoc).hom.hom w =
        (cup G k A (B ⊗ C) 1 (q + 1)).hom
          (x ⊗ₜ[k] (cup G k B C q 1).hom (y ⊗ₜ[k] z)) := by
    exact hassoc
  have hproof : hAssoc.trans hRight = hLeft := Subsingleton.elim _ _
  have hcomp := ConcreteCategory.congr_hom
    (homologyIsoOfEq_hom_comp (A ⊗ (B ⊗ C)) hAssoc hRight) w
  have hcasts :
      ((inhomogeneousCochains (A ⊗ (B ⊗ C))).homologyIsoOfEq
        hLeft).hom.hom w =
        ((inhomogeneousCochains (A ⊗ (B ⊗ C))).homologyIsoOfEq
          hRight).hom.hom
          (((inhomogeneousCochains (A ⊗ (B ⊗ C))).homologyIsoOfEq
            hAssoc).hom.hom w) := by
    rw [← hproof]
    exact hcomp.symm
  unfold cupOneAny
  simp only [ConcreteCategory.comp_apply]
  change (groupCohomology.map (MonoidHom.id G)
      (α_ A B C).hom (q + 2)).hom
      ((cup G k (A ⊗ B) C (q + 1) 1).hom
        (((inhomogeneousCochains (A ⊗ B)).homologyIsoOfEq h).hom.hom u
          ⊗ₜ[k] z)) = _
  rw [houter_apply, hnat_apply, hcasts, hassoc_apply]
  rfl

end groupCohomology
