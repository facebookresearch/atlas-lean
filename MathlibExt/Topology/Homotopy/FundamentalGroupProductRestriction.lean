/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.Topology.Homotopy.FundamentalGroupProduct
public import MathlibExt.AlgebraicTopology.FundamentalGroupoid.PiOneMapComposition

/-!
# The original inactive axis in the product fundamental group

The literal second-axis inclusion corresponds to the pair (1,p) under the
original projection equivalence. Therefore an original product class with
trivial first projection is that actual axis image. This calibrates killing
of the product subgroup by the actual whole map and its inactive restriction.
-/

set_option autoImplicit false

noncomputable section

open CategoryTheory

universe u v w

namespace FundamentalGroup

variable {A : Type u} {X : Type v} {Y : Type w}
  [TopologicalSpace A] [TopologicalSpace X] [TopologicalSpace Y]

/-- The original second-axis inclusion at the selected active point. -/
public abbrev secondProductInclusion (a : A) : C(X, A × X) :=
  (ContinuousMap.const X a).prodMk (ContinuousMap.id X)

private theorem map_secondProductInclusion_recipe (a : A) (x : X)
    (p : FundamentalGroup X x) :
    mapOfEq (x := x) (y := (a, x)) (secondProductInclusion a) rfl p =
      (productMulEquiv a x).symm (1, p) := by
  have hi : secondProductInclusion a x = (a, x) := rfl
  change mapOfEq (x := x) (y := (a, x)) (secondProductInclusion a) hi p =
    (productMulEquiv a x).symm (1, p)
  rw [productMulEquiv_symm_apply]
  apply End.ext
  have hmap :
      (mapOfEq (x := x) (y := (a, x)) (secondProductInclusion a) hi p).asHom =
        (Path.Homotopic.Quotient.map p.asHom (secondProductInclusion a)).cast
          hi.symm hi.symm :=
    congrArg (fun q : FundamentalGroup (A × X) (a, x) => q.asHom)
      (mapOfEq_apply (secondProductInclusion a) hi p)
  refine hmap.trans ?_
  obtain ⟨γ, hγ⟩ := Path.Homotopic.Quotient.mk_surjective p.asHom
  rw [← hγ]
  change Path.Homotopic.Quotient.mk
      ((γ.map (secondProductInclusion a).continuous).cast hi.symm hi.symm) =
    Path.Homotopic.Quotient.mk ((Path.refl a).prod γ)
  apply congrArg Path.Homotopic.Quotient.mk
  apply Path.ext
  funext t
  rfl

/-- The actual inactive-axis map has the pair (1,p) as its original
projection coordinates. -/
public theorem productMulEquiv_map_secondProductInclusion (a : A) (x : X)
    (p : FundamentalGroup X x) :
    productMulEquiv a x
      (mapOfEq (x := x) (y := (a, x)) (secondProductInclusion a) rfl p) = (1, p) := by
  exact (congrArg (fun q : FundamentalGroup (A × X) (a, x) => productMulEquiv a x q)
    (map_secondProductInclusion_recipe a x p)).trans
      ((productMulEquiv a x).apply_symm_apply (1, p))

/-- Every original class with trivial first projection is the literal
second-axis image of its original second projection. -/
public theorem eq_secondProductInclusion_of_first_one (a : A) (x : X)
    (p : FundamentalGroup (A × X) (a, x))
    (h : (productMulEquiv a x p).1 = 1) :
    mapOfEq (x := x) (y := (a, x)) (secondProductInclusion a) rfl
      (productMulEquiv a x p).2 = p := by
  apply (productMulEquiv a x).injective
  exact (productMulEquiv_map_secondProductInclusion a x (productMulEquiv a x p).2).trans
    (Prod.ext h.symm rfl)

/-- Killing the original inactive restriction kills the exact original
product subgroup with trivial first coordinate, without a substituted
product map or quotient witness. -/
public theorem mapOfEq_product_subgroup_bot_left_eq_one
    (a : A) (x : X) (P : Subgroup (FundamentalGroup X x))
    (φ : C(A × X, Y))
    (hk : ∀ q ∈ P, mapOfEq (φ.comp (secondProductInclusion a)) rfl q = 1)
    (p : FundamentalGroup (A × X) (a, x))
    (hp : p ∈ ((⊥ : Subgroup (FundamentalGroup A a)).prod P).comap
      (productMulEquiv a x).toMonoidHom) :
    mapOfEq φ rfl p = 1 := by
  let y : Y := φ (a, x)
  let i : C(X, A × X) := secondProductInclusion a
  have hi : i x = (a, x) := rfl
  have hφ : φ (a, x) = y := rfl
  have hcomp : (φ.comp i) x = y := by
    change φ (i x) = y
    exact (congrArg φ hi).trans hφ
  let I : FundamentalGroup X x →* FundamentalGroup (A × X) (a, x) :=
    mapOfEq (x := x) (y := (a, x)) i hi
  let F : FundamentalGroup (A × X) (a, x) →* FundamentalGroup Y y :=
    mapOfEq (x := (a, x)) (y := y) φ hφ
  let K : FundamentalGroup X x →* FundamentalGroup Y y :=
    mapOfEq (x := x) (y := y) (φ.comp i) hcomp
  have hpair : (productMulEquiv a x p).1 ∈ (⊥ : Subgroup (FundamentalGroup A a)) ∧
      (productMulEquiv a x p).2 ∈ P := hp
  let q : FundamentalGroup X x := (productMulEquiv a x p).2
  have he : I q = p :=
    eq_secondProductInclusion_of_first_one a x p (Subgroup.mem_bot.mp hpair.1)
  have hc : K = F.comp I :=
    mapOfEq_comp (x := x) (y := (a, x)) (z := y) i φ hi hφ hcomp
  have hcompq : F (I q) = K q := by
    change (F.comp I) q = K q
    exact congrArg (fun m : FundamentalGroup X x →* FundamentalGroup Y y => m q) hc.symm
  have hkill : K q = 1 := hk q hpair.2
  change F p = 1
  exact (congrArg (fun r : FundamentalGroup (A × X) (a, x) => F r) he.symm).trans
    (hcompq.trans hkill)

end FundamentalGroup

end
