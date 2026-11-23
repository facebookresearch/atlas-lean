/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  MathlibExt.AlgebraicTopology.SimplicialSet.FundamentalGroupoid.Basic
public import MathlibExt.AlgebraicTopology.SingularHomology.Integral
public import Mathlib.GroupTheory.Abelianization.Defs

/-!
# Degree-one chains and the simplicial fundamental groupoid

This file begins the combinatorial comparison between the abelianized
fundamental group of a connected simplicial set and its integral homology in
degree one.  It constructs the quotient one-chain groupoid: its morphisms are
integral one-chains with prescribed boundary, modulo two-boundaries.  Edges
map to their chain classes, and the boundary of a two-simplex supplies the
composition relation, so the construction descends from the simplicial
fundamental groupoid.

The connector-based map on based fundamental groups is also packaged here.
This packet does not yet construct the connected inverse, an H1/abelianized-
pi1 isomorphism, or its naturality.  It makes no generic topological
Hurewicz, finite-BGL, kernel, plus-construction, or `Q = +` claim.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits Opposite Simplicial
open scoped Simplicial

universe u

namespace SSet

/-- A simplicial map and an isomorphism from the literal image of the source
base vertex to a selected target base vertex induce a homomorphism of based
fundamental groups. -/
noncomputable def basedFundamentalGroupHom
    {X Y : SSet.{u}} (f : X ⟶ Y)
    (x : X _⦋0⦌) (y : Y _⦋0⦌)
    (e : (SSet.mapFundamentalGroupoid f).obj
          (SSet.FundamentalGroupoid.mk x) ≅
        SSet.FundamentalGroupoid.mk y) :
    End (SSet.FundamentalGroupoid.mk x) →*
      End (SSet.FundamentalGroupoid.mk y) :=
  e.conj.toMonoidHom.comp
    ((SSet.mapFundamentalGroupoid f).mapEnd
      (SSet.FundamentalGroupoid.mk x))

@[simp]
theorem basedFundamentalGroupHom_apply
    {X Y : SSet.{u}} (f : X ⟶ Y)
    (x : X _⦋0⦌) (y : Y _⦋0⦌)
    (e : (SSet.mapFundamentalGroupoid f).obj
          (SSet.FundamentalGroupoid.mk x) ≅
        SSet.FundamentalGroupoid.mk y)
    (q : End (SSet.FundamentalGroupoid.mk x)) :
    basedFundamentalGroupHom f x y e q =
      End.of (e.inv ≫ (SSet.mapFundamentalGroupoid f).map q.asHom ≫ e.hom) :=
  rfl

/-- Integral one-chains of a simplicial set. -/
noncomputable abbrev integralOneChains (X : SSet.{u}) : Type u :=
  (X.chainComplex
    (AlgebraicTopology.singularIntegralCoefficients :
      AddCommGrpCat.{u})).X 1

/-- Integral zero-chains of a simplicial set. -/
noncomputable abbrev integralZeroChains (X : SSet.{u}) : Type u :=
  (X.chainComplex
    (AlgebraicTopology.singularIntegralCoefficients :
      AddCommGrpCat.{u})).X 0

/-- Integral two-chains of a simplicial set. -/
noncomputable abbrev integralTwoChains (X : SSet.{u}) : Type u :=
  (X.chainComplex
    (AlgebraicTopology.singularIntegralCoefficients :
      AddCommGrpCat.{u})).X 2

/-- The subgroup of integral one-chains which are boundaries of
two-chains. -/
noncomputable def oneChainBoundaries (X : SSet.{u}) :
    AddSubgroup (integralOneChains X) :=
  AddMonoidHom.range
    ((X.chainComplex
      (AlgebraicTopology.singularIntegralCoefficients :
        AddCommGrpCat.{u})).d 2 1).hom

/-- Integral one-chains modulo two-boundaries. -/
noncomputable abbrev oneChainQuotient (X : SSet.{u}) : Type u :=
  integralOneChains X ⧸ oneChainBoundaries X

/-- The one-chain boundary descends through the quotient by
two-boundaries. -/
noncomputable def oneChainBoundary (X : SSet.{u}) :
    oneChainQuotient X →+ integralZeroChains X := by
  let K := X.chainComplex
    (AlgebraicTopology.singularIntegralCoefficients :
      AddCommGrpCat.{u})
  refine QuotientAddGroup.lift (oneChainBoundaries X) (K.d 1 0).hom ?_
  rintro z ⟨a, rfl⟩
  change (K.d 1 0) ((K.d 2 1) a) = 0
  exact ConcreteCategory.congr_hom (K.d_comp_d 2 1 0) a

@[simp]
theorem oneChainBoundary_mk (X : SSet.{u})
    (c : integralOneChains X) :
    oneChainBoundary X (QuotientAddGroup.mk' (oneChainBoundaries X) c) =
      ((X.chainComplex
        (AlgebraicTopology.singularIntegralCoefficients :
          AddCommGrpCat.{u})).d 1 0) c :=
  rfl

/-- The integral zero-chain represented by a vertex. -/
noncomputable def vertexChain (X : SSet.{u}) (x : X _⦋0⦌) :
    integralZeroChains X :=
  (X.ιChainComplex
    (R := AlgebraicTopology.singularIntegralCoefficients) x).hom
      (ULift.up (1 : ℤ))

/-- The integral one-chain represented by a one-simplex. -/
noncomputable def simplexOneChain (X : SSet.{u}) (s : X _⦋1⦌) :
    integralOneChains X :=
  (X.ιChainComplex
    (R := AlgebraicTopology.singularIntegralCoefficients) s).hom
      (ULift.up (1 : ℤ))

/-- The integral two-chain represented by a two-simplex. -/
noncomputable def simplexTwoChain (X : SSet.{u}) (s : X _⦋2⦌) :
    integralTwoChains X :=
  (X.ιChainComplex
    (R := AlgebraicTopology.singularIntegralCoefficients) s).hom
      (ULift.up (1 : ℤ))

/-- The class modulo two-boundaries of an edge's underlying one-simplex. -/
noncomputable def edgeOneChainClass
    {X : SSet.{u}} {x y : X _⦋0⦌} (e : X.Edge x y) :
    oneChainQuotient X :=
  QuotientAddGroup.mk' (oneChainBoundaries X)
    (simplexOneChain X e.edge)

/-- The boundary of an edge class is target minus source. -/
theorem oneChainBoundary_edgeOneChainClass
    {X : SSet.{u}} {x y : X _⦋0⦌} (e : X.Edge x y) :
    oneChainBoundary X (edgeOneChainClass e) =
      vertexChain X y - vertexChain X x := by
  rw [edgeOneChainClass, oneChainBoundary_mk]
  let K := X.chainComplex
    (AlgebraicTopology.singularIntegralCoefficients :
      AddCommGrpCat.{u})
  calc
    (K.d 1 0) (simplexOneChain X e.edge) =
        vertexChain X (X.δ 0 e.edge) -
          vertexChain X (X.δ 1 e.edge) := by
      change (X.ιChainComplex e.edge ≫ K.d 1 0)
          (ULift.up (1 : ℤ)) =
        (X.ιChainComplex
          (R := AlgebraicTopology.singularIntegralCoefficients)
          (X.δ 0 e.edge)).hom (ULift.up (1 : ℤ)) -
          (X.ιChainComplex
            (R := AlgebraicTopology.singularIntegralCoefficients)
            (X.δ 1 e.edge)).hom (ULift.up (1 : ℤ))
      rw [X.ιChainComplex_d]
      change (∑ i : Fin 2, ((-1 : ℤ) ^ i.val) •
        (X.ιChainComplex
          (R := AlgebraicTopology.singularIntegralCoefficients)
          (X.δ i e.edge)).hom (ULift.up (1 : ℤ))) = _
      simp [Fin.sum_univ_two, sub_eq_add_neg]
    _ = vertexChain X y - vertexChain X x := by
      rw [e.tgt_eq, e.src_eq]

/-- Objects of the quotient one-chain groupoid are vertices of the
simplicial set. -/
structure OneChainGroupoid (X : SSet.{u}) where
  /-- The represented vertex. -/
  vertex : X _⦋0⦌

namespace OneChainGroupoid

/-- A quotient one-chain from `a` to `b` has boundary `b - a`. -/
def Hom {X : SSet.{u}} (a b : OneChainGroupoid X) :=
  {q : oneChainQuotient X //
    oneChainBoundary X q = vertexChain X b.vertex - vertexChain X a.vertex}

instance (X : SSet.{u}) : Category (OneChainGroupoid X) where
  Hom a b := Hom a b
  id a := ⟨0, by simp⟩
  comp q r := ⟨q.val + r.val, by
    rw [map_add, q.2, r.2]
    abel⟩
  id_comp q := Subtype.ext (zero_add q.val)
  comp_id q := Subtype.ext (add_zero q.val)
  assoc q r s := Subtype.ext (add_assoc q.val r.val s.val)

instance (X : SSet.{u}) : Groupoid (OneChainGroupoid X) where
  inv q := ⟨-q.val, by
    rw [map_neg, q.2]
    abel⟩
  inv_comp q := Subtype.ext (neg_add_cancel q.val)
  comp_inv q := Subtype.ext (add_neg_cancel q.val)

/-- An edge defines the corresponding morphism in the quotient one-chain
groupoid. -/
noncomputable def edgeHom
    {X : SSet.{u}} {x y : X _⦋0⦌} (e : X.Edge x y) :
    mk x ⟶ mk y :=
  ⟨edgeOneChainClass e, oneChainBoundary_edgeOneChainClass e⟩

/-- The boundary of a two-simplex identifies the sum of its two short edges
with its long edge in the quotient one-chain groupoid. -/
theorem edgeHom_comp
    {X : SSet.{u}} {x₀ x₁ x₂ : X _⦋0⦌}
    {e₀₁ : X.Edge x₀ x₁} {e₁₂ : X.Edge x₁ x₂}
    {e₀₂ : X.Edge x₀ x₂}
    (h : SSet.Edge.CompStruct e₀₁ e₁₂ e₀₂) :
    edgeHom e₀₁ ≫ edgeHom e₁₂ = edgeHom e₀₂ := by
  apply Subtype.ext
  change edgeOneChainClass e₀₁ + edgeOneChainClass e₁₂ =
    edgeOneChainClass e₀₂
  change ((simplexOneChain X e₀₁.edge + simplexOneChain X e₁₂.edge :
      integralOneChains X) : oneChainQuotient X) =
    ((simplexOneChain X e₀₂.edge : integralOneChains X) :
      oneChainQuotient X)
  rw [QuotientAddGroup.eq_iff_sub_mem]
  change simplexOneChain X e₀₁.edge + simplexOneChain X e₁₂.edge -
      simplexOneChain X e₀₂.edge ∈
    AddMonoidHom.range
      ((X.chainComplex
        (AlgebraicTopology.singularIntegralCoefficients :
          AddCommGrpCat.{u})).d 2 1).hom
  refine ⟨simplexTwoChain X h.simplex, ?_⟩
  let K := X.chainComplex
    (AlgebraicTopology.singularIntegralCoefficients :
      AddCommGrpCat.{u})
  change (K.d 2 1) (simplexTwoChain X h.simplex) = _
  change (X.ιChainComplex h.simplex ≫ K.d 2 1)
      (ULift.up (1 : ℤ)) = _
  rw [X.ιChainComplex_d]
  change (∑ i : Fin 3, ((-1 : ℤ) ^ i.val) •
    (X.ιChainComplex
      (R := AlgebraicTopology.singularIntegralCoefficients)
      (X.δ i h.simplex)).hom (ULift.up (1 : ℤ))) = _
  rw [Fin.sum_univ_three, h.d₀, h.d₁, h.d₂]
  norm_num [simplexOneChain]
  abel

end OneChainGroupoid

/-- The canonical functor from the simplicial fundamental groupoid to the
quotient one-chain groupoid. -/
noncomputable def fundamentalGroupoidToOneChainGroupoid (X : SSet.{u}) :
    SSet.FundamentalGroupoid X ⥤ OneChainGroupoid X :=
  SSet.FundamentalGroupoid.desc
    (fun x ↦ OneChainGroupoid.mk x)
    (fun e ↦ OneChainGroupoid.edgeHom e)
    (fun h ↦ OneChainGroupoid.edgeHom_comp h)

@[simp]
theorem fundamentalGroupoidToOneChainGroupoid_obj_mk
    (X : SSet.{u}) (x : X _⦋0⦌) :
    (fundamentalGroupoidToOneChainGroupoid X).obj
        (SSet.FundamentalGroupoid.mk x) =
      OneChainGroupoid.mk x :=
  rfl

@[simp]
theorem fundamentalGroupoidToOneChainGroupoid_map_homMk
    (X : SSet.{u}) {x y : X _⦋0⦌} (e : X.Edge x y) :
    (fundamentalGroupoidToOneChainGroupoid X).map
        (SSet.FundamentalGroupoid.homMk e) =
      OneChainGroupoid.edgeHom e :=
  SSet.FundamentalGroupoid.desc_map_homMk _ _ _ e

/-- Integral one-cycles, in the concrete `AddMonoidHom.ker` model. -/
noncomputable abbrev integralOneCycles (X : SSet.{u}) : Type u :=
  AddMonoidHom.ker
    ((X.chainComplex
      (AlgebraicTopology.singularIntegralCoefficients :
        AddCommGrpCat.{u})).d 1 0).hom

/-- The differential from integral two-chains, with codomain restricted to
integral one-cycles. -/
noncomputable def oneBoundariesToCycles (X : SSet.{u}) :
    integralTwoChains X →+ integralOneCycles X where
  toFun a := ⟨((X.chainComplex
      (AlgebraicTopology.singularIntegralCoefficients :
        AddCommGrpCat.{u})).d 2 1) a, by
    exact ConcreteCategory.congr_hom
      ((X.chainComplex
        (AlgebraicTopology.singularIntegralCoefficients :
          AddCommGrpCat.{u})).d_comp_d 2 1 0) a⟩
  map_zero' := by ext; simp
  map_add' _ _ := by ext; simp

/-- The concrete cycles-modulo-boundaries model for integral homology in
degree one. -/
noncomputable abbrev integralHomologyOneQuotient (X : SSet.{u}) : Type u :=
  integralOneCycles X ⧸
    AddMonoidHom.range (oneBoundariesToCycles X)

/-- A one-cycle determines a class in the kernel of the descended one-chain
boundary. -/
noncomputable def oneCyclesToOneChainBoundaryKer (X : SSet.{u}) :
    integralOneCycles X →+
      AddMonoidHom.ker (oneChainBoundary X) where
  toFun z := ⟨(z.val : oneChainQuotient X), by
    change oneChainBoundary X
      (QuotientAddGroup.mk' (oneChainBoundaries X) z.val) = 0
    rw [oneChainBoundary_mk]
    exact z.prop⟩
  map_zero' := by ext; rfl
  map_add' _ _ := by ext; rfl

/-- Concrete one-boundaries vanish after passing from cycles to the kernel of
the descended one-chain boundary. -/
theorem oneChainBoundaries_le_ker_oneCyclesToOneChainBoundaryKer
    (X : SSet.{u}) :
    AddMonoidHom.range (oneBoundariesToCycles X) ≤
      AddMonoidHom.ker (oneCyclesToOneChainBoundaryKer X) := by
  rintro z ⟨a, rfl⟩
  rw [AddMonoidHom.mem_ker]
  apply Subtype.ext
  change ((
      ((X.chainComplex
        (AlgebraicTopology.singularIntegralCoefficients :
          AddCommGrpCat.{u})).d 2 1) a : integralOneChains X) :
      oneChainQuotient X) = 0
  rw [QuotientAddGroup.eq_zero_iff]
  exact ⟨a, rfl⟩

/-- Cycles modulo concrete one-boundaries map to the kernel of the descended
one-chain boundary. -/
noncomputable def homologyOneQuotientToOneChainBoundaryKer
    (X : SSet.{u}) :
    integralHomologyOneQuotient X →+
      AddMonoidHom.ker (oneChainBoundary X) :=
  QuotientAddGroup.lift _ (oneCyclesToOneChainBoundaryKer X)
    (oneChainBoundaries_le_ker_oneCyclesToOneChainBoundaryKer X)

@[simp]
theorem homologyOneQuotientToOneChainBoundaryKer_mk
    (X : SSet.{u}) (z : integralOneCycles X) :
    homologyOneQuotientToOneChainBoundaryKer X
        (QuotientAddGroup.mk' _ z) =
      oneCyclesToOneChainBoundaryKer X z :=
  rfl

/-- The concrete cycles-modulo-boundaries model of H1 is additively
equivalent to the kernel of the descended boundary on all one-chains modulo
two-boundaries. -/
noncomputable def homologyOneQuotientAddEquivOneChainBoundaryKer
    (X : SSet.{u}) :
    integralHomologyOneQuotient X ≃+
      AddMonoidHom.ker (oneChainBoundary X) :=
  AddEquiv.ofBijective (homologyOneQuotientToOneChainBoundaryKer X) <| by
    constructor
    · intro q r hqr
      induction q using QuotientAddGroup.induction_on with
      | _ q =>
        induction r using QuotientAddGroup.induction_on with
        | _ r =>
          apply (QuotientAddGroup.eq_iff_sub_mem).2
          have hqr' : oneCyclesToOneChainBoundaryKer X q =
              oneCyclesToOneChainBoundaryKer X r := by
            change homologyOneQuotientToOneChainBoundaryKer X
                (QuotientAddGroup.mk' _ q) =
              homologyOneQuotientToOneChainBoundaryKer X
                (QuotientAddGroup.mk' _ r) at hqr
            rw [homologyOneQuotientToOneChainBoundaryKer_mk,
              homologyOneQuotientToOneChainBoundaryKer_mk] at hqr
            exact hqr
          have hclasses : ((q.val : integralOneChains X) :
                oneChainQuotient X) =
              ((r.val : integralOneChains X) : oneChainQuotient X) :=
            congrArg Subtype.val hqr'
          have hmem : q.val - r.val ∈ oneChainBoundaries X :=
            (QuotientAddGroup.eq_iff_sub_mem).mp hclasses
          obtain ⟨a, ha⟩ := hmem
          refine ⟨a, ?_⟩
          apply Subtype.ext
          exact ha
    · rintro ⟨q, hq⟩
      obtain ⟨c, hc⟩ :=
        QuotientAddGroup.mk'_surjective (oneChainBoundaries X) q
      have hcycle :
          ((X.chainComplex
            (AlgebraicTopology.singularIntegralCoefficients :
              AddCommGrpCat.{u})).d 1 0) c = 0 := by
        have hboundary : oneChainBoundary X q = 0 :=
          AddMonoidHom.mem_ker.mp hq
        have hc' := congrArg (oneChainBoundary X) hc
        rw [oneChainBoundary_mk] at hc'
        exact hc'.trans hboundary
      let z : integralOneCycles X := ⟨c, hcycle⟩
      refine ⟨QuotientAddGroup.mk' _ z, ?_⟩
      apply Subtype.ext
      change ((c : integralOneChains X) : oneChainQuotient X) = q
      exact hc

/-- Endomorphisms in the quotient one-chain groupoid are the kernel of the
descended boundary.  The target is written multiplicatively to match
`CategoryTheory.End`. -/
noncomputable def oneChainGroupoidEndMulEquivBoundaryKer
    (X : SSet.{u}) (x : X _⦋0⦌) :
    End (OneChainGroupoid.mk x) ≃*
      Multiplicative (AddMonoidHom.ker (oneChainBoundary X)) where
  toFun q := Multiplicative.ofAdd ⟨q.asHom.val, by
    apply AddMonoidHom.mem_ker.mpr
    simpa only [sub_self] using q.asHom.prop⟩
  invFun q := End.of ⟨(Multiplicative.toAdd q).val, by
    have h := AddMonoidHom.mem_ker.mp (Multiplicative.toAdd q).prop
    simpa only [sub_self] using h⟩
  left_inv q := by apply End.ext; apply Subtype.ext; rfl
  right_inv q := by
    apply Multiplicative.toAdd.injective
    apply Subtype.ext
    rfl
  map_mul' q r := by
    apply Multiplicative.toAdd.injective
    apply Subtype.ext
    change r.asHom.val + q.asHom.val = q.asHom.val + r.asHom.val
    exact add_comm r.asHom.val q.asHom.val

/-- The based simplicial fundamental group maps to the concrete integral
cycles-modulo-boundaries quotient in degree one. -/
noncomputable def fundamentalGroupConcreteHomologyOneHom
    (X : SSet.{u}) (x : X _⦋0⦌) :
    End (SSet.FundamentalGroupoid.mk x) →*
      Multiplicative (integralHomologyOneQuotient X) :=
  (homologyOneQuotientAddEquivOneChainBoundaryKer X).symm.toMultiplicative.toMonoidHom.comp
    ((oneChainGroupoidEndMulEquivBoundaryKer X x).toMonoidHom.comp
      ((fundamentalGroupoidToOneChainGroupoid X).mapEnd
        (SSet.FundamentalGroupoid.mk x)))

/-- The forward concrete degree-one homology map factors through the
abelianization of the based simplicial fundamental group. -/
noncomputable def fundamentalGroupAbelianizationConcreteHomologyOneHom
    (X : SSet.{u}) (x : X _⦋0⦌) :
    Abelianization (End (SSet.FundamentalGroupoid.mk x)) →*
      Multiplicative (integralHomologyOneQuotient X) :=
  Abelianization.lift (fundamentalGroupConcreteHomologyOneHom X x)

@[simp]
theorem fundamentalGroupAbelianizationConcreteHomologyOneHom_of
    (X : SSet.{u}) (x : X _⦋0⦌)
    (q : End (SSet.FundamentalGroupoid.mk x)) :
    fundamentalGroupAbelianizationConcreteHomologyOneHom X x
        (Abelianization.of q) =
      fundamentalGroupConcreteHomologyOneHom X x q :=
  rfl

end SSet

end
