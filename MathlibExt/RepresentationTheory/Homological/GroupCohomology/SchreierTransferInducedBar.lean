/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
public import Mathlib.CategoryTheory.Preadditive.Projective.Resolution
public import Mathlib.RepresentationTheory.FiniteIndex
public import
MathlibExt.RepresentationTheory.Homological.GroupCohomology.SchreierRestrictionCorestrictionArbitrary

/-!
# The induced bar resolution and universal transfer

For a finite-index subgroup H ≤ G and a commutative ring k, induction sends the H-bar
resolution to a projective resolution of the induced trivial representation ind_H^G(k). The
induction unit applied to each H-bar generator defines a universal cochain uₙ(q) = η(barBasis
n q).

Transferring uₙ by a right transversal T and extending from G-bar generators produces a chain
map B_G → ind_H^G(B_H). Its augmentation is the canonical norm map from the trivial
G-representation to ind_H^G(k), whose value at 1 is ∑ₜ IndV.mk(t,1). Under the induction
adjunction, composing this universal map with the adjoint free lift of a coefficient cochain
gives the free lift of its Schreier transfer.

Universal maps obtained from two transversals lift the same norm and are chain homotopic.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits

namespace Rep

universe u

variable {k G : Type u} [CommRing k] [Group G]
variable (H : Subgroup G) [H.FiniteIndex]

attribute [local instance] Subgroup.fintypeQuotientOfFiniteIndex

/-- Additivity of finite-index induction.

For a finite-index subgroup H ≤ G, induction of k-linear representations preserves sums of
morphisms. -/
noncomputable instance indFunctorFiniteIndexAdditive :
    (indFunctor.{u} k H.subtype).Additive :=
  Functor.additive_of_preserves_binary_products _

/-- Projective objects under finite-index induction.

For a finite-index subgroup H ≤ G, induction sends projective H-representations to projective
G-representations. -/
noncomputable instance indFunctorFiniteIndexPreservesProjectiveObjects :
    (indFunctor.{u} k H.subtype).PreservesProjectiveObjects :=
  Functor.preservesProjectiveObjects_of_adjunction_of_preservesEpimorphisms
    (indResAdjunction.{u} k H.subtype)

end Rep

namespace groupCohomology

universe u

variable {k G : Type u} [CommRing k] [Group G]
variable (H : Subgroup G) [H.FiniteIndex]

attribute [local instance] Subgroup.fintypeQuotientOfFiniteIndex

/-- Finite representatives for the induced-bar construction.

For a finite-index H ≤ G, the representative type of a right transversal T is finitely
enumerated for the induced-bar sums. -/
noncomputable local instance inducedBarRightTransversalFintype
    (T : H.RightTransversal) : Fintype (T : Set G) :=
  @Fintype.ofFinite (T : Set G) (T.2.finite_right)

/-- The projective resolution induced from the subgroup bar.

Apply induction along H → G to the H-bar resolution of the trivial k-representation. For
finite-index H, this gives a projective resolution of ind_H^G(k). -/
noncomputable def inducedBarResolution :
    ProjectiveResolution
      ((Rep.indFunctor.{u} k H.subtype).obj (Rep.trivial k H k)) :=
  (Rep.indFunctor.{u} k H.subtype).mapProjectiveResolution
    (Rep.barResolution k H)

/-- The norm map to the induced trivial representation.

For finite-index H, the unit of the restriction-to-induction adjunction gives a G-equivariant
map from the trivial G-representation k to ind_H^G(k). -/
noncomputable def inducedTrivialNorm :
    Rep.trivial k G k ⟶
      (Rep.indFunctor.{u} k H.subtype).obj (Rep.trivial k H k) := by
  letI : DecidableRel (QuotientGroup.rightRel H) := Classical.decRel _
  exact (Rep.resIndAdjunction.{u} k H).unit.app (Rep.trivial k G k)

section

variable (K : Type u) [Group K]

/-- The degree-zero bar augmentation.

For a group K, the map from its degree-zero bar module to the trivial k-representation is the
standard bar augmentation transported through the bar-to-standard-complex isomorphism. -/
noncomputable def barAugmentationZero :
    (Rep.barComplex k K).X 0 ⟶ Rep.trivial k K k :=
  (Rep.barComplex.isoStandardComplex k K).hom.f 0 ≫
    Rep.standardComplex.ε k K

/-- The augmentation of the empty-tuple bar generator.

The degree-zero bar basis vector indexed by the empty tuple maps to 1 ∈ k under
barAugmentationZero. -/
@[simp]
theorem barAugmentationZero_barBasis :
    (barAugmentationZero (k := k) K).hom
        (barBasis (k := k) 0 Fin.elim0) = (1 : k) := by
  exact barResolution_augmentation_barBasis_zero

end

/-- The induced degree-zero augmentation.

Apply induction along H → G to the degree-zero H-bar augmentation, giving a map from the
induced degree-zero bar module to ind_H^G(k). -/
noncomputable def inducedBarAugmentationZero :
  (Rep.indFunctor.{u} k H.subtype).obj ((Rep.barComplex k H).X 0) ⟶
      (Rep.indFunctor.{u} k H.subtype).obj (Rep.trivial k H k) :=
  (Rep.indFunctor.{u} k H.subtype).map
    (barAugmentationZero (k := k) H)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
/-- The degree-zero component of the induced resolution map.

The degree-zero augmentation of inducedBarResolution H equals the induced H-bar augmentation. -/
theorem inducedBarResolution_π_f_zero :
    (inducedBarResolution (k := k) H).π.f 0 =
      inducedBarAugmentationZero (k := k) H := by
  rfl

omit [H.FiniteIndex] in
/-- Coordinates of an induced representation morphism.

For f : A → B between H-representations, its induced map sends the coinvariant generator
IndV.mk(g,a) to IndV.mk(g,f(a)). -/
theorem indFunctor_map_indV_mk
    {A B : Rep k H} (f : A ⟶ B) (g : G) (a : A) :
    ((Rep.indFunctor.{u} k H.subtype).map f).hom
        (Representation.IndV.mk H.subtype A.ρ g a) =
      Representation.IndV.mk H.subtype B.ρ g (f.hom a) := by
  simp [Rep.indFunctor_map, Rep.indMap, Representation.IndV.mk]

set_option backward.isDefEq.respectTransparency.types false in
/-- The coinduction-to-induction map as a transversal sum.

For a coinduced coefficient function f and right transversal T, its image in ind_H^G(A) is ∑ₜ
IndV.mk(t,f(t)). -/
theorem coindToInd_eq_sum_rightTransversal
    (A : Rep k H) (f : Rep.coind H.subtype A)
    (T : H.RightTransversal) :
    Rep.coindToInd A f =
      ∑ t : (T : Set G),
        Representation.IndV.mk H.subtype A.ρ (t : G) (f.1 (t : G)) := by
  rw [Rep.coindToInd_apply]
  calc
    _ = ∑ q : Quotient (QuotientGroup.rightRel H),
        Representation.IndV.mk H.subtype A.ρ
          (T.2.rightQuotientEquiv q : G)
          (f.1 (T.2.rightQuotientEquiv q : G)) := by
      apply Finset.sum_congr rfl
      intro q _
      conv_lhs => rw [← T.2.mk''_rightQuotientEquiv q]
      rfl
    _ = _ := (T.2.rightQuotientEquiv.sum_comp
      (fun t : (T : Set G) ↦
        Representation.IndV.mk H.subtype A.ρ (t : G) (f.1 (t : G))))

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
/-- The norm of one in induced trivial coordinates.

For any right transversal T, the canonical norm map sends 1 ∈ k to ∑ₜ IndV.mk(t,1) in the
induced trivial representation. -/
theorem inducedTrivialNorm_one_eq_sum
    (T : H.RightTransversal) :
    (inducedTrivialNorm (k := k) H).hom (1 : k) =
      ∑ t : (T : Set G),
        Representation.IndV.mk H.subtype (Rep.trivial k H k).ρ
          (t : G) (1 : k) := by
  classical
  let _ : DecidableRel (QuotientGroup.rightRel H) := Classical.decRel _
  unfold inducedTrivialNorm
  rw [Rep.resIndAdjunction_unit_app]
  change Rep.coindToInd (Rep.trivial k H k)
      (((Rep.resCoindAdjunction k H.subtype).unit.app
        (Rep.trivial k G k)).hom (1 : k)) = _
  have hvalue (g : G) :
      ((((Rep.resCoindAdjunction k H.subtype).unit.app
        (Rep.trivial k G k)).hom (1 : k)).1 g) = 1 := by
    simp [Rep.resCoindAdjunction, Rep.resCoindHomEquiv,
      Rep.resCoindToHom]
  rw [coindToInd_eq_sum_rightTransversal (T := T)]
  simp_rw [hvalue]

/-- The induction unit of a subgroup bar degree.

In degree n, the induction-restriction adjunction gives B_H,ₙ → res_H^G(ind_H^G(B_H,ₙ)). -/
noncomputable def inducedBarUnit (n : ℕ) :
    (Rep.barComplex k H).X n ⟶
      Rep.res H.subtype
        ((Rep.indFunctor.{u} k H.subtype).obj
          ((Rep.barComplex k H).X n)) :=
  (Rep.indResAdjunction.{u} k H.subtype).unit.app
    ((Rep.barComplex k H).X n)

/-- The universal cochain of the induced subgroup bar.

For q : Fin n → H, apply the induction unit to the bar basis vector indexed by q. This cochain
takes values in the induced degree-n H-bar module. -/
noncomputable def inducedBarUnitCochain (n : ℕ) :
    (Fin n → H) →
      (Rep.indFunctor.{u} k H.subtype).obj
        ((Rep.barComplex k H).X n) :=
  fun q ↦ (inducedBarUnit (k := k) H n).hom
    (barBasis (k := k) n q)

omit [H.FiniteIndex] in
/-- Values of the universal induced-bar cochain.

The value at q is the induction-unit image of barBasis n q. -/
@[simp]
theorem inducedBarUnitCochain_apply (n : ℕ) (q : Fin n → H) :
    inducedBarUnitCochain (k := k) H n q =
      (inducedBarUnit (k := k) H n).hom (barBasis (k := k) n q) :=
  rfl

omit [H.FiniteIndex] in
/-- The universal induced-bar cochain in coinvariant coordinates.

At a tuple q, the universal cochain is IndV.mk(1,barBasis n q). -/
theorem inducedBarUnitCochain_eq_indV_mk
    (n : ℕ) (q : Fin n → H) :
    inducedBarUnitCochain (k := k) H n q =
      Representation.IndV.mk H.subtype
        ((Rep.barComplex k H).X n).ρ 1 (barBasis (k := k) n q) := by
  rfl

omit [H.FiniteIndex] in
/-- Evaluation through the induction adjunction.

For φ : ind_H^G(B_H,ₙ) → A, applying φ to the universal cochain at q equals applying its
adjoint H-map to barBasis n q. -/
theorem hom_inducedBarUnitCochain
    (A : Rep k G) (n : ℕ)
    (phi : (Rep.indFunctor.{u} k H.subtype).obj
      ((Rep.barComplex k H).X n) ⟶ A)
    (q : Fin n → H) :
    phi.hom (inducedBarUnitCochain (k := k) H n q) =
      ((Rep.indResHomEquiv H.subtype
        ((Rep.barComplex k H).X n) A) phi).hom
          (barBasis (k := k) n q) := by
  rfl

omit [H.FiniteIndex] in
/-- The adjoint free lift evaluates to the prescribed cochain.

For z : Hⁿ → A, the G-map adjoint to its H-bar free lift sends the universal induced-bar
cochain at q to z(q). -/
theorem indResHomEquiv_symm_freeLift_inducedBarUnitCochain
    (A : Rep k G) (n : ℕ) (z : (Fin n → H) → A)
    (q : Fin n → H) :
    let zHom : (Rep.barComplex k H).X n ⟶
        Rep.res H.subtype A :=
      Rep.freeLift k H (Rep.res H.subtype A) z
    let phi : (Rep.indFunctor.{u} k H.subtype).obj
        ((Rep.barComplex k H).X n) ⟶ A :=
      (Rep.indResHomEquiv H.subtype
        ((Rep.barComplex k H).X n) A).symm zHom
    phi.hom (inducedBarUnitCochain (k := k) H n q) = z q := by
  dsimp only
  rw [hom_inducedBarUnitCochain]
  rw [LinearEquiv.apply_symm_apply]
  exact freeLift_barBasis (Rep.res H.subtype A) n z q

omit [H.FiniteIndex] in
/-- The free lift of the universal induced-bar cochain.

Extending the universal cochain from H-bar basis vectors by the free-lift construction
recovers the induction-unit morphism in degree n. -/
theorem freeLift_inducedBarUnitCochain (n : ℕ) :
    Rep.freeLift k H
        (Rep.res H.subtype
          ((Rep.indFunctor.{u} k H.subtype).obj
            ((Rep.barComplex k H).X n)))
        (inducedBarUnitCochain (k := k) H n) =
      inducedBarUnit (k := k) H n := by
  apply Rep.free_ext k H _
  intro q
  change (Rep.freeLift k H
      (Rep.res H.subtype
        ((Rep.indFunctor.{u} k H.subtype).obj
          ((Rep.barComplex k H).X n)))
      (inducedBarUnitCochain (k := k) H n)).hom
        (barBasis (k := k) n q) =
    (inducedBarUnit (k := k) H n).hom (barBasis (k := k) n q)
  rw [freeLift_barBasis]
  rfl

omit [H.FiniteIndex] in
/-- The differential identity of the universal induced-bar cochain.

The inhomogeneous differential of the degree-n universal cochain equals the induced H-bar
differential applied to the degree-(n+1) universal cochain, with the native bar differential
signs. -/
theorem inhomogeneous_d_inducedBarUnitCochain (n : ℕ) :
    (inhomogeneousCochains.d
      (Rep.res H.subtype
        ((Rep.indFunctor.{u} k H.subtype).obj
          ((Rep.barComplex k H).X n))) n).hom
        (inducedBarUnitCochain (k := k) H n) =
      fun q ↦
        ((Rep.indFunctor.{u} k H.subtype).map
          ((Rep.barComplex k H).d (n + 1) n)).hom
            (inducedBarUnitCochain (k := k) H (n + 1) q) := by
  let dH := (Rep.barComplex k H).d (n + 1) n
  let phi := (Rep.indFunctor.{u} k H.subtype).map dH
  have hnat := (Rep.indResAdjunction.{u} k H.subtype).unit.naturality dH
  have hbar := barComplex_d_comp_freeLift
    (Rep.res H.subtype
      ((Rep.indFunctor.{u} k H.subtype).obj
        ((Rep.barComplex k H).X n))) n
    (inducedBarUnitCochain (k := k) H n)
  have hmor : inducedBarUnit (k := k) H (n + 1) ≫
        (Rep.resFunctor H.subtype).map phi =
      Rep.freeLift k H
        (Rep.res H.subtype
          ((Rep.indFunctor.{u} k H.subtype).obj
            ((Rep.barComplex k H).X n)))
        ((inhomogeneousCochains.d
          (Rep.res H.subtype
            ((Rep.indFunctor.{u} k H.subtype).obj
              ((Rep.barComplex k H).X n))) n).hom
          (inducedBarUnitCochain (k := k) H n)) := by
    calc
      inducedBarUnit (k := k) H (n + 1) ≫
          (Rep.resFunctor H.subtype).map phi =
        dH ≫ inducedBarUnit (k := k) H n := hnat
      _ = dH ≫ Rep.freeLift k H
          (Rep.res H.subtype
            ((Rep.indFunctor.{u} k H.subtype).obj
              ((Rep.barComplex k H).X n)))
          (inducedBarUnitCochain (k := k) H n) := by
        rw [freeLift_inducedBarUnitCochain]
      _ = _ := hbar
  funext q
  have hq := congrArg (fun f ↦ f.hom (barBasis (k := k) (n + 1) q)) hmor
  change
    (inhomogeneousCochains.d
      (Rep.res H.subtype
        ((Rep.indFunctor.{u} k H.subtype).obj
          ((Rep.barComplex k H).X n))) n).hom
        (inducedBarUnitCochain (k := k) H n) q =
      phi.hom (inducedBarUnitCochain (k := k) H (n + 1) q)
  calc
    _ = (Rep.freeLift k H
          (Rep.res H.subtype
            ((Rep.indFunctor.{u} k H.subtype).obj
              ((Rep.barComplex k H).X n)))
          ((inhomogeneousCochains.d
            (Rep.res H.subtype
              ((Rep.indFunctor.{u} k H.subtype).obj
                ((Rep.barComplex k H).X n))) n).hom
            (inducedBarUnitCochain (k := k) H n))).hom
          (barBasis (k := k) (n + 1) q) := by
        rw [freeLift_barBasis]
    _ = ((Rep.resFunctor H.subtype).map phi).hom
          (inducedBarUnitCochain (k := k) H (n + 1) q) := by
        exact hq.symm
    _ = _ := rfl

/-- The universal transfer component into an induced bar degree.

In degree n, transfer the universal induced-bar cochain using T and extend from G-bar basis
vectors. This gives a G-equivariant map B_G,ₙ → ind_H^G(B_H,ₙ). -/
noncomputable def schreierTransferInducedBarComponent
    (T : H.RightTransversal) (n : ℕ) :
    (Rep.barComplex k G).X n ⟶
      (Rep.indFunctor.{u} k H.subtype).obj
        ((Rep.barComplex k H).X n) :=
  Rep.freeLift k G _
    (corestrictionCochain
      ((Rep.indFunctor.{u} k H.subtype).obj
        ((Rep.barComplex k H).X n)) T n
      (inducedBarUnitCochain (k := k) H n))

/-- The induced-bar transfer on a bar generator.

On barBasis n g, the universal transfer component is the degree-n Schreier transfer of the
universal induced-bar cochain at g. -/
theorem schreierTransferInducedBarComponent_barBasis
    (T : H.RightTransversal) (n : ℕ)
    (g : Fin n → G) :
    (schreierTransferInducedBarComponent (k := k) H T n).hom
        (barBasis (k := k) n g) =
      corestrictionCochain
        ((Rep.indFunctor.{u} k H.subtype).obj
          ((Rep.barComplex k H).X n)) T n
        (inducedBarUnitCochain (k := k) H n) g := by
  unfold schreierTransferInducedBarComponent
  exact freeLift_barBasis _ n _ g

/-- Universal transfer followed by an adjoint coefficient map.

For z : Hⁿ → A, precomposing its adjoint H-bar free lift with the universal transfer component
gives the G-bar free lift of cor_Tⁿ(z). -/
theorem schreierTransferInducedBarComponent_comp_adjointFreeLift
    (A : Rep k G) (T : H.RightTransversal)
    (n : ℕ) (z : (Fin n → H) → A) :
    let zHom : (Rep.barComplex k H).X n ⟶
        Rep.res H.subtype A :=
      Rep.freeLift k H (Rep.res H.subtype A) z
    let phi : (Rep.indFunctor.{u} k H.subtype).obj
        ((Rep.barComplex k H).X n) ⟶ A :=
      (Rep.indResHomEquiv H.subtype
        ((Rep.barComplex k H).X n) A).symm zHom
    schreierTransferInducedBarComponent (k := k) H T n ≫ phi =
      Rep.freeLift k G A (corestrictionCochain A T n z) := by
  dsimp only
  apply Rep.free_ext k G A
  intro g
  change ((Rep.indResHomEquiv H.subtype
      ((Rep.barComplex k H).X n) A).symm
        (Rep.freeLift k H (Rep.res H.subtype A) z)).hom
      ((schreierTransferInducedBarComponent (k := k) H T n).hom
        (barBasis (k := k) n g)) =
    (Rep.freeLift k G A (corestrictionCochain A T n z)).hom
      (barBasis (k := k) n g)
  rw [schreierTransferInducedBarComponent_barBasis,
    freeLift_barBasis]
  have h := congrFun
    (corestrictionCochain_naturality
      ((Rep.indResHomEquiv H.subtype
        ((Rep.barComplex k H).X n) A).symm
          (Rep.freeLift k H (Rep.res H.subtype A) z))
      T n (inducedBarUnitCochain (k := k) H n)) g
  have hunit :
      (fun q : Fin n → H ↦
        ((Rep.indResHomEquiv H.subtype
          ((Rep.barComplex k H).X n) A).symm
            (Rep.freeLift k H (Rep.res H.subtype A) z)).hom
          (inducedBarUnitCochain (k := k) H n q)) = z := by
    funext q
    exact indResHomEquiv_symm_freeLift_inducedBarUnitCochain
      (k := k) H A n z q
  rw [hunit] at h
  exact h

/-- The chain equation of the universal transfer components.

The degree-(n+1) transfer followed by the induced H-bar differential equals the G-bar
differential followed by the degree-n transfer. -/
theorem schreierTransferInducedBarComponent_comm
    (T : H.RightTransversal) (n : ℕ) :
    schreierTransferInducedBarComponent (k := k) H T (n + 1) ≫
        (Rep.indFunctor.{u} k H.subtype).map
          ((Rep.barComplex k H).d (n + 1) n) =
      (Rep.barComplex k G).d (n + 1) n ≫
        schreierTransferInducedBarComponent (k := k) H T n := by
  let PHn := (Rep.barComplex k H).X n
  let A : Rep k G := (Rep.indFunctor.{u} k H.subtype).obj PHn
  let U := inducedBarUnitCochain (k := k) H n
  let C := corestrictionCochain A T n U
  let dH := (Rep.barComplex k H).d (n + 1) n
  let phi := (Rep.indFunctor.{u} k H.subtype).map dH
  have hunit :
      (inhomogeneousCochains.d (Rep.res H.subtype A) n).hom U =
        fun q ↦ phi.hom
          (inducedBarUnitCochain (k := k) H (n + 1) q) := by
    exact inhomogeneous_d_inducedBarUnitCochain (k := k) H n
  have hleft :
      (fun g ↦ phi.hom
        (corestrictionCochain
          ((Rep.indFunctor.{u} k H.subtype).obj
            ((Rep.barComplex k H).X (n + 1))) T (n + 1)
          (inducedBarUnitCochain (k := k) H (n + 1)) g)) =
        (inhomogeneousCochains.d A n).hom C := by
    calc
      _ = corestrictionCochain A T (n + 1)
          (fun q ↦ phi.hom
            (inducedBarUnitCochain (k := k) H (n + 1) q)) :=
        corestrictionCochain_naturality phi T (n + 1)
          (inducedBarUnitCochain (k := k) H (n + 1))
      _ = corestrictionCochain A T (n + 1)
          ((inhomogeneousCochains.d (Rep.res H.subtype A) n).hom U) := by
        rw [hunit]
      _ = (inhomogeneousCochains.d A n).hom C :=
        corestrictionCochain_d A T n U
  apply Rep.free_ext k G A
  intro g
  change phi.hom
      ((schreierTransferInducedBarComponent (k := k) H T (n + 1)).hom
        (barBasis (k := k) (n + 1) g)) =
    (schreierTransferInducedBarComponent (k := k) H T n).hom
      (((Rep.barComplex k G).d (n + 1) n).hom
        (barBasis (k := k) (n + 1) g))
  rw [schreierTransferInducedBarComponent_barBasis]
  have hg := congrFun hleft g
  rw [hg]
  have hbar := barComplex_d_comp_freeLift A n C
  have hbasis := congrArg
    (fun f ↦ f.hom (barBasis (k := k) (n + 1) g)) hbar
  calc
    (inhomogeneousCochains.d A n).hom C g =
        (Rep.freeLift k G A
          ((inhomogeneousCochains.d A n).hom C)).hom
          (barBasis (k := k) (n + 1) g) :=
      (freeLift_barBasis A (n + 1)
        ((inhomogeneousCochains.d A n).hom C) g).symm
    _ = ((Rep.barComplex k G).d (n + 1) n ≫
          Rep.freeLift k G A C).hom
          (barBasis (k := k) (n + 1) g) := hbasis.symm
    _ = (schreierTransferInducedBarComponent (k := k) H T n).hom
        (((Rep.barComplex k G).d (n + 1) n).hom
          (barBasis (k := k) (n + 1) g)) := rfl

/-- The universal Schreier transfer of bar complexes.

The degreewise universal components assemble into a chain map from the G-bar complex to the
induced H-bar complex. -/
noncomputable def schreierTransferInducedBarChain
    (T : H.RightTransversal) :
    Rep.barComplex k G ⟶
      ((Rep.indFunctor.{u} k H.subtype).mapHomologicalComplex
        (ComplexShape.down ℕ)).obj (Rep.barComplex k H) where
  f n := schreierTransferInducedBarComponent (k := k) H T n
  comm' i j hij := by
    rcases hij with ⟨rfl⟩
    exact schreierTransferInducedBarComponent_comm H T j

/-- Components of the universal bar-complex chain map.

The component in degree n of schreierTransferInducedBarChain H T is
schreierTransferInducedBarComponent H T n. -/
@[simp]
theorem schreierTransferInducedBarChain_f
    (T : H.RightTransversal) (n : ℕ) :
    (schreierTransferInducedBarChain (k := k) H T).f n =
      schreierTransferInducedBarComponent (k := k) H T n :=
  rfl

/-- The universal Schreier map between projective resolutions.

The chosen-transversal bar-complex map gives a chain map from the G-bar resolution to the
projective resolution induced from the H-bar. -/
noncomputable def schreierTransferInducedBar
    (T : H.RightTransversal) :
    (Rep.barResolution k G).complex ⟶
      (inducedBarResolution (k := k) H).complex := by
  rw [Rep.barResolution_complex]
  change Rep.barComplex k G ⟶
    ((Rep.indFunctor.{u} k H.subtype).mapHomologicalComplex
      (ComplexShape.down ℕ)).obj (Rep.barResolution k H).complex
  rw [Rep.barResolution_complex]
  exact schreierTransferInducedBarChain (k := k) H T

set_option backward.isDefEq.respectTransparency false in
/-- The augmented universal transfer on the degree-zero generator.

The degree-zero universal transfer, followed by induced augmentation, sends the empty-tuple
G-bar basis vector to the induced trivial norm of 1. -/
theorem schreierTransferInducedBarComponent_zero_augmentation
    (T : H.RightTransversal) :
    (inducedBarAugmentationZero (k := k) H).hom
        ((schreierTransferInducedBarComponent (k := k) H T 0).hom
          (barBasis (k := k) 0 Fin.elim0)) =
      (inducedTrivialNorm (k := k) H).hom (1 : k) := by
  rw [schreierTransferInducedBarComponent_barBasis,
    corestrictionCochain_apply, map_sum]
  have hterm (t : (T : Set G)) :
      (inducedBarAugmentationZero (k := k) H).hom
          (((Rep.indFunctor.{u} k H.subtype).obj
            ((Rep.barComplex k H).X 0)).ρ (t : G)⁻¹
            (inducedBarUnitCochain (k := k) H 0
              (T.schreierFactorTuple t Fin.elim0))) =
        Representation.IndV.mk H.subtype (Rep.trivial k H k).ρ
          (t : G) (1 : k) := by
    have hempty : T.schreierFactorTuple t Fin.elim0 =
        (Fin.elim0 : Fin 0 → H) := Subsingleton.elim _ _
    rw [hempty, Rep.hom_comm_apply,
      inducedBarUnitCochain_eq_indV_mk]
    change ((Rep.indFunctor.{u} k H.subtype).obj
        (Rep.trivial k H k)).ρ (t : G)⁻¹
      ((inducedBarAugmentationZero (k := k) H).hom
          (Representation.IndV.mk H.subtype
            ((Rep.barComplex k H).X 0).ρ 1
            (barBasis (k := k) 0 Fin.elim0))) = _
    unfold inducedBarAugmentationZero
    rw [indFunctor_map_indV_mk]
    change (Representation.ind H.subtype (Rep.trivial k H k).ρ)
        ((t : G)⁻¹)
        (Representation.IndV.mk H.subtype (Rep.trivial k H k).ρ 1
          ((barAugmentationZero (k := k) H).hom
            (barBasis (k := k) 0 Fin.elim0))) = _
    rw [Representation.ind_mk]
    rw [barAugmentationZero_barBasis]
    simp
  simp_rw [hterm]
  exact (inducedTrivialNorm_one_eq_sum (k := k) H T).symm

/-- The degree-zero universal transfer lifts the norm map.

The transfer component followed by induced H-bar augmentation equals the G-bar augmentation
followed by the induced trivial norm. -/
theorem schreierTransferInducedBarComponent_zero_comp_augmentation
    (T : H.RightTransversal) :
    schreierTransferInducedBarComponent (k := k) H T 0 ≫
        inducedBarAugmentationZero (k := k) H =
      barAugmentationZero (k := k) G ≫
        inducedTrivialNorm (k := k) H := by
  apply Rep.free_ext k G _
  intro g
  have hg : g = (Fin.elim0 : Fin 0 → G) := Subsingleton.elim _ _
  subst g
  change (inducedBarAugmentationZero (k := k) H).hom
      ((schreierTransferInducedBarComponent (k := k) H T 0).hom
        (barBasis (k := k) 0 Fin.elim0)) =
    (inducedTrivialNorm (k := k) H).hom
      ((barAugmentationZero (k := k) G).hom
        (barBasis (k := k) 0 Fin.elim0))
  rw [schreierTransferInducedBarComponent_zero_augmentation,
    barAugmentationZero_barBasis]

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
/-- The resolution square for the universal norm lift.

The universal transfer followed by the induced resolution augmentation equals the G-resolution
augmentation followed by the chain map on single-degree complexes induced by the norm. -/
theorem schreierTransferInducedBar_comp_π
    (T : H.RightTransversal) :
    schreierTransferInducedBar (k := k) H T ≫
        (inducedBarResolution (k := k) H).π =
      (Rep.barResolution k G).π ≫
        (ChainComplex.single₀ (Rep k G)).map
          (inducedTrivialNorm (k := k) H) := by
  apply HomologicalComplex.Hom.ext
  funext n
  cases n with
  | zero =>
      change schreierTransferInducedBarComponent (k := k) H T 0 ≫
          inducedBarAugmentationZero (k := k) H =
        barAugmentationZero (k := k) G ≫
          inducedTrivialNorm (k := k) H
      exact schreierTransferInducedBarComponent_zero_comp_augmentation H T
  | succ n => simp

/-- A homotopy between universal transfers from different transversals.

For T and U, their universal resolution maps lift the same induced trivial norm. Projective-
resolution lift uniqueness supplies a chain homotopy between the maps. -/
noncomputable def schreierTransferInducedBarHomotopy
    (T U : H.RightTransversal) :
    Homotopy
      (schreierTransferInducedBar (k := k) H T)
      (schreierTransferInducedBar (k := k) H U) :=
  ProjectiveResolution.liftHomotopy
    (inducedTrivialNorm (k := k) H)
    (schreierTransferInducedBar (k := k) H T)
    (schreierTransferInducedBar (k := k) H U)
    (schreierTransferInducedBar_comp_π H T)
    (schreierTransferInducedBar_comp_π H U)

end groupCohomology
