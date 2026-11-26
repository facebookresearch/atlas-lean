/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.Algebra.Homology.LinearHomCochainHomotopyEquiv
public import MathlibExt.RepresentationTheory.Homological.GroupCohomology.SchreierTransferArbitraryIndependence
public import MathlibExt.RepresentationTheory.Homological.GroupCohomology.SchreierTransferNorm
public import MathlibExt.RepresentationTheory.Homological.GroupCohomology.ShapiroCorestriction
public import MathlibExt.RepresentationTheory.Rep.CyclicPermutationCoinduced

/-!
# Shapiro comparison, restriction, and corestriction

Let `G` be a group and `k` a commutative ring. The bar complexes for a subgroup `H ≤ G` and
for `G` have a natural inclusion `B_H → Res_H B_G`. If `H` has finite index, a right
transversal gives an adjoint Schreier comparison and a homotopy equivalence of these
resolutions. Applying coefficient Hom and the restriction–coinduction adjunction gives `S_T^n
: H^n(G,Coind_H^G B) ≅ H^n(H,B)` for `B : Rep k H`.

For `A : Rep k G`, let `η_A : A → Coind(Res A)` be the restriction–coinduction unit and let
`ε_A : Coind(Res A) → A` be the finite-index counit. They satisfy `η_* ≫ S_T.hom = res_H^G`
and `S_T.inv ≫ ε_* = cor_H^G` in every degree. The counit has value `ε_A(f)=∑ t∈T,
ρ_A(t⁻¹)f(t)` for any right transversal.

For a surjective character `χ : G → Multiplicative (ZMod ℓ)` with `ℓ ≠ 0`, put
`c(g)=Multiplicative.toAdd (χ g)`. The cyclic coefficient representation consists of functions
`p : ZMod ℓ → A` with action `(g·p)(i)=ρ_A(g)p(i+c(g))`. Its comparison with coinduction is `p
↦ (g ↦ ρ_A(g)p(c(g)))`. The diagonal `a ↦ (i ↦ a)` corresponds to restriction, and the
augmentation `p ↦ ∑ i, p(i)` corresponds to corestriction from `ker χ`.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section

open CategoryTheory

namespace groupCohomology

universe u

variable {k G : Type u} [CommRing k] [Group G]
variable (H : Subgroup G) [H.FiniteIndex]

/-- For a group `G` and a subgroup `H ≤ G`, the relation of belonging to the same right `H`-coset
is classically decidable. This local instance gives `DecidableRel (QuotientGroup.rightRel H)`
on `G`. -/
noncomputable local instance shapiroComparisonDecidableRightRel :
    DecidableRel (QuotientGroup.rightRel H) :=
  Classical.decRel _

/-- For a group `G`, a finite-index subgroup `H ≤ G`, and a right transversal `T`, the subtype `(T
: Set G)` of representatives has a finite enumeration. This local `Fintype` structure gives
the index set of the finite coinduction counit sum. -/
noncomputable local instance shapiroComparisonRightTransversalFintype
    (T : H.RightTransversal) : Fintype (T : Set G) :=
  @Fintype.ofFinite (T : Set G) (T.2.finite_right)

/-- Let `G` be a group, `k` a commutative ring, `H ≤ G` finite index, `A : Rep k G`, and `T` a
right transversal. For `f ∈ Coind_H^G(Res_H A)`, `(corestrictionCounit H A)(f) = ∑ t∈T,
A.ρ(t⁻¹)(f.1(t))`. Here `f.1 : G → A` is the coinduced function, and the sum is over the
finite representative subtype of `T`. -/
theorem corestrictionCounit_apply_eq_sum
    (A : Rep k G) (T : H.RightTransversal)
    (f : Rep.coind H.subtype (Rep.res H.subtype A)) :
    (corestrictionCounit H A).hom f =
      ∑ t : (T : Set G), A.ρ (t : G)⁻¹ (f.1 (t : G)) := by
  classical
  let _ : DecidableRel (QuotientGroup.rightRel H) := Classical.decRel _
  unfold corestrictionCounit
  rw [Rep.coindResAdjunction_counit_app]
  change ((Rep.indResAdjunction k H.subtype).counit.app A).hom
      (Rep.coindToInd (Rep.res H.subtype A) f) = _
  rw [coindToInd_eq_sum_rightTransversal (k := k) H
    (Rep.res H.subtype A) f T, map_sum]
  apply Finset.sum_congr rfl
  intro t _ht
  simp [Rep.indResAdjunction, Rep.indResHomEquiv]

/-- Let `G` be a group, `k` a commutative ring, `H ≤ G` finite index, `X,A : Rep k G`, and `Y :
Rep k H`. Given `r : Res X → Y` and `z : Y → Res A`, write `α=Rep.resCoindHomEquiv H.subtype X
(Res A)`, `β=(Rep.resIndAdjunction k H).homEquiv X Y`, and `γ=(Rep.indResHomEquiv H.subtype Y
A).symm`. Then `α(r ≫ z) ≫ corestrictionCounit H A = β(r) ≫ γ(z)` as morphisms `X → A`; the
right-hand composite factors through `Ind_H^G Y`. -/
theorem resCoindHomEquiv_comp_corestrictionCounit
    {X : Rep.{u} k G} {Y : Rep.{u} k H} (A : Rep.{u} k G)
    (r : Rep.res H.subtype X ⟶ Y)
    (z : Y ⟶ Rep.res H.subtype A) :
    Rep.resCoindHomEquiv H.subtype X (Rep.res H.subtype A) (r ≫ z) ≫
        corestrictionCounit H A =
      (Rep.resIndAdjunction k H).homEquiv X Y r ≫
        (Rep.indResHomEquiv H.subtype Y A).symm z := by
  let _ : DecidableRel (QuotientGroup.rightRel H) := Classical.decRel _
  let adjR := Rep.resCoindAdjunction k H.subtype
  let adjL := Rep.coindResAdjunction k H
  have hAdj :
      (Rep.coindFunctor k H.subtype).map z ≫ adjL.counit.app A =
        (adjL.homEquiv Y A).symm z := by
    symm
    simpa only [Category.comp_id, adjL.homEquiv_symm_id] using
      adjL.homEquiv_naturality_left_symm z
        (𝟙 (Rep.res H.subtype A))
  change adjR.homEquiv X (Rep.res H.subtype A) (r ≫ z) ≫
      adjL.counit.app A = _
  calc
    adjR.homEquiv X (Rep.res H.subtype A) (r ≫ z) ≫
          adjL.counit.app A =
        (adjR.homEquiv X Y r ≫
            (Rep.coindFunctor k H.subtype).map z) ≫
          adjL.counit.app A := by
      rw [adjR.homEquiv_naturality_right]
    _ = adjR.homEquiv X Y r ≫
          (adjL.homEquiv Y A).symm z := by
      rw [Category.assoc, hAdj]
    _ = adjR.homEquiv X Y r ≫
          (Rep.indCoindIso Y).inv ≫
            (Rep.indResHomEquiv H.subtype Y A).symm z := by
      rw [Rep.coindResAdjunction_homEquiv_symm_apply]
    _ = (Rep.resIndAdjunction k H).homEquiv X Y r ≫
          (Rep.indResHomEquiv H.subtype Y A).symm z := by
      rw [Rep.resIndAdjunction_homEquiv_apply]
      simp only [Category.assoc]
      rfl

omit [H.FiniteIndex] in
/-- Let `G` be a group, `k` a commutative ring, `H ≤ G`, `X,A : Rep k G`, and `f : X → A`. For the
restriction–coinduction unit `η_A=(Rep.resCoindAdjunction k H.subtype).unit.app A`,
`(Rep.resCoindHomEquiv H.subtype X (Res A)).symm (f ≫ η_A) = (Rep.resFunctor H.subtype).map
f`. -/
theorem resCoindHomEquiv_symm_comp_unit
    {X A : Rep.{u} k G} (f : X ⟶ A) :
    (Rep.resCoindHomEquiv H.subtype X (Rep.res H.subtype A)).symm
        (f ≫ (Rep.resCoindAdjunction k H.subtype).unit.app A) =
      (Rep.resFunctor H.subtype).map f := by
  let adj := Rep.resCoindAdjunction k H.subtype
  apply (Rep.resCoindHomEquiv H.subtype X
    (Rep.res H.subtype A)).injective
  rw [LinearEquiv.apply_symm_apply]
  change f ≫ adj.unit.app A =
    adj.unit.app X ≫
      (Rep.coindFunctor k H.subtype).map
        ((Rep.resFunctor H.subtype).map f)
  exact adj.unit.naturality f

/-- Let `G` be a group, `k` a commutative ring, `H ≤ G`, and `n : ℕ`. The equivariant morphism
`barRestrictionComponent H n : (Rep.barComplex k H).X n → Res_H((Rep.barComplex k G).X n)`
sends the unit-coefficient bar basis at `q : Fin n → H` to the ambient bar basis at `fun i =>
(q i : G)`. It is the free equivariant extension of this basis formula. -/
noncomputable def barRestrictionComponent (n : ℕ) :
    (Rep.barComplex k H).X n ⟶
      Rep.res H.subtype ((Rep.barComplex k G).X n) :=
  Rep.freeLift k H _
    (restrictedBarBasisCochain (k := k) (G := G) (H := H) n)

omit [H.FiniteIndex] in
@[simp]
theorem barRestrictionComponent_barBasis
    (n : ℕ) (q : Fin n → H) :
    (barRestrictionComponent (k := k) H n).hom
        (barBasis (k := k) n q) =
      restrictedBarBasisCochain
        (k := k) (G := G) (H := H) n q :=
  freeLift_barBasis _ _ _ _

omit [H.FiniteIndex] in
/-- Let `G` be a group, `k` a commutative ring, `H ≤ G`, and `n : ℕ`. Write
`ι_j=barRestrictionComponent H j` and `B_H,B_G` for the two bar complexes. Then `ι_{n+1} ≫
Res_H(B_G.d (n+1) n) = B_H.d (n+1) n ≫ ι_n`, as maps from `B_H.X (n+1)` to `Res_H(B_G.X n)`. -/
theorem barRestrictionComponent_comm (n : ℕ) :
    barRestrictionComponent (k := k) H (n + 1) ≫
        (Rep.resFunctor H.subtype).map
          ((Rep.barComplex k G).d (n + 1) n) =
      (Rep.barComplex k H).d (n + 1) n ≫
        barRestrictionComponent (k := k) H n := by
  apply Rep.free_ext k H _
  intro q
  change ((Rep.resFunctor H.subtype).map
      ((Rep.barComplex k G).d (n + 1) n)).hom
        ((barRestrictionComponent (k := k) H (n + 1)).hom
          (barBasis (k := k) (n + 1) q)) =
    (barRestrictionComponent (k := k) H n).hom
      (((Rep.barComplex k H).d (n + 1) n).hom
        (barBasis (k := k) (n + 1) q))
  rw [barRestrictionComponent_barBasis]
  have hG := congrArg
    (fun f : (Rep.barComplex k G).X (n + 1) ⟶
        (Rep.barComplex k G).X n =>
      f.hom (barBasis (k := k) (n + 1)
        (fun i => (q i : G))))
    (freeLift_barDifferentialCochain (k := k) (G := G) n)
  have hH := congrArg
    (fun f : (Rep.barComplex k H).X (n + 1) ⟶
        Rep.res H.subtype ((Rep.barComplex k G).X n) =>
      f.hom (barBasis (k := k) (n + 1) q))
    (barComplex_d_comp_freeLift
      (Rep.res H.subtype ((Rep.barComplex k G).X n)) n
      (restrictedBarBasisCochain
        (k := k) (G := G) (H := H) n))
  rw [freeLift_barBasis] at hG hH
  rw [inhomogeneous_d_restrictedBarBasisCochain] at hH
  exact hG.symm.trans hH.symm

/-- Let `G` be a group, `k` a commutative ring, and `H ≤ G`. The chain map `barRestrictionChain H
: B_H → Res_H B_G` has component `barRestrictionComponent H n` in every degree `n : ℕ`. On
unit-coefficient basis tuples it applies the inclusion `H → G` to each coordinate. -/
noncomputable def barRestrictionChain :
    Rep.barComplex k H ⟶
      ((Rep.resFunctor H.subtype).mapHomologicalComplex
        (ComplexShape.down ℕ)).obj (Rep.barComplex k G) where
  f n := barRestrictionComponent (k := k) H n
  comm' i j hij := by
    rcases hij with ⟨rfl⟩
    exact barRestrictionComponent_comm (k := k) H j

/-- Let `G` be a group, `k` a commutative ring, and `H ≤ G`. Write `P_G=Rep.barResolution k G`,
`P_H=Rep.barResolution k H`, and `R_H(P_G)=(Rep.resFunctor H.subtype).mapProjectiveResolution
P_G`. The chain map `barRestriction H : P_H.complex → R_H(P_G).complex` has the subgroup bar
inclusions `barRestrictionComponent H n` as its degree-`n` components. -/
noncomputable def barRestriction :
    (Rep.barResolution k H).complex ⟶
      ((Rep.resFunctor H.subtype).mapProjectiveResolution
        (Rep.barResolution k G)).complex := by
  rw [Rep.barResolution_complex]
  change Rep.barComplex k H ⟶
    ((Rep.resFunctor H.subtype).mapHomologicalComplex
      (ComplexShape.down ℕ)).obj (Rep.barResolution k G).complex
  rw [Rep.barResolution_complex]
  exact barRestrictionChain (k := k) H

set_option backward.isDefEq.respectTransparency false in
omit [H.FiniteIndex] in
/-- Let `G` be a group, `k` a commutative ring, and `H ≤ G`. For the degree-zero bar inclusion
`ι₀=barRestrictionComponent H 0`, `ι₀ ≫ Res_H(barAugmentationZero G) = barAugmentationZero H`.
The augmentations send unit-coefficient degree-zero basis elements to `1 : k`. -/
theorem barRestrictionComponent_zero_comp_augmentation :
    barRestrictionComponent (k := k) H 0 ≫
        (Rep.resFunctor H.subtype).map
          (barAugmentationZero (k := k) G) =
      barAugmentationZero (k := k) H := by
  apply Rep.free_ext k H _
  intro q
  have hq : q = (Fin.elim0 : Fin 0 → H) := Subsingleton.elim _ _
  subst q
  change (barAugmentationZero (k := k) G).hom
      ((barRestrictionComponent (k := k) H 0).hom
        (barBasis (k := k) 0 Fin.elim0)) =
    (barAugmentationZero (k := k) H).hom
      (barBasis (k := k) 0 Fin.elim0)
  rw [barRestrictionComponent_barBasis]
  have hbasis :
      restrictedBarBasisCochain
          (k := k) (G := G) (H := H) 0 Fin.elim0 =
        barBasis (k := k) 0 Fin.elim0 := by
    unfold restrictedBarBasisCochain
    congr 2
    funext i
    exact Fin.elim0 i
  rw [hbasis]
  rw [barAugmentationZero_barBasis, barAugmentationZero_barBasis]

set_option backward.isDefEq.respectTransparency false in
omit [H.FiniteIndex] in
/-- Let `G` be a group, `k` a commutative ring, and `H ≤ G`. Put `P_H=Rep.barResolution k H` and
`R_H(P_G)=(Rep.resFunctor H.subtype).mapProjectiveResolution (Rep.barResolution k G)`. The
chain map `barRestriction H` satisfies `barRestriction H ≫ R_H(P_G).π = P_H.π`, as maps to the
degree-zero complex of the trivial `H`-representation. -/
theorem barRestriction_comp_π :
    barRestriction (k := k) H ≫
        ((Rep.resFunctor H.subtype).mapProjectiveResolution
          (Rep.barResolution k G)).π =
      (Rep.barResolution k H).π := by
  apply HomologicalComplex.Hom.ext
  funext n
  cases n with
  | zero =>
      change barRestrictionComponent (k := k) H 0 ≫
          (Rep.resFunctor H.subtype).map
            (barAugmentationZero (k := k) G) =
        barAugmentationZero (k := k) H
      exact barRestrictionComponent_zero_comp_augmentation (k := k) H
  | succ n => simp

/-- Let `G` be a group, `k` a commutative ring, `H ≤ G` finite index, and `T` a right transversal.
If `J_T=schreierTransferInducedBarChain H T : B_G → Ind_H^G B_H`, then
`schreierRestrictionBarChain H T : Res_H B_G → B_H` has degree-`n` component
`((Rep.resIndAdjunction k H).homEquiv _ _).symm (J_T.f n)`. Thus each component is the adjoint
of induced-bar transfer under the finite-index restriction–induction adjunction. -/
noncomputable def schreierRestrictionBarChain
    (T : H.RightTransversal) :
    ((Rep.resFunctor H.subtype).mapHomologicalComplex
      (ComplexShape.down ℕ)).obj (Rep.barComplex k G) ⟶
        Rep.barComplex k H := by
  let _ : DecidableRel (QuotientGroup.rightRel H) := Classical.decRel _
  exact
    { f := fun n => ((Rep.resIndAdjunction k H).homEquiv _ _).symm
        ((schreierTransferInducedBarChain (k := k) H T).f n)
      comm' := fun i j hij => by
        rcases hij with ⟨rfl⟩
        let adj := Rep.resIndAdjunction k H
        rw [← adj.homEquiv_naturality_right_symm]
        change (adj.homEquiv _ _).symm
            ((schreierTransferInducedBarChain (k := k) H T).f (j + 1) ≫
              (Rep.indFunctor k H.subtype).map
                ((Rep.barComplex k H).d (j + 1) j)) =
          (Rep.resFunctor H.subtype).map
              ((Rep.barComplex k G).d (j + 1) j) ≫
            (adj.homEquiv _ _).symm
              ((schreierTransferInducedBarChain (k := k) H T).f j)
        rw [← adj.homEquiv_naturality_left_symm]
        apply congrArg (adj.homEquiv _ _).symm
        exact (schreierTransferInducedBarChain (k := k) H T).comm _ _ }

/-- Let `G` be a group, `k` a commutative ring, `H ≤ G` finite index, and `T` a right transversal.
The chain map `schreierRestrictionBar H T` runs from the restricted complex of
`Rep.barResolution k G` to the complex of `Rep.barResolution k H`. Under the bar-complex
identifications, its components are those of `schreierRestrictionBarChain H T`, the adjoint
induced-bar transfer. -/
noncomputable def schreierRestrictionBar
    (T : H.RightTransversal) :
    ((Rep.resFunctor H.subtype).mapHomologicalComplex
      (ComplexShape.down ℕ)).obj (Rep.barResolution k G).complex ⟶
        (Rep.barResolution k H).complex := by
  rw [Rep.barResolution_complex, Rep.barResolution_complex]
  exact schreierRestrictionBarChain H T

/-- Let `G` be a group, `k` a commutative ring, `H ≤ G` finite index, and `T` a right transversal.
The degree-zero adjoint Schreier component satisfies `(schreierRestrictionBarChain H T).f 0 ≫
barAugmentationZero H = Res_H(barAugmentationZero G)` as morphisms from the restricted ambient
bar term to the trivial `H`-representation. -/
theorem schreierRestrictionBarChain_zero_comp_augmentation
    (T : H.RightTransversal) :
    (schreierRestrictionBarChain (k := k) H T).f 0 ≫
        barAugmentationZero (k := k) H =
      (Rep.resFunctor H.subtype).map
        (barAugmentationZero (k := k) G) := by
  let _ : DecidableRel (QuotientGroup.rightRel H) := Classical.decRel _
  let adj := Rep.resIndAdjunction k H
  apply (adj.homEquiv _ _).injective
  rw [adj.homEquiv_naturality_right]
  change (adj.homEquiv _ _)
        ((adj.homEquiv _ _).symm
          (schreierTransferInducedBarComponent (k := k) H T 0)) ≫
      (Rep.indFunctor k H.subtype).map
        (barAugmentationZero (k := k) H) = _
  rw [Equiv.apply_symm_apply]
  change (schreierTransferInducedBarComponent (k := k) H T 0) ≫
      inducedBarAugmentationZero (k := k) H = _
  rw [schreierTransferInducedBarComponent_zero_comp_augmentation]
  symm
  change (adj.homEquiv _ _)
      ((Rep.resFunctor H.subtype).map
        (barAugmentationZero (k := k) G)) =
    barAugmentationZero (k := k) G ≫ adj.unit.app _
  simpa only [Category.comp_id, adj.homEquiv_id] using
    adj.homEquiv_naturality_left
      (barAugmentationZero (k := k) G)
      (𝟙 ((Rep.resFunctor H.subtype).obj
        (Rep.trivial k G k)))

set_option backward.isDefEq.respectTransparency false in
/-- Let `G` be a group, `k` a commutative ring, `H ≤ G` finite index, and `T` a right transversal.
With `P_H=Rep.barResolution k H` and `R_H(P_G)` the restricted ambient bar projective
resolution, `schreierRestrictionBar H T ≫ P_H.π = R_H(P_G).π`. Hence this chain map lifts the
identity of the trivial `H`-representation. -/
theorem schreierRestrictionBar_comp_π
    (T : H.RightTransversal) :
    schreierRestrictionBar (k := k) H T ≫
        (Rep.barResolution k H).π =
      ((Rep.resFunctor H.subtype).mapProjectiveResolution
        (Rep.barResolution k G)).π := by
  apply HomologicalComplex.Hom.ext
  funext n
  cases n with
  | zero =>
      change (schreierRestrictionBarChain (k := k) H T).f 0 ≫
          barAugmentationZero (k := k) H =
        (Rep.resFunctor H.subtype).map
          (barAugmentationZero (k := k) G)
      exact schreierRestrictionBarChain_zero_comp_augmentation H T
  | succ n => simp

set_option backward.isDefEq.respectTransparency false in
/-- Let `G` be a group, `k` a commutative ring, `H ≤ G` finite index, and `T` a right transversal.
Put `P_H=Rep.barResolution k H` and `R_H(P_G)` for the restricted ambient bar projective
resolution. There is a chain homotopy from `schreierRestrictionBar H T` to
`ProjectiveResolution.lift (𝟙 (Rep.trivial k H k)) R_H(P_G) P_H`, the canonical comparison
lifting the identity on the resolved trivial representation. -/
noncomputable def schreierRestrictionBarHomotopy
    (T : H.RightTransversal) :
    Homotopy (schreierRestrictionBar (k := k) H T)
      (ProjectiveResolution.lift (𝟙 (Rep.trivial k H k))
        ((Rep.resFunctor H.subtype).mapProjectiveResolution
          (Rep.barResolution k G))
        (Rep.barResolution k H)) :=
  ProjectiveResolution.liftHomotopy
    (𝟙 (Rep.trivial k H k))
    (schreierRestrictionBar (k := k) H T)
    (ProjectiveResolution.lift (𝟙 (Rep.trivial k H k))
      ((Rep.resFunctor H.subtype).mapProjectiveResolution
        (Rep.barResolution k G))
      (Rep.barResolution k H))
    (by
      have hid :
          (ChainComplex.single₀ (Rep k H)).map
              (𝟙 (Rep.trivial k H k)) =
            𝟙 ((ChainComplex.single₀ (Rep k H)).obj
              (Rep.trivial k H k)) :=
        (ChainComplex.single₀ (Rep k H)).map_id _
      rw [hid, Category.comp_id]
      exact schreierRestrictionBar_comp_π H T)
    (by simp)

/-- Let `G` be a group, `k` a commutative ring, `H ≤ G` finite index, and `T` a right transversal.
Put `P_H=Rep.barResolution k H` and `R_H(P_G)` for the restricted ambient bar projective
resolution. The homotopy equivalence `schreierRestrictionBarHomotopyEquiv H T :
R_H(P_G).complex ≃ P_H.complex` has forward chain map `schreierRestrictionBar H T`. Its
composites with the reverse map are homotopic to the respective identities. -/
noncomputable def schreierRestrictionBarHomotopyEquiv
    (T : H.RightTransversal) :
    HomotopyEquiv
      ((Rep.resFunctor H.subtype).mapProjectiveResolution
        (Rep.barResolution k G)).complex
      (Rep.barResolution k H).complex :=
  (ProjectiveResolution.homotopyEquiv
    ((Rep.resFunctor H.subtype).mapProjectiveResolution
      (Rep.barResolution k G))
    (Rep.barResolution k H)).copy
      (schreierRestrictionBarHomotopy (k := k) H T).symm

set_option backward.isDefEq.respectTransparency false in
/-- Let `G` be a group, `k` a commutative ring, `H ≤ G` finite index, and `T` a right transversal.
For `F_T=schreierRestrictionBarHomotopyEquiv H T`, `P_H=Rep.barResolution k H`, and the
restricted resolution `R_H(P_G)`, `F_T.inv ≫ R_H(P_G).π = P_H.π`. Thus the reverse map also
lifts the identity on the trivial `H`-representation. -/
theorem schreierRestrictionBarHomotopyEquiv_inv_comp_π
    (T : H.RightTransversal) :
    (schreierRestrictionBarHomotopyEquiv (k := k) H T).inv ≫
        ((Rep.resFunctor H.subtype).mapProjectiveResolution
          (Rep.barResolution k G)).π =
      (Rep.barResolution k H).π := by
  change (ProjectiveResolution.homotopyEquiv
      ((Rep.resFunctor H.subtype).mapProjectiveResolution
        (Rep.barResolution k G))
      (Rep.barResolution k H)).inv ≫
        ((Rep.resFunctor H.subtype).mapProjectiveResolution
          (Rep.barResolution k G)).π =
      (Rep.barResolution k H).π
  exact ProjectiveResolution.homotopyEquiv_inv_π _ _

set_option backward.isDefEq.respectTransparency false in
/-- Let `G` be a group, `k` a commutative ring, `H ≤ G` finite index, and `T` a right transversal.
The reverse chain map of `schreierRestrictionBarHomotopyEquiv H T` is homotopic to
`barRestriction H : (Rep.barResolution k H).complex → R_H(Rep.barResolution k G).complex`.
Both comparisons preserve augmentation and lift the identity on the trivial
`H`-representation. -/
noncomputable def schreierShapiroInverseBarRestrictionHomotopy
    (T : H.RightTransversal) :
    Homotopy
      (schreierRestrictionBarHomotopyEquiv (k := k) H T).inv
      (barRestriction (k := k) H) :=
  ProjectiveResolution.liftHomotopy
    (𝟙 (Rep.trivial k H k))
    (schreierRestrictionBarHomotopyEquiv (k := k) H T).inv
    (barRestriction (k := k) H)
    (by
      have hid :
          (ChainComplex.single₀ (Rep k H)).map
              (𝟙 (Rep.trivial k H k)) =
            𝟙 ((ChainComplex.single₀ (Rep k H)).obj
              (Rep.trivial k H k)) :=
        (ChainComplex.single₀ (Rep k H)).map_id _
      rw [hid, Category.comp_id]
      exact schreierRestrictionBarHomotopyEquiv_inv_comp_π H T)
    (by
      have hid :
          (ChainComplex.single₀ (Rep k H)).map
              (𝟙 (Rep.trivial k H k)) =
            𝟙 ((ChainComplex.single₀ (Rep k H)).obj
              (Rep.trivial k H k)) :=
        (ChainComplex.single₀ (Rep k H)).map_id _
      rw [hid, Category.comp_id]
      exact barRestriction_comp_π (k := k) H)

/-- Let `G` be a group, `k` a commutative ring, `H ≤ G` finite index, `B : Rep k H`, and `T` a
right transversal. For `P_H` and the restricted ambient resolution `R_H(P_G)`, applying the
contravariant linear-Hom cochain functor gives a homotopy equivalence `L(P_H,B) ≃
L(R_H(P_G),B)`. Its forward map precomposes with `schreierRestrictionBar H T`; its reverse map
precomposes with the reverse bar-resolution comparison. -/
noncomputable def schreierRestrictionLinearHomHomotopyEquiv
    (B : Rep k H) (T : H.RightTransversal) :
    HomotopyEquiv
      ((HomologicalComplex.linearHomCochainComplexFunctor
        k (Rep k H) B).obj
          (Opposite.op (Rep.barResolution k H).complex))
      ((HomologicalComplex.linearHomCochainComplexFunctor
        k (Rep k H) B).obj
          (Opposite.op
            ((Rep.resFunctor H.subtype).mapProjectiveResolution
              (Rep.barResolution k G)).complex)) :=
  HomologicalComplex.HomotopyEquiv.mapLinearHomCochainComplex k
    (schreierRestrictionBarHomotopyEquiv (k := k) H T) B

@[simp]
theorem schreierRestrictionLinearHomHomotopyEquiv_hom
    (B : Rep k H) (T : H.RightTransversal) :
    (schreierRestrictionLinearHomHomotopyEquiv H B T).hom =
      (HomologicalComplex.linearHomCochainComplexFunctor
        k (Rep k H) B).map
          (schreierRestrictionBar (k := k) H T).op :=
  rfl

/-- Let `G` be a group, `k` a commutative ring, `H ≤ G` finite index, `B : Rep k H`, and `T` a
right transversal. The homotopy equivalence `schreierCoindShapiroInvCochainHomotopyEquiv H B
T` runs from `C^*(H,B)` to `C^*(G,Coind_H^G B)`. It combines the inhomogeneous/bar
comparisons, precomposition with the adjoint Schreier map, and the restriction–coinduction Hom
adjunction. Its forward map induces inverse Shapiro on cohomology. -/
noncomputable def schreierCoindShapiroInvCochainHomotopyEquiv
    (B : Rep k H) (T : H.RightTransversal) :
    HomotopyEquiv
      (inhomogeneousCochains B)
      (inhomogeneousCochains (Rep.coind H.subtype B)) :=
  (HomotopyEquiv.ofIso
      (inhomogeneousResolutionLinearHomCochainIso B)).trans <|
    (schreierRestrictionLinearHomHomotopyEquiv H B T).trans <|
      (HomotopyEquiv.ofIso
        (linearHomCochainComplexObjIso B
          ((Rep.resFunctor H.subtype).mapProjectiveResolution
            (Rep.barResolution k G)).complex)).trans <|
        (HomotopyEquiv.ofIso
          (linearYonedaObjResProjectiveResolutionIso
            (Rep.barResolution k G) B)).trans <|
          (HomotopyEquiv.ofIso
            (linearHomCochainComplexObjIso
              (Rep.coind H.subtype B)
              (Rep.barResolution k G).complex).symm).trans <|
            HomotopyEquiv.ofIso
              (inhomogeneousResolutionLinearHomCochainIso
                (Rep.coind H.subtype B)).symm

/-- Let `G` be a group, `k` a commutative ring, `H ≤ G`, and `A : Rep k G`. The cochain map
`ambientRestrictedBarCochains H A : C^*(G,A) → L(R_H(P_G),Res_H A)` carries each ambient
inhomogeneous cochain to its equivariant bar morphism restricted to `H`. Here
`P_G=Rep.barResolution k G` and `L` is the linear-Hom cochain complex. -/
noncomputable def ambientRestrictedBarCochains (A : Rep k G) :
    inhomogeneousCochains A ⟶
      (HomologicalComplex.linearHomCochainComplexFunctor
        k (Rep k H) (Rep.res H.subtype A)).obj
          (Opposite.op
            ((Rep.resFunctor H.subtype).mapProjectiveResolution
              (Rep.barResolution k G)).complex) :=
  cochainsMap (MonoidHom.id G)
      ((Rep.resCoindAdjunction k H.subtype).unit.app A) ≫
    (inhomogeneousResolutionLinearHomCochainIso
      (Rep.coind H.subtype (Rep.res H.subtype A))).hom ≫
    (linearHomCochainComplexObjIso
      (Rep.coind H.subtype (Rep.res H.subtype A))
      (Rep.barResolution k G).complex).hom ≫
    (linearYonedaObjResProjectiveResolutionIso
      (Rep.barResolution k G) (Rep.res H.subtype A)).inv ≫
    (linearHomCochainComplexObjIso
      (Rep.res H.subtype A)
      ((Rep.resFunctor H.subtype).mapProjectiveResolution
        (Rep.barResolution k G)).complex).inv

set_option backward.isDefEq.respectTransparency false in
omit [H.FiniteIndex] in
/-- Let `G` be a group, `k` a commutative ring, `H ≤ G`, `A : Rep k G`, `n : ℕ`, and `z : (Fin n →
G) → A`. Then `(ambientRestrictedBarCochains H A).f n (z) = (Rep.resFunctor H.subtype).map
(Rep.freeLift k G A z)`. This identifies the degree-`n` restricted bar morphism with the
restriction of the ambient equivariant linear extension. -/
theorem ambientRestrictedBarCochains_f_apply
    (A : Rep k G) (n : ℕ) (z : (Fin n → G) → A) :
    ((ambientRestrictedBarCochains H A).f n).hom z =
      (Rep.resFunctor H.subtype).map (Rep.freeLift k G A z) := by
  unfold ambientRestrictedBarCochains
  simp only [HomologicalComplex.comp_f, ModuleCat.hom_comp,
    LinearMap.comp_apply]
  change (Rep.resCoindHomEquiv H.subtype
      ((Rep.barComplex k G).X n) (Rep.res H.subtype A)).symm
        (Rep.freeLift k G
          (Rep.coind H.subtype (Rep.res H.subtype A))
          (fun g => ((Rep.resCoindAdjunction
            k H.subtype).unit.app A).hom (z g))) = _
  have hfree :
      Rep.freeLift k G
          (Rep.coind H.subtype (Rep.res H.subtype A))
          (fun g => ((Rep.resCoindAdjunction
            k H.subtype).unit.app A).hom (z g)) =
        Rep.freeLift k G A z ≫
          (Rep.resCoindAdjunction k H.subtype).unit.app A := by
    apply Rep.free_ext k G _
    intro g
    change (Rep.freeLift k G
        (Rep.coind H.subtype (Rep.res H.subtype A))
        (fun g => ((Rep.resCoindAdjunction
          k H.subtype).unit.app A).hom (z g))).hom
          (barBasis (k := k) n g) =
      (Rep.freeLift k G A z ≫
        (Rep.resCoindAdjunction k H.subtype).unit.app A).hom
          (barBasis (k := k) n g)
    rw [freeLift_barBasis]
    change ((Rep.resCoindAdjunction k H.subtype).unit.app A).hom
        (z g) =
      ((Rep.resCoindAdjunction k H.subtype).unit.app A).hom
        ((Rep.freeLift k G A z).hom
          (barBasis (k := k) n g))
    rw [freeLift_barBasis]
  rw [hfree, resCoindHomEquiv_symm_comp_unit]

/-- Let `G` be a group, `k` a commutative ring, `H ≤ G` finite index, `A : Rep k G`, and `T` a
right transversal. Write `η_A` for the restriction–coinduction unit and
`Ψ_T=schreierCoindShapiroInvCochainHomotopyEquiv H (Res_H A) T`. The cochain map
`coindUnitSchreierShapiroCochains H A T : C^*(G,A) → C^*(H,Res_H A)` is `cochainsMap (id G)
η_A ≫ Ψ_T.inv`. -/
noncomputable def coindUnitSchreierShapiroCochains
    (A : Rep k G) (T : H.RightTransversal) :
    inhomogeneousCochains A ⟶
      inhomogeneousCochains (Rep.res H.subtype A) :=
  cochainsMap (MonoidHom.id G)
      ((Rep.resCoindAdjunction k H.subtype).unit.app A) ≫
    (schreierCoindShapiroInvCochainHomotopyEquiv H
      (Rep.res H.subtype A) T).inv

set_option backward.isDefEq.respectTransparency false in
/-- Let `G` be a group, `k` a commutative ring, `H ≤ G` finite index, `A : Rep k G`, `T` a right
transversal, and `n : ℕ`. For `z : (Fin n → G) → A` and `q : Fin n → H`, the value of
`coindUnitSchreierShapiroCochains H A T` is `(F_T.inv.f n ≫ Res_H(Rep.freeLift k G A
z))(barBasis_H n q)`, where `F_T=schreierRestrictionBarHomotopyEquiv H T` and the basis has
unit group-ring coefficient. -/
theorem coindUnitSchreierShapiroCochains_f_apply
    (A : Rep k G) (T : H.RightTransversal) (n : ℕ)
    (z : (Fin n → G) → A) (q : Fin n → H) :
    ((coindUnitSchreierShapiroCochains H A T).f n).hom z q =
      (((schreierRestrictionBarHomotopyEquiv (k := k) H T).inv.f n ≫
        (Rep.resFunctor H.subtype).map
          (Rep.freeLift k G A z)).hom
        (barBasis (k := k) n q)) := by
  dsimp only [coindUnitSchreierShapiroCochains,
    schreierCoindShapiroInvCochainHomotopyEquiv,
    HomotopyEquiv.trans, HomotopyEquiv.ofIso]
  simp only [HomologicalComplex.comp_f, ModuleCat.hom_comp,
    LinearMap.comp_apply]
  change (((schreierRestrictionBarHomotopyEquiv
      (k := k) H T).inv.f n ≫
        (Rep.resCoindHomEquiv H.subtype
          ((Rep.barComplex k G).X n) (Rep.res H.subtype A)).symm
            (Rep.freeLift k G
              (Rep.coind H.subtype (Rep.res H.subtype A))
              (fun g => ((Rep.resCoindAdjunction
                k H.subtype).unit.app A).hom (z g)))).hom
      (barBasis (k := k) n q)) = _
  have hfree :
      Rep.freeLift k G
          (Rep.coind H.subtype (Rep.res H.subtype A))
          (fun g => ((Rep.resCoindAdjunction
            k H.subtype).unit.app A).hom (z g)) =
        Rep.freeLift k G A z ≫
          (Rep.resCoindAdjunction k H.subtype).unit.app A := by
    apply Rep.free_ext k G _
    intro g
    change (Rep.freeLift k G
        (Rep.coind H.subtype (Rep.res H.subtype A))
        (fun g => ((Rep.resCoindAdjunction
          k H.subtype).unit.app A).hom (z g))).hom
          (barBasis (k := k) n g) =
      (Rep.freeLift k G A z ≫
        (Rep.resCoindAdjunction k H.subtype).unit.app A).hom
          (barBasis (k := k) n g)
    rw [freeLift_barBasis]
    change ((Rep.resCoindAdjunction k H.subtype).unit.app A).hom
        (z g) =
      ((Rep.resCoindAdjunction k H.subtype).unit.app A).hom
        ((Rep.freeLift k G A z).hom
          (barBasis (k := k) n g))
    rw [freeLift_barBasis]
  rw [hfree, resCoindHomEquiv_symm_comp_unit]

set_option backward.isDefEq.respectTransparency false in
/-- Let `G` be a group, `k` a commutative ring, `H ≤ G` finite index, `A : Rep k G`, and `T` a
right transversal. Put `F_T=schreierRestrictionBarHomotopyEquiv H T`,
`I_H=inhomogeneousResolutionLinearHomCochainIso (Res_H A)`, and `L` the contravariant
Hom-cochain functor with coefficient `Res_H A`. Then `coindUnitSchreierShapiroCochains H A T ≫
I_H.hom = ambientRestrictedBarCochains H A ≫ L.map F_T.inv.op`. -/
theorem coindUnitSchreierShapiroCochains_comp_resolutionIso
    (A : Rep k G) (T : H.RightTransversal) :
    coindUnitSchreierShapiroCochains H A T ≫
        (inhomogeneousResolutionLinearHomCochainIso
          (Rep.res H.subtype A)).hom =
      ambientRestrictedBarCochains H A ≫
        (HomologicalComplex.linearHomCochainComplexFunctor
          k (Rep k H) (Rep.res H.subtype A)).map
            (schreierRestrictionBarHomotopyEquiv
              (k := k) H T).inv.op := by
  ext n z
  apply Rep.free_ext k H _
  intro q
  simp only [HomologicalComplex.comp_f, ModuleCat.hom_comp,
    LinearMap.comp_apply]
  change (Rep.freeLift k H (Rep.res H.subtype A)
      (((coindUnitSchreierShapiroCochains H A T).f n).hom z)).hom
        (barBasis (k := k) n q) =
    (((schreierRestrictionBarHomotopyEquiv (k := k) H T).inv.f n ≫
      ((ambientRestrictedBarCochains H A).f n).hom z).hom
        (barBasis (k := k) n q))
  rw [freeLift_barBasis]
  rw [coindUnitSchreierShapiroCochains_f_apply,
    ambientRestrictedBarCochains_f_apply]

set_option backward.isDefEq.respectTransparency false in
omit [H.FiniteIndex] in
/-- Let `G` be a group, `k` a commutative ring, `H ≤ G`, and `A : Rep k G`. Put
`I_H=inhomogeneousResolutionLinearHomCochainIso (Res_H A)` and let `L` be the contravariant
Hom-cochain functor with coefficient `Res_H A`. Then `cochainsMap H.subtype (𝟙 (Res_H A)) ≫
I_H.hom = ambientRestrictedBarCochains H A ≫ L.map (barRestriction H).op`. Thus subgroup
restriction is precomposition by the bar inclusion after the ambient cochain comparison. -/
theorem restrictionCochains_comp_resolutionIso
    (A : Rep k G) :
    cochainsMap H.subtype (𝟙 (Rep.res H.subtype A)) ≫
        (inhomogeneousResolutionLinearHomCochainIso
          (Rep.res H.subtype A)).hom =
      ambientRestrictedBarCochains H A ≫
        (HomologicalComplex.linearHomCochainComplexFunctor
          k (Rep k H) (Rep.res H.subtype A)).map
            (barRestriction (k := k) H).op := by
  ext n z
  apply Rep.free_ext k H _
  intro q
  simp only [HomologicalComplex.comp_f, ModuleCat.hom_comp,
    LinearMap.comp_apply]
  change (Rep.freeLift k H (Rep.res H.subtype A)
      (fun q => z (fun i => (q i : G)))).hom
        (barBasis (k := k) n q) =
    (((barRestriction (k := k) H).f n ≫
      ((ambientRestrictedBarCochains H A).f n).hom z).hom
        (barBasis (k := k) n q))
  rw [freeLift_barBasis]
  rw [ambientRestrictedBarCochains_f_apply]
  change z (fun i => (q i : G)) =
    ((Rep.resFunctor H.subtype).map
      (Rep.freeLift k G A z)).hom
        ((barRestrictionComponent (k := k) H n).hom
          (barBasis (k := k) n q))
  rw [barRestrictionComponent_barBasis]
  change z (fun i => (q i : G)) =
    (Rep.freeLift k G A z).hom
      (barBasis (k := k) n (fun i => (q i : G)))
  rw [freeLift_barBasis]

set_option backward.isDefEq.respectTransparency false in
/-- Let `G` be a group, `k` a commutative ring, `H ≤ G` finite index, `A : Rep k G`, `T` a right
transversal, and `n : ℕ`. The map induced by `coindUnitSchreierShapiroCochains H A T` on
degree-`n` cohomology equals `map H.subtype (𝟙 (Res_H A)) n : H^n(G,A) → H^n(H,Res_H A)`. -/
theorem homologyMap_coindUnitSchreierShapiroCochains
    (A : Rep k G) (T : H.RightTransversal) (n : ℕ) :
    HomologicalComplex.homologyMap
        (coindUnitSchreierShapiroCochains H A T) n =
      groupCohomology.map H.subtype
        (𝟙 (Rep.res H.subtype A)) n := by
  let B := Rep.res H.subtype A
  let e := inhomogeneousResolutionLinearHomCochainIso B
  let F := HomologicalComplex.linearHomCochainComplexFunctor
    k (Rep k H) B
  let a := ambientRestrictedBarCochains H A
  let f := F.map
    (schreierRestrictionBarHomotopyEquiv (k := k) H T).inv.op
  let g := F.map (barRestriction (k := k) H).op
  have hSquare :
      coindUnitSchreierShapiroCochains H A T ≫ e.hom = a ≫ f :=
    coindUnitSchreierShapiroCochains_comp_resolutionIso H A T
  have hRestriction :
      cochainsMap H.subtype (𝟙 B) ≫ e.hom = a ≫ g :=
    restrictionCochains_comp_resolutionIso H A
  have hBar :
      HomologicalComplex.homologyMap f n =
        HomologicalComplex.homologyMap g n :=
    ((schreierShapiroInverseBarRestrictionHomotopy
      (k := k) H T).mapLinearHomCochainComplex k B).homologyMap_eq n
  apply (cancel_mono
    (HomologicalComplex.homologyMap e.hom n)).mp
  calc
    HomologicalComplex.homologyMap
          (coindUnitSchreierShapiroCochains H A T) n ≫
        HomologicalComplex.homologyMap e.hom n =
      HomologicalComplex.homologyMap
        (coindUnitSchreierShapiroCochains H A T ≫ e.hom) n := by
          rw [HomologicalComplex.homologyMap_comp]
    _ = HomologicalComplex.homologyMap (a ≫ f) n := by rw [hSquare]
    _ = HomologicalComplex.homologyMap a n ≫
        HomologicalComplex.homologyMap f n := by
          rw [HomologicalComplex.homologyMap_comp]
    _ = HomologicalComplex.homologyMap a n ≫
        HomologicalComplex.homologyMap g n := by rw [hBar]
    _ = HomologicalComplex.homologyMap (a ≫ g) n := by
          rw [HomologicalComplex.homologyMap_comp]
    _ = HomologicalComplex.homologyMap
        (cochainsMap H.subtype (𝟙 B) ≫ e.hom) n := by
          rw [hRestriction]
    _ = groupCohomology.map H.subtype (𝟙 B) n ≫
        HomologicalComplex.homologyMap e.hom n := by
          rw [HomologicalComplex.homologyMap_comp]

set_option backward.isDefEq.respectTransparency false in
/-- Let `G` be a group, `k` a commutative ring, `H ≤ G` finite index, `A : Rep k G`, and `T` a
right transversal. Put `Ψ_T=schreierCoindShapiroInvCochainHomotopyEquiv H (Res_H A) T` and
`ε_A=corestrictionCounit H A`. Then `Ψ_T.hom ≫ cochainsMap (id G) ε_A = corestrictionCochains
A T`, as maps `C^*(H,Res_H A) → C^*(G,A)`. -/
theorem schreierCoindShapiroInvCochains_comp_counit
    (A : Rep k G) (T : H.RightTransversal) :
    (schreierCoindShapiroInvCochainHomotopyEquiv H
        (Rep.res H.subtype A) T).hom ≫
      cochainsMap (MonoidHom.id G) (corestrictionCounit H A) =
        corestrictionCochains A T := by
  ext n z g
  change (corestrictionCounit H A).hom
      ((Rep.resCoindHomEquiv H.subtype
        ((Rep.barComplex k G).X n) (Rep.res H.subtype A)
        ((schreierRestrictionBarChain (k := k) H T).f n ≫
          Rep.freeLift k H (Rep.res H.subtype A) z)).hom
        (barBasis (k := k) n g)) =
    corestrictionCochain A T n z g
  have hadj :
      (Rep.resIndAdjunction k H).homEquiv _ _
          ((schreierRestrictionBarChain (k := k) H T).f n) =
        schreierTransferInducedBarComponent (k := k) H T n := by
    change (Rep.resIndAdjunction k H).homEquiv _ _
        (((Rep.resIndAdjunction k H).homEquiv _ _).symm
          (schreierTransferInducedBarComponent (k := k) H T n)) = _
    exact Equiv.apply_symm_apply _ _
  have hmate := resCoindHomEquiv_comp_corestrictionCounit H A
    ((schreierRestrictionBarChain (k := k) H T).f n)
    (Rep.freeLift k H (Rep.res H.subtype A) z)
  rw [hadj,
    schreierTransferInducedBarComponent_comp_adjointFreeLift] at hmate
  have hbasis := congrArg
    (fun f : (Rep.barComplex k G).X n ⟶ A =>
      f.hom (barBasis (k := k) n g)) hmate
  change (corestrictionCounit H A).hom
      ((Rep.resCoindHomEquiv H.subtype
        ((Rep.barComplex k G).X n) (Rep.res H.subtype A)
        ((schreierRestrictionBarChain (k := k) H T).f n ≫
          Rep.freeLift k H (Rep.res H.subtype A) z)).hom
        (barBasis (k := k) n g)) =
    (Rep.freeLift k G A (corestrictionCochain A T n z)).hom
      (barBasis (k := k) n g) at hbasis
  rw [freeLift_barBasis] at hbasis
  exact hbasis

/-- Let `G` be a group, `k` a commutative ring, `H ≤ G` finite index, `B : Rep k H`, `T` a right
transversal, and `n : ℕ`. The isomorphism `schreierCoindShapiroIso H B T n : H^n(G,Coind_H^G
B) ≅ H^n(H,B)` is the inverse of the homology isomorphism induced by
`schreierCoindShapiroInvCochainHomotopyEquiv H B T`. Its inverse morphism is induced by that
cochain equivalence's forward map. -/
noncomputable def schreierCoindShapiroIso
    (B : Rep k H) (T : H.RightTransversal) (n : ℕ) :
    groupCohomology (Rep.coind H.subtype B) n ≅
      groupCohomology B n :=
  (schreierCoindShapiroInvCochainHomotopyEquiv H B T
    ).toHomologyIso n |>.symm

@[simp]
theorem schreierCoindShapiroIso_inv
    (B : Rep k H) (T : H.RightTransversal) (n : ℕ) :
    (schreierCoindShapiroIso H B T n).inv =
      HomologicalComplex.homologyMap
        (schreierCoindShapiroInvCochainHomotopyEquiv H B T).hom n :=
  rfl

@[simp]
theorem schreierCoindShapiroIso_hom
    (B : Rep k H) (T : H.RightTransversal) (n : ℕ) :
    (schreierCoindShapiroIso H B T n).hom =
      HomologicalComplex.homologyMap
        (schreierCoindShapiroInvCochainHomotopyEquiv H B T).inv n :=
  rfl

/-- Let `G` be a group, `k` a commutative ring, `H ≤ G` finite index, `A : Rep k G`, `T` a right
transversal, and `n : ℕ`. For `η_A=(Rep.resCoindAdjunction k H.subtype).unit.app A` and
`S_T=schreierCoindShapiroIso H (Res_H A) T n`, `map (id G) η_A n ≫ S_T.hom = map H.subtype (𝟙
(Res_H A)) n` as maps `H^n(G,A) → H^n(H,Res_H A)`. -/
theorem map_unit_comp_schreierCoindShapiroIso_hom
    (A : Rep k G) (T : H.RightTransversal) (n : ℕ) :
    groupCohomology.map (MonoidHom.id G)
        ((Rep.resCoindAdjunction k H.subtype).unit.app A) n ≫
      (schreierCoindShapiroIso H
        (Rep.res H.subtype A) T n).hom =
      groupCohomology.map H.subtype
        (𝟙 (Rep.res H.subtype A)) n := by
  rw [schreierCoindShapiroIso_hom]
  change HomologicalComplex.homologyMap
        (cochainsMap (MonoidHom.id G)
          ((Rep.resCoindAdjunction k H.subtype).unit.app A)) n ≫
      HomologicalComplex.homologyMap
        (schreierCoindShapiroInvCochainHomotopyEquiv H
          (Rep.res H.subtype A) T).inv n = _
  rw [← HomologicalComplex.homologyMap_comp]
  change HomologicalComplex.homologyMap
      (coindUnitSchreierShapiroCochains H A T) n = _
  exact homologyMap_coindUnitSchreierShapiroCochains H A T n

/-- Let `G` be a group, `k` a commutative ring, `H ≤ G` finite index, `A : Rep k G`, `T` a right
transversal, and `n : ℕ`. For `S_T=schreierCoindShapiroIso H (Res_H A) T n` and
`ε_A=corestrictionCounit H A`, `S_T.inv ≫ map (id G) ε_A n = corestrictionOfRightTransversal A
T n` as maps `H^n(H,Res_H A) → H^n(G,A)`. -/
theorem schreierCoindShapiroIso_inv_comp_corestrictionCounit
    (A : Rep k G) (T : H.RightTransversal) (n : ℕ) :
    (schreierCoindShapiroIso H (Rep.res H.subtype A) T n).inv ≫
        groupCohomology.map (MonoidHom.id G)
          (corestrictionCounit H A) n =
      corestrictionOfRightTransversal A T n := by
  rw [schreierCoindShapiroIso_inv]
  change HomologicalComplex.homologyMap
        (schreierCoindShapiroInvCochainHomotopyEquiv H
          (Rep.res H.subtype A) T).hom n ≫
      HomologicalComplex.homologyMap
        (cochainsMap (MonoidHom.id G) (corestrictionCounit H A)) n =
    HomologicalComplex.homologyMap (corestrictionCochains A T) n
  rw [← HomologicalComplex.homologyMap_comp,
    schreierCoindShapiroInvCochains_comp_counit]

/-- Let `G` be a group, `k` a commutative ring, `H ≤ G` finite index, `A : Rep k G`, `T` a right
transversal, and `n : ℕ`. For `S_T=schreierCoindShapiroIso H (Res_H A) T n` and
`ε_A=corestrictionCounit H A`, `S_T.inv ≫ map (id G) ε_A n = schreierCorestriction H A n`.
Thus this composite `H^n(H,Res_H A) → H^n(G,A)` is independent of the chosen right
transversal. -/
theorem schreierCoindShapiroIso_inv_comp_schreierCorestriction
    (A : Rep k G) (T : H.RightTransversal) (n : ℕ) :
    (schreierCoindShapiroIso H (Rep.res H.subtype A) T n).inv ≫
        groupCohomology.map (MonoidHom.id G)
          (corestrictionCounit H A) n =
      schreierCorestriction H A n := by
  rw [schreierCoindShapiroIso_inv_comp_corestrictionCounit,
    ← schreierCorestriction_eq_of_rightTransversal H A T n]

/-- Let `G` be a group, `k` a commutative ring, `ℓ : ℕ` nonzero, `χ : G → Multiplicative (ZMod ℓ)`
a surjective group homomorphism, `A : Rep k G`, `T` a right transversal for `J=ker χ`, and `n
: ℕ`. Put `c(g)=Multiplicative.toAdd (χ g)`. The isomorphism `H^n(G,P_χ(A)) ≅ H^n(J,Res_J A)`
composes the coefficient comparison `p ↦ (g ↦ ρ_A(g)p(c(g)))` with Schreier Shapiro. Here
`P_χ(A)` has carrier `ZMod ℓ → A` and action `(g·p)(i)=ρ_A(g)p(i+c(g))`. -/
noncomputable def schreierCyclicPermutationShapiroIso
    (ell : ℕ) [NeZero ell]
    (chi : G →* Multiplicative (ZMod ell))
    (hchi : Function.Surjective chi) (A : Rep.{u} k G)
    (T : chi.ker.RightTransversal) (n : ℕ) :
    groupCohomology (Rep.cyclicPermutation ell chi A) n ≅
      groupCohomology (Rep.res chi.ker.subtype A) n := by
  let _ : Finite (G ⧸ chi.ker) :=
    Finite.of_equiv (Multiplicative (ZMod ell))
      (QuotientGroup.quotientKerEquivOfSurjective chi hchi).symm
  let _ : chi.ker.FiniteIndex :=
    Subgroup.finiteIndex_of_finite_quotient
  exact cyclicPermutationCoinducedCohomologyIso
      ell chi hchi A n ≪≫
    schreierCoindShapiroIso chi.ker
      (Rep.res chi.ker.subtype A) T n

@[simp]
theorem schreierCyclicPermutationShapiroIso_inv
    (ell : ℕ) [NeZero ell]
    (chi : G →* Multiplicative (ZMod ell))
    (hchi : Function.Surjective chi) (A : Rep.{u} k G)
    (T : chi.ker.RightTransversal) (n : ℕ) :
    (schreierCyclicPermutationShapiroIso
        ell chi hchi A T n).inv =
      (schreierCoindShapiroIso chi.ker
          (Rep.res chi.ker.subtype A) T n).inv ≫
        (cyclicPermutationCoinducedCohomologyIso
          ell chi hchi A n).inv := by
  let _ : Finite (G ⧸ chi.ker) :=
    Finite.of_equiv (Multiplicative (ZMod ell))
      (QuotientGroup.quotientKerEquivOfSurjective chi hchi).symm
  let _ : chi.ker.FiniteIndex :=
    Subgroup.finiteIndex_of_finite_quotient
  rfl

@[simp]
theorem schreierCyclicPermutationShapiroIso_hom
    (ell : ℕ) [NeZero ell]
    (chi : G →* Multiplicative (ZMod ell))
    (hchi : Function.Surjective chi) (A : Rep.{u} k G)
    (T : chi.ker.RightTransversal) (n : ℕ) :
    (schreierCyclicPermutationShapiroIso
        ell chi hchi A T n).hom =
      (cyclicPermutationCoinducedCohomologyIso
          ell chi hchi A n).hom ≫
        (schreierCoindShapiroIso chi.ker
          (Rep.res chi.ker.subtype A) T n).hom := by
  let _ : Finite (G ⧸ chi.ker) :=
    Finite.of_equiv (Multiplicative (ZMod ell))
      (QuotientGroup.quotientKerEquivOfSurjective chi hchi).symm
  let _ : chi.ker.FiniteIndex :=
    Subgroup.finiteIndex_of_finite_quotient
  rfl

/-- Let `G` be a group, `k` a commutative ring, `ℓ : ℕ` nonzero, `χ : G → Multiplicative (ZMod ℓ)`
surjective, and `A : Rep k G`. For `J=ker χ`, `F_χ=Rep.cyclicPermutationCoinducedIso ℓ χ hχ
A`, and `ε_A=corestrictionCounit J A`, `F_χ.hom ≫ ε_A = Rep.cyclicPermutationAugmentation ℓ χ
A`. The comparison sends `p` to `g ↦ ρ_A(g)p(Multiplicative.toAdd (χ g))`, and the
augmentation sends `p` to `∑ i : ZMod ℓ, p(i)`. -/
theorem cyclicPermutationCoinducedIso_hom_comp_corestrictionCounit
    (ell : ℕ) [NeZero ell]
    (chi : G →* Multiplicative (ZMod ell))
    (hchi : Function.Surjective chi) (A : Rep.{u} k G) :
    (Rep.cyclicPermutationCoinducedIso ell chi hchi A).hom ≫
        corestrictionCounit chi.ker A =
      Rep.cyclicPermutationAugmentation ell chi A := by
  let _ : Finite (G ⧸ chi.ker) :=
    Finite.of_equiv (Multiplicative (ZMod ell))
      (QuotientGroup.quotientKerEquivOfSurjective chi hchi).symm
  let _ : chi.ker.FiniteIndex :=
    Subgroup.finiteIndex_of_finite_quotient
  let T : chi.ker.RightTransversal := default
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro p
  change (corestrictionCounit chi.ker A).hom
      ((Rep.cyclicPermutationCoinducedIso ell chi hchi A).hom.hom p) =
    ∑ i : ZMod ell, p i
  rw [corestrictionCounit_apply_eq_sum chi.ker A T]
  have hcancel (t : (T : Set G)) (x : A) :
      A.ρ (t : G)⁻¹ (A.ρ (t : G) x) = x := by
    rw [← Module.End.mul_apply, ← map_mul]
    simp
  have hterm (t : (T : Set G)) :
      A.ρ (t : G)⁻¹
          (((Rep.cyclicPermutationCoinducedIso
            ell chi hchi A).hom.hom p).1 (t : G)) =
        p (Multiplicative.toAdd (chi (t : G))) := by
    rw [Rep.cyclicPermutationCoinducedIso_hom_apply]
    exact hcancel t _
  simp_rw [hterm]
  let e : (T : Set G) ≃ ZMod ell :=
    ((rightTransversalEquivCodomain chi hchi T).trans
      (Equiv.inv (Multiplicative (ZMod ell)))).trans Multiplicative.toAdd
  have he (t : (T : Set G)) :
      e t = Multiplicative.toAdd (chi (t : G)) := by
    dsimp only [e]
    rw [Equiv.trans_apply, Equiv.trans_apply,
      rightTransversalEquivCodomain_apply]
    simp
  calc
    (∑ t : (T : Set G), p (Multiplicative.toAdd (chi (t : G)))) =
        ∑ t : (T : Set G), p (e t) := by
      apply Finset.sum_congr rfl
      intro t _ht
      rw [he]
    _ = ∑ i : ZMod ell, p i := Equiv.sum_comp e p

set_option backward.isDefEq.respectTransparency false in
/-- Let `G` be a group, `k` a commutative ring, `ℓ : ℕ` nonzero, `χ : G → Multiplicative (ZMod ℓ)`
surjective, `A : Rep k G`, `T` a right transversal for `J=ker χ`, and `n : ℕ`. For
`S_χ=schreierCyclicPermutationShapiroIso ℓ χ hχ A T n` and
`a_χ=Rep.cyclicPermutationAugmentation ℓ χ A`, `S_χ.inv ≫ map (id G) a_χ n =
corestrictionOfRightTransversal A T n`. The map `a_χ` sums the cyclic coordinates. -/
theorem schreierCyclicPermutationShapiroIso_inv_comp_augmentation
    (ell : ℕ) [NeZero ell]
    (chi : G →* Multiplicative (ZMod ell))
    (hchi : Function.Surjective chi) (A : Rep.{u} k G)
    (T : chi.ker.RightTransversal) (n : ℕ) :
    (schreierCyclicPermutationShapiroIso
        ell chi hchi A T n).inv ≫
      groupCohomology.map (MonoidHom.id G)
        (Rep.cyclicPermutationAugmentation ell chi A) n =
      corestrictionOfRightTransversal A T n := by
  let _ : Finite (G ⧸ chi.ker) :=
    Finite.of_equiv (Multiplicative (ZMod ell))
      (QuotientGroup.quotientKerEquivOfSurjective chi hchi).symm
  let _ : chi.ker.FiniteIndex :=
    Subgroup.finiteIndex_of_finite_quotient
  have hCoeff :
      (cyclicPermutationCoinducedCohomologyIso
          ell chi hchi A n).inv ≫
          groupCohomology.map (MonoidHom.id G)
            (Rep.cyclicPermutationAugmentation ell chi A) n =
        groupCohomology.map (MonoidHom.id G)
          (corestrictionCounit chi.ker A) n := by
    apply (cancel_epi
      (cyclicPermutationCoinducedCohomologyIso
        ell chi hchi A n).hom).mp
    simp only [Iso.hom_inv_id_assoc]
    rw [cyclicPermutationCoinducedCohomologyIso_hom]
    rw [← groupCohomology.map_id_comp,
      cyclicPermutationCoinducedIso_hom_comp_corestrictionCounit]
  have hShapiro :=
    schreierCoindShapiroIso_inv_comp_corestrictionCounit
      chi.ker A T n
  rw [schreierCyclicPermutationShapiroIso_inv,
    Category.assoc, hCoeff]
  exact hShapiro

set_option backward.isDefEq.respectTransparency false in
/-- Let `G` be a group, `k` a commutative ring, `ℓ : ℕ` nonzero, `χ : G → Multiplicative (ZMod ℓ)`
surjective, `A : Rep k G`, `T` a right transversal for `J=ker χ`, and `n : ℕ`. With
`d_χ=Rep.cyclicPermutationDiagonal ℓ χ A`, `map (id G) d_χ n ≫
(schreierCyclicPermutationShapiroIso ℓ χ hχ A T n).hom = map J.subtype (𝟙 (Res_J A)) n`. The
coefficient diagonal is `a ↦ (i ↦ a)`. -/
theorem map_diagonal_comp_schreierCyclicPermutationShapiroIso_hom
    (ell : ℕ) [NeZero ell]
    (chi : G →* Multiplicative (ZMod ell))
    (hchi : Function.Surjective chi) (A : Rep.{u} k G)
    (T : chi.ker.RightTransversal) (n : ℕ) :
    groupCohomology.map (MonoidHom.id G)
        (Rep.cyclicPermutationDiagonal ell chi A) n ≫
      (schreierCyclicPermutationShapiroIso
        ell chi hchi A T n).hom =
      groupCohomology.map chi.ker.subtype
        (𝟙 (Rep.res chi.ker.subtype A)) n := by
  let _ : Finite (G ⧸ chi.ker) :=
    Finite.of_equiv (Multiplicative (ZMod ell))
      (QuotientGroup.quotientKerEquivOfSurjective chi hchi).symm
  let _ : chi.ker.FiniteIndex :=
    Subgroup.finiteIndex_of_finite_quotient
  rw [schreierCyclicPermutationShapiroIso_hom,
    cyclicPermutationCoinducedCohomologyIso_hom,
    ← Category.assoc, ← groupCohomology.map_id_comp]
  have hCoeff := Rep.cyclicPermutationDiagonal_comp_coinducedIso
    ell chi hchi A
  have hMap :
      groupCohomology.map (MonoidHom.id G)
          (Rep.cyclicPermutationDiagonal ell chi A ≫
            (Rep.cyclicPermutationCoinducedIso ell chi hchi A).hom) n =
        groupCohomology.map (MonoidHom.id G)
          ((Rep.resCoindAdjunction k chi.ker.subtype).unit.app A) n := by
    apply groupCohomology.map_congr rfl
    exact congrArg (fun f => f.hom.toLinearMap) hCoeff
  rw [hMap]
  exact map_unit_comp_schreierCoindShapiroIso_hom
    chi.ker A T n

set_option backward.isDefEq.respectTransparency false in
/-- Let `G` be a group, `k` a commutative ring, `ℓ : ℕ` nonzero, `χ : G → Multiplicative (ZMod ℓ)`
surjective, `A : Rep k G`, `T` a right transversal for `J=ker χ`, and `n : ℕ`. Then
`(schreierCyclicPermutationShapiroIso ℓ χ hχ A T n).hom ≫ schreierCorestriction J A n = map
(id G) (Rep.cyclicPermutationAugmentation ℓ χ A) n`, as maps `H^n(G,P_χ(A)) → H^n(G,A)`; the
coefficient augmentation is `p ↦ ∑ i : ZMod ℓ, p(i)`. -/
theorem schreierCyclicPermutationShapiroIso_hom_comp_schreierCorestriction
    (ell : ℕ) [NeZero ell]
    (chi : G →* Multiplicative (ZMod ell))
    (hchi : Function.Surjective chi) (A : Rep.{u} k G)
    (T : chi.ker.RightTransversal) (n : ℕ) :
    (schreierCyclicPermutationShapiroIso ell chi hchi A T n).hom ≫
      schreierCorestriction chi.ker A n =
        groupCohomology.map (MonoidHom.id G)
          (Rep.cyclicPermutationAugmentation ell chi A) n := by
  let _ : Finite (G ⧸ chi.ker) :=
    Finite.of_equiv (Multiplicative (ZMod ell))
      (QuotientGroup.quotientKerEquivOfSurjective chi hchi).symm
  let _ : chi.ker.FiniteIndex :=
    Subgroup.finiteIndex_of_finite_quotient
  have hCanonical :
      (schreierCyclicPermutationShapiroIso ell chi hchi A T n).inv ≫
          groupCohomology.map (MonoidHom.id G)
            (Rep.cyclicPermutationAugmentation ell chi A) n =
        schreierCorestriction chi.ker A n :=
    (schreierCyclicPermutationShapiroIso_inv_comp_augmentation
      ell chi hchi A T n).trans
      (schreierCorestriction_eq_of_rightTransversal chi.ker A T n).symm
  rw [← hCanonical]
  rw [← Category.assoc, Iso.hom_inv_id, Category.id_comp]

end groupCohomology
