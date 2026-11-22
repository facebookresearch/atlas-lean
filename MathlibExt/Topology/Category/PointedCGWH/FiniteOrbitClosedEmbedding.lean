/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Topology.Category.PointedCGWH.Basic
public import MathlibExt.Topology.Category.CGWH.Reflection
public import Mathlib.CategoryTheory.Action.Basic
public import Mathlib.Topology.Algebra.ConstMulAction

/-!
# Finite coinvariants preserve pointed closed embeddings

Finite group orbits use Mathlib's `MulAction.orbitRel` and its ordinary quotient
topology. The orbit relation is closed in the native compactly generated square
because it is a finite union of graphs, tested on compact Hausdorff probes.
Thus its ordinary quotient is already weak Hausdorff. Finite saturation proves
that the quotient projection is closed, and equivariance preserves injectivity
on orbit classes.

This formalizes the finite coinvariant closure used in Pavlov–Scholbach,
*Homotopy theory of symmetric powers*, arXiv:1510.04969, §7.5,
and *Symmetric operads in abstract symmetric spectra*,
arXiv:1410.5699, Appendix 9.3. The compact-probe graph argument adapts the
native diagonal proof `CompactlyGenerated.uWeakHausdorffSpace_iff_isClosed_nativeDiagonal`
in `CGWH.Reflection` (by @toskua, Avocado), and uses its existing
`CGWH.quotient_isWeakHausdorff_iff_isClosed` criterion.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section

universe u v w wX wY

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Topology

namespace Topology

variable {G : Type w} [Group G]
variable {X : Type wX} {Y : Type wY} [TopologicalSpace X] [TopologicalSpace Y]
variable [MulAction G X] [MulAction G Y]

/-- An equivariant map induces the map of the existing orbit quotients. -/
def orbitQuotientMap (f : X → Y) (heq : ∀ (g : G) (x : X), f (g • x) = g • f x) :
    Quotient (MulAction.orbitRel G X) → Quotient (MulAction.orbitRel G Y) :=
  Quotient.map' f (by
    intro x y hxy
    obtain ⟨g, hg⟩ := MulAction.mem_orbit_iff.mp hxy
    exact MulAction.mem_orbit_iff.mpr ⟨g, (heq g y).symm.trans (congrArg f hg)⟩)

/-- Finite saturation makes the ordinary orbit projection a closed map. -/
theorem isClosedMap_orbitProjection_of_finite [Finite G] [ContinuousConstSMul G X] :
    IsClosedMap (@Quotient.mk' X (MulAction.orbitRel G X)) := by
  intro S hS
  apply isQuotientMap_quotient_mk'.isCoinducing.isClosed_preimage.mp
  rw [MulAction.quotient_preimage_image_eq_union_mul S]
  exact isClosed_iUnion_of_finite fun g => isClosedMap_smul g S hS

/-- Finite orbit quotients preserve equivariant closed embeddings.
No separation property of either space is needed. -/
theorem isClosedEmbedding_orbitQuotientMap_of_finite [Finite G]
    [ContinuousConstSMul G Y] (f : X → Y)
    (heq : ∀ (g : G) (x : X), f (g • x) = g • f x) (hf : IsClosedEmbedding f) :
    IsClosedEmbedding (orbitQuotientMap f heq) := by
  apply IsClosedEmbedding.of_continuous_injective_isClosedMap
  · exact hf.continuous.quotient_map' _
  · intro q r h
    induction q using Quotient.inductionOn with
    | h x =>
      induction r using Quotient.inductionOn with
      | h y =>
        change (@Quotient.mk' Y (MulAction.orbitRel G Y)) (f x) =
          (@Quotient.mk' Y (MulAction.orbitRel G Y)) (f y) at h
        apply Quotient.sound
        obtain ⟨g, hg⟩ := MulAction.mem_orbit_iff.mp (Quotient.exact h)
        exact MulAction.mem_orbit_iff.mpr ⟨g, hf.injective ((heq g y).trans hg)⟩
  · intro S hS
    have hpre : IsClosed ((@Quotient.mk' X (MulAction.orbitRel G X)) ⁻¹' S) :=
      hS.preimage continuous_quotient_mk'
    have hi : orbitQuotientMap f heq '' S =
        (@Quotient.mk' Y (MulAction.orbitRel G Y)) ''
          (f '' ((@Quotient.mk' X (MulAction.orbitRel G X)) ⁻¹' S)) := by
      calc
        _ = orbitQuotientMap f heq ''
            ((@Quotient.mk' X (MulAction.orbitRel G X)) ''
              ((@Quotient.mk' X (MulAction.orbitRel G X)) ⁻¹' S)) := by
          exact congrArg (Set.image (orbitQuotientMap f heq))
            (Set.image_preimage_eq S
              (@Quotient.mk'_surjective X (MulAction.orbitRel G X))).symm
        _ = _ := by
          rw [Set.image_image, Set.image_image]
          rfl
    rw [hi]
    exact isClosedMap_orbitProjection_of_finite _ (hf.isClosedMap _ hpre)

end Topology

namespace CGWH

/-- A finite group action has closed orbit relation in the native square.
This is a compact-probe equalizer argument, so weak Hausdorff spaces suffice. -/
theorem closedOrbitRelation_of_finite (G : Type w) [Group G] [Finite G]
    (X : CGWH.{u, v}) [MulAction G X] [ContinuousConstSMul G X] :
    closedEquivalenceRelation (cgwhToCompactlyGenerated.obj X) (MulAction.orbitRel G X) := by
  let C := cgwhToCompactlyGenerated.obj X
  let _ : UCompactlyGeneratedSpace.{u} ↥((C ⊗ C).toTop) :=
    (C ⊗ C).is_compactly_generated
  unfold closedEquivalenceRelation
  apply UCompactlyGeneratedSpace.isClosed
  intro K a
  let f : C(K, X) :=
    (ConcreteCategory.hom (CartesianMonoidalCategory.fst C C)).comp a
  let h : C(K, X) :=
    (ConcreteCategory.hom (CartesianMonoidalCategory.snd C C)).comp a
  have hi : {k : K | MulAction.orbitRel G X (f k) (h k)} =
      ⋃ g : G, {k : K | g • h k = f k} := by
    ext k
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion]
    exact MulAction.mem_orbit_iff
  change IsClosed {k : K | MulAction.orbitRel G X (f k) (h k)}
  rw [hi]
  exact isClosed_iUnion_of_finite fun g =>
    (uWeakHausdorffSpace_iff_isClosed_equalizer.mp (inferInstance :
      UWeakHausdorffSpace.{u} X)) K
        ⟨fun k => g • h k, h.continuous.const_smul g⟩ f

end CGWH

namespace PointedCGWH

variable {G : Type w} [Group G]

/-- The underlying action is the one specified by the pointed categorical action. -/
@[instance_reducible] def actionCarrierMulAction (A : Action PointedCGWH.{u, v} G) : MulAction G A.V.right where
  smul g x := (A.ρ g).asHom.right x
  one_smul x := by
    change (A.ρ 1).asHom.right x = x
    rw [A.ρ.map_one]
    rfl
  mul_smul g h x := by
    change (A.ρ (g * h)).asHom.right x =
      (A.ρ g).asHom.right ((A.ρ h).asHom.right x)
    rw [A.ρ.map_mul]
    rfl

/-- The orbit relation uses the original categorical action on the coefficient carrier. -/
def actionOrbitRel (A : Action PointedCGWH.{u, v} G) : Setoid A.V.right :=
  @MulAction.orbitRel G A.V.right _ (actionCarrierMulAction A)

/-- A categorical action of a finite group produces the needed closed relation. -/
theorem actionOrbitRel_closed [Finite G] (A : Action PointedCGWH.{u, v} G) :
    CGWH.closedEquivalenceRelation (CGWH.cgwhToCompactlyGenerated.obj A.V.right)
      (actionOrbitRel A) := by
  let _ := actionCarrierMulAction A
  let _ : ContinuousConstSMul G A.V.right :=
    ⟨fun g => (ConcreteCategory.hom (A.ρ g).asHom.right).continuous⟩
  exact CGWH.closedOrbitRelation_of_finite G A.V.right

/-- The same ordinary orbit quotient is a native CGWH object for finite groups. -/
def finiteOrbitCGWH [Finite G] (A : Action PointedCGWH.{u, v} G) : CGWH.{u, v} := by
  letI : UWeakHausdorffSpace.{u} (Quotient (actionOrbitRel A)) :=
    (CGWH.quotient_isWeakHausdorff_iff_isClosed
      (CGWH.cgwhToCompactlyGenerated.obj A.V.right) (actionOrbitRel A)).mpr
        (actionOrbitRel_closed A)
  exact CGWH.of (Quotient (actionOrbitRel A))

/-- The literal orbit quotient projection, with its ordinary quotienttopology. -/
def finiteOrbitCGWHProjection [Finite G] (A : Action PointedCGWH.{u, v} G) :
    A.V.right ⟶ finiteOrbitCGWH A :=
  ConcreteCategory.ofHom ⟨@Quotient.mk' A.V.right (actionOrbitRel A),
    continuous_quotient_mk'⟩

/-- The original basepoint descends by the literal orbit quotient projection. -/
def finiteOrbit [Finite G] (A : Action PointedCGWH.{u, v} G) : PointedCGWH.{u, v} :=
  Under.mk (A.V.hom ≫ finiteOrbitCGWHProjection A)

/-- The actual pointed orbit projection. -/
def finiteOrbitProjection [Finite G] (A : Action PointedCGWH.{u, v} G) :
    A.V ⟶ finiteOrbit A :=
  Under.homMk (finiteOrbitCGWHProjection A)

/-- The original action supplies the usual orbit witnesses. -/
theorem actionOrbitRel_iff (A : Action PointedCGWH.{u, v} G) (x y : A.V.right) :
    actionOrbitRel A x y ↔ ∃ g : G, (A.ρ g).asHom.right y = x := by
  let _ := actionCarrierMulAction A
  exact MulAction.mem_orbit_iff

/-- Finite categorical actions produce a homeomorphic comparison to the native
weak-Hausdorff-reflected quotient. -/
theorem finiteOrbitComparison_isHomeomorph [Finite G]
    (A : Action PointedCGWH.{u, v} G) :
    IsHomeomorph (CGWH.quotientComparisonFromTop A.V.right (actionOrbitRel A)) :=
  (CGWH.quotientComparisonFromTop_isHomeomorph_iff A.V.right (actionOrbitRel A)).mpr
    (actionOrbitRel_closed A)

/-- The literal `SingleObj` diagram of the original pointed action. -/
abbrev actionDiagram (A : Action PointedCGWH.{u, v} G) :
    SingleObj G ⥤ PointedCGWH.{u, v} :=
  (Action.functorCategoryEquivalence PointedCGWH.{u, v} G).functor.obj A

variable [Finite G]

/-- The actual quotient projection coequalizes each original action arrow. -/
@[reassoc (attr := simp)]
theorem finiteOrbitProjection_action (A : Action PointedCGWH.{u, v} G) (g : G) :
    (A.ρ g).asHom ≫ finiteOrbitProjection A = finiteOrbitProjection A := by
  ext x
  change (@Quotient.mk' A.V.right (actionOrbitRel A)) ((A.ρ g).asHom.right x) =
    (@Quotient.mk' A.V.right (actionOrbitRel A)) x
  exact Quotient.sound ((actionOrbitRel_iff A _ _).mpr ⟨g, rfl⟩)

/-- The pointed orbit quotient is a cocone over the literal original action diagram. -/
def finiteOrbitCocone (A : Action PointedCGWH.{u, v} G) : Cocone (actionDiagram A) where
  pt := finiteOrbit A
  ι :=
    { app := fun _ => finiteOrbitProjection A
      naturality := by
        intro i j g
        change (A.ρ g).asHom ≫ finiteOrbitProjection A = finiteOrbitProjection A ≫ 𝟙 _
        rw [Category.comp_id, finiteOrbitProjection_action] }

/-- The literal finite quotient cocone has its complete native universal property. -/
def finiteOrbitCoconeIsColimit (A : Action PointedCGWH.{u, v} G) :
    IsColimit (finiteOrbitCocone A) := by
  let respects : ∀ s : Cocone (actionDiagram A),
      ∀ x y, actionOrbitRel A x y →
        (s.ι.app (SingleObj.star G)).right x = (s.ι.app (SingleObj.star G)).right y :=
    fun s x y hxy => by
      obtain ⟨g, rfl⟩ := (actionOrbitRel_iff A x y).mp hxy
      exact ConcreteCategory.congr_hom (C := CGWH.{u, v})
        (congrArg (fun f => f.right) (s.w (show SingleObj.star G ⟶ SingleObj.star G from g))) y
  let desc : ∀ s : Cocone (actionDiagram A), finiteOrbit A ⟶ s.pt := fun s => by
    let d : finiteOrbitCGWH A ⟶ s.pt.right :=
      ConcreteCategory.ofHom
        ⟨Quotient.lift (fun x => (s.ι.app (SingleObj.star G)).right x) (respects s),
          (ConcreteCategory.hom (s.ι.app (SingleObj.star G)).right).continuous.quotient_lift
            (respects s)⟩
    refine Under.homMk d ?_
    have hfac : finiteOrbitCGWHProjection A ≫ d = (s.ι.app (SingleObj.star G)).right := by
      ext x
      rfl
    change (A.V.hom ≫ finiteOrbitCGWHProjection A) ≫ d = s.pt.hom
    rw [Category.assoc, hfac]
    exact (s.ι.app (SingleObj.star G)).w
  refine { desc := desc, fac := ?_, uniq := ?_ }
  · intro s j
    cases j
    ext x
    rfl
  · intro s m hm
    ext q
    refine Quotient.inductionOn q fun x => ?_
    exact ConcreteCategory.congr_hom (C := CGWH.{u, v})
      (congrArg (fun f => f.right) (hm (SingleObj.star G))) x

omit [Finite G] in
/-- The original pointed equivariant morphism is equivariant on its underlying carrier. -/
theorem actionMap_equivariant {A B : Action PointedCGWH.{u, v} G} (f : A ⟶ B)
    (g : G) (x : A.V.right) :
    f.hom.right ((A.ρ g).asHom.right x) = (B.ρ g).asHom.right (f.hom.right x) :=
  ConcreteCategory.congr_hom (C := CGWH.{u, v})
    (congrArg (fun h => h.right) (f.comm g)) x

/-- The actual quotient map of the original pointed equivariant morphism. -/
def finiteOrbitMap {A B : Action PointedCGWH.{u, v} G} (f : A ⟶ B) :
    finiteOrbit A ⟶ finiteOrbit B := by
  let _ := actionCarrierMulAction A
  let _ := actionCarrierMulAction B
  let d : finiteOrbitCGWH A ⟶ finiteOrbitCGWH B :=
    ConcreteCategory.ofHom
      ⟨Topology.orbitQuotientMap (fun x => f.hom.right x) (actionMap_equivariant f),
        (ConcreteCategory.hom f.hom.right).continuous.quotient_map' _⟩
  refine Under.homMk d ?_
  have hfac : finiteOrbitCGWHProjection A ≫ d = f.hom.right ≫ finiteOrbitCGWHProjection B := by
    ext x
    rfl
  change (A.V.hom ≫ finiteOrbitCGWHProjection A) ≫ d = B.V.hom ≫ finiteOrbitCGWHProjection B
  rw [Category.assoc, hfac, ← Category.assoc, f.hom.w]

/-- The actual induced quotient map retains the original source and target projections. -/
@[reassoc (attr := simp)]
theorem finiteOrbitMap_projection {A B : Action PointedCGWH.{u, v} G} (f : A ⟶ B) :
    finiteOrbitProjection A ≫ finiteOrbitMap f = f.hom ≫ finiteOrbitProjection B := by
  ext x
  rfl

/-- Finite categorical coinvariants preserve the underlying closed embedding. -/
theorem isClosedEmbedding_finiteOrbitMap {A B : Action PointedCGWH.{u, v} G} (f : A ⟶ B)
    (hf : IsClosedEmbedding (ConcreteCategory.hom f.hom.right)) :
    IsClosedEmbedding (ConcreteCategory.hom (finiteOrbitMap f).right) := by
  let _ := actionCarrierMulAction A
  let _ := actionCarrierMulAction B
  let _ : ContinuousConstSMul G B.V.right :=
    ⟨fun g => (ConcreteCategory.hom (B.ρ g).asHom.right).continuous⟩
  exact Topology.isClosedEmbedding_orbitQuotientMap_of_finite
    (fun x => f.hom.right x) (actionMap_equivariant f) hf

/-- Any two original orbit cocones retain their induced morphism square,
and that morphism is a closed embedding when the original equivariant map is. -/
theorem isClosedEmbedding_orbitCoconeMap
    {A B : Action PointedCGWH.{u, v} G} (f : A ⟶ B)
    (cA : Cocone (actionDiagram A)) (cB : Cocone (actionDiagram B))
    (hA : IsColimit cA) (hB : IsColimit cB)
    (m : cA.pt ⟶ cB.pt)
    (hm : ∀ j, cA.ι.app j ≫ m = f.hom ≫ cB.ι.app j)
    (hf : IsClosedEmbedding (ConcreteCategory.hom f.hom.right)) :
    IsClosedEmbedding (ConcreteCategory.hom m.right) := by
  let eA : finiteOrbit A ≅ cA.pt :=
    (finiteOrbitCoconeIsColimit A).coconePointUniqueUpToIso hA
  let eB : finiteOrbit B ≅ cB.pt :=
    (finiteOrbitCoconeIsColimit B).coconePointUniqueUpToIso hB
  have hComm : eA.hom ≫ m = finiteOrbitMap f ≫ eB.hom := by
    apply (finiteOrbitCoconeIsColimit A).hom_ext
    intro j
    let a : A.V ⟶ cA.pt := cA.ι.app j
    let b : B.V ⟶ cB.pt := cB.ι.app j
    have heA : finiteOrbitProjection A ≫ eA.hom = a :=
      (finiteOrbitCoconeIsColimit A).comp_coconePointUniqueUpToIso_hom hA j
    have heB : finiteOrbitProjection B ≫ eB.hom = b :=
      (finiteOrbitCoconeIsColimit B).comp_coconePointUniqueUpToIso_hom hB j
    have hmj : a ≫ m = f.hom ≫ b := hm j
    change finiteOrbitProjection A ≫ (eA.hom ≫ m) =
      finiteOrbitProjection A ≫ (finiteOrbitMap f ≫ eB.hom)
    rw [← Category.assoc, heA, hmj, ← Category.assoc,
      finiteOrbitMap_projection, Category.assoc, heB]
  have hEq : m = eA.inv ≫ finiteOrbitMap f ≫ eB.hom := by
    calc
      m = eA.inv ≫ (eA.hom ≫ m) := by simp
      _ = eA.inv ≫ (finiteOrbitMap f ≫ eB.hom) := congrArg (fun t => eA.inv ≫ t) hComm
      _ = _ := (Category.assoc _ _ _).symm
  rw [hEq]
  have heA : IsClosedEmbedding (ConcreteCategory.hom eA.inv.right) :=
    (CGWH.homeoOfIso (pointedToCGWH.mapIso eA.symm)).isClosedEmbedding
  have heB : IsClosedEmbedding (ConcreteCategory.hom eB.hom.right) :=
    (CGWH.homeoOfIso (pointedToCGWH.mapIso eB)).isClosedEmbedding
  exact heB.comp ((isClosedEmbedding_finiteOrbitMap f hf).comp heA)

/-- Finite coinvariant descent between the actual original colimit cocones
preserves the closed embedding of the original equivariant morphism. -/
theorem isClosedEmbedding_isColimitMap
    {A B : Action PointedCGWH.{u, v} G} (f : A ⟶ B)
    (cA : Cocone (actionDiagram A)) (cB : Cocone (actionDiagram B))
    (hA : IsColimit cA) (hB : IsColimit cB)
    (hf : IsClosedEmbedding (ConcreteCategory.hom f.hom.right)) :
    IsClosedEmbedding (ConcreteCategory.hom
      (hA.map cB ((Action.functorCategoryEquivalence PointedCGWH.{u, v} G).functor.map f)).right) := by
  apply isClosedEmbedding_orbitCoconeMap f cA cB hA hB _ _ hf
  intro j
  exact hA.fac
    ((Cocone.precompose
      ((Action.functorCategoryEquivalence PointedCGWH.{u, v} G).functor.map f)).obj cB) j

/-- The literal finite action diagram has a native colimit at the original
coefficient universes, even if the group is presented in a larger universe. -/
theorem finiteOrbit_hasColimit (A : Action PointedCGWH.{u, v} G) :
    HasColimit (actionDiagram A) :=
  ⟨⟨finiteOrbitCocone A, finiteOrbitCoconeIsColimit A⟩⟩

/-- Mathlib's actual selected map of finite action colimits preserves closed embeddings. -/
theorem isClosedEmbedding_actionColimMap
    {A B : Action PointedCGWH.{u, v} G} (f : A ⟶ B)
    [HasColimit (actionDiagram A)] [HasColimit (actionDiagram B)]
    (hf : IsClosedEmbedding (ConcreteCategory.hom f.hom.right)) :
    IsClosedEmbedding (ConcreteCategory.hom
      (colimMap ((Action.functorCategoryEquivalence PointedCGWH.{u, v} G).functor.map f)).right) :=
  isClosedEmbedding_isColimitMap f
    (colimit.cocone (actionDiagram A)) (colimit.cocone (actionDiagram B))
    (colimit.isColimit (actionDiagram A)) (colimit.isColimit (actionDiagram B)) hf

end PointedCGWH
