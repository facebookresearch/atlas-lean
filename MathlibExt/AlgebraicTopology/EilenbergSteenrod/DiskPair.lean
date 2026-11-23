/-
Copyright (c) 2026 Avocado. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-
Modified for Atlas library integration. Standalone author labels were removed;
source attributions are retained in NOTICE.
-/
module

public import MathlibExt.AlgebraicTopology.EilenbergSteenrod.Contractible
public import MathlibExt.AlgebraicTopology.EilenbergSteenrod.PairSequenceExact
public import MathlibExt.Topology.Category.TopPair.ClosedBall.Topology

/-!
# Disk-pair boundary isomorphisms for ordinary homology theories

General homotopy-invariant boundary transport for closed-ball pairs induced by
continuous linear equivalences between unit spheres, and the exact pair
sequence which identifies the positive-degree relative homology of a
contractible ambient space with the homology of its subspace.  Applied to the
classical disk pair, this gives the boundary-sphere isomorphism.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe w u v x

namespace TopPair.HomologyPretheory

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C]
variable {ι : Type*} {c : ComplexShape ι}

/-- Homotopy-invariant transport between the homology of unit-sphere boundaries
of closed-ball pairs induced by a continuous linear equivalence. -/
noncomputable def closedBallPairUnitSphereIso
    (E : HomologyPretheory.{max w x} C c) [E.IsHomotopyInvariant]
    {V W : Type x}
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    (e : V ≃L[ℝ] W) (i : ι) :
    (E.H i).obj (closedBallPair.{w} (0 : V) 1).snd ≅
      (E.H i).obj (closedBallPair.{w} (0 : W) 1).snd :=
  E.absoluteIsoOfHomotopyEquiv (closedBallPairUnitSphereHomeomorph e).toHomotopyEquiv i

/-- Transport along the identity linear equivalence is the identity. -/
@[simp] theorem closedBallPairUnitSphereIso_refl
    (E : HomologyPretheory.{max w x} C c) [E.IsHomotopyInvariant]
    (V : Type x) [NormedAddCommGroup V] [NormedSpace ℝ V] (i : ι) :
    closedBallPairUnitSphereIso E (ContinuousLinearEquiv.refl ℝ V) i =
      Iso.refl ((E.H i).obj (closedBallPair.{w} (0 : V) 1).snd) := by
  unfold closedBallPairUnitSphereIso
  rw [closedBallPairUnitSphereHomeomorph_refl]
  rw [Homeomorph.refl_toHomotopyEquiv]
  rw [absoluteIsoOfHomotopyEquiv_refl]

/-- Transport along a composite is the composite of transports. -/
@[simp] theorem closedBallPairUnitSphereIso_trans
    (E : HomologyPretheory.{max w x} C c) [E.IsHomotopyInvariant]
    {V W Z : Type x}
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    (e : V ≃L[ℝ] W) (f : W ≃L[ℝ] Z) (i : ι) :
    closedBallPairUnitSphereIso E (e.trans f) i =
      (closedBallPairUnitSphereIso E e i).trans
        (closedBallPairUnitSphereIso E f i) := by
  unfold closedBallPairUnitSphereIso
  rw [closedBallPairUnitSphereHomeomorph_trans]
  rw [Homeomorph.trans_toHomotopyEquiv]
  rw [absoluteIsoOfHomotopyEquiv_trans]

/-- Transport along the inverse is the inverse iso. -/
@[simp] theorem closedBallPairUnitSphereIso_symm
    (E : HomologyPretheory.{max w x} C c) [E.IsHomotopyInvariant]
    {V W : Type x}
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    (e : V ≃L[ℝ] W) (i : ι) :
    closedBallPairUnitSphereIso E e.symm i =
      (closedBallPairUnitSphereIso E e i).symm := by
  unfold closedBallPairUnitSphereIso
  rw [← closedBallPairUnitSphereHomeomorph_symm]
  rw [Homeomorph.symm_toHomotopyEquiv]
  rw [absoluteIsoOfHomotopyEquiv_symm]

/-- Naturality of the boundary transport in morphisms of homology pretheories. -/
theorem closedBallPairUnitSphereIso_hom_naturality
    {E F : HomologyPretheory.{max w x} C c}
    [E.IsHomotopyInvariant] [F.IsHomotopyInvariant]
    (α : E ⟶ F) {V W : Type x}
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    (e : V ≃L[ℝ] W) (i : ι) :
    (α.hom i).app (closedBallPair.{w} (0 : V) 1).snd ≫
        (closedBallPairUnitSphereIso F e i).hom =
      (closedBallPairUnitSphereIso E e i).hom ≫
        (α.hom i).app (closedBallPair.{w} (0 : W) 1).snd := by
  unfold closedBallPairUnitSphereIso
  exact absoluteIsoOfHomotopyEquiv_hom_naturality α
    (closedBallPairUnitSphereHomeomorph e).toHomotopyEquiv i

end TopPair.HomologyPretheory

namespace TopPair.GeneralizedHomologyTheory

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C]

/-- Theory-natural absolute homology transport from the boundary of the
classical `(m + 1)`-cell to the standard `m`-sphere. -/
noncomputable def classicalCellBoundarySphereNatIso (m : ℕ) (n : ℤ) :
    hFunctor (C := C) n ⋙
        (evaluation TopCat.{w} C).obj
          (Topology.CWComplex.classicalCellDiskPair.{w} (m + 1)).snd ≅
      hFunctor (C := C) n ⋙
        (evaluation TopCat.{w} C).obj (TopCat.sphere.{w} m) :=
  NatIso.ofComponents
    (fun E => E.obj.closedBallPairUnitSphereIso
      (EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm n)
    (fun {_ _} α => TopPair.HomologyPretheory.closedBallPairUnitSphereIso_hom_naturality α.hom
      (EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm n)

@[simp] theorem classicalCellBoundarySphereNatIso_app
    (m : ℕ) (n : ℤ) (E : GeneralizedHomologyTheory.{u, v, w} C) :
    (classicalCellBoundarySphereNatIso (C := C) m n).app E =
      E.obj.closedBallPairUnitSphereIso
        (EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm n :=
  rfl

end TopPair.GeneralizedHomologyTheory

namespace TopPair.HomologyTheoryData.IsExact

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- Exactness identifies relative homology with boundary homology when the two
adjacent ambient groups vanish. -/
noncomputable def relativeBoundaryIsoOfIsZeroAmbient
    (E : HomologyTheoryData.{w} C) [E.IsExact]
    (n : ℤ) (P : TopPair.{w})
    (hAmbient : IsZero ((E.H n).obj P.fst))
    (hAmbientPrev : IsZero ((E.H (n - 1)).obj P.fst)) :
    (E.Hₚ n).obj P ≅ (E.H (n - 1)).obj P.snd := by
  have hToRelative : E.toRelative n P = 0 :=
    hAmbient.eq_of_src _ _
  have hSubspace : E.subspaceMap (n - 1) P = 0 :=
    hAmbientPrev.eq_of_tgt _ _
  let S₁ := ShortComplex.mk
    (E.toRelative n P)
    (E.boundary n P)
    (toRelative_comp_boundary E n P)
  let S₂ := ShortComplex.mk
    (E.boundary n P)
    (E.subspaceMap (n - 1) P)
    (boundary_comp_subspaceMap E n P)
  have hS₁f : S₁.f = 0 := hToRelative
  have hS₂g : S₂.g = 0 := hSubspace
  have hMono : Mono S₁.g :=
    (ShortComplex.exact_iff_mono S₁ hS₁f).mp
      (exact_toRelative_boundary E n P)
  have hEpi : Epi S₂.f :=
    (ShortComplex.exact_iff_epi S₂ hS₂g).mp
      (exact_boundary_subspaceMap E n P)
  letI : Mono S₁.g := hMono
  letI : Epi S₁.g := by
    change Epi (E.boundary n P)
    change Epi S₂.f at hEpi
    exact hEpi
  letI : IsIso S₁.g := isIso_of_mono_of_epi S₁.g
  exact @asIso C _ S₁.X₂ S₁.X₃ S₁.g _

@[simp]
theorem relativeBoundaryIsoOfIsZeroAmbient_hom
    (E : HomologyTheoryData.{w} C) [E.IsExact]
    (n : ℤ) (P : TopPair.{w})
    (hAmbient : IsZero ((E.H n).obj P.fst))
    (hAmbientPrev : IsZero ((E.H (n - 1)).obj P.fst)) :
    (relativeBoundaryIsoOfIsZeroAmbient E n P hAmbient hAmbientPrev).hom =
      E.boundary n P := by
  rfl

theorem relativeBoundaryIsoOfIsZeroAmbient_hom_naturality_theory
    {E F : HomologyTheoryData.{w} C} [E.IsExact] [F.IsExact]
    (φ : E ⟶ F) (n : ℤ) (P : TopPair.{w})
    (hE : IsZero ((E.H n).obj P.fst))
    (hEPrev : IsZero ((E.H (n - 1)).obj P.fst))
    (hF : IsZero ((F.H n).obj P.fst))
    (hFPrev : IsZero ((F.H (n - 1)).obj P.fst)) :
    (φ.homₚ n).app P ≫
        (relativeBoundaryIsoOfIsZeroAmbient F n P hF hFPrev).hom =
      (relativeBoundaryIsoOfIsZeroAmbient E n P hE hEPrev).hom ≫
        (φ.hom (n - 1)).app P.snd := by
  rw [relativeBoundaryIsoOfIsZeroAmbient_hom]
  rw [relativeBoundaryIsoOfIsZeroAmbient_hom]
  exact (φ.w_app n (n - 1) P).symm

end TopPair.HomologyTheoryData.IsExact

namespace TopPair.OrdinaryHomologyTheory

variable {C : Type u} [Category.{v} C] [Abelian C]

open TopPair.HomologyTheoryData.IsExact

/-- Theory-natural boundary comparison for a pair with contractible ambient
space in degrees where both adjacent ambient groups vanish. -/
noncomputable def relativeBoundaryNatIsoOfContractibleAmbient
    (P : TopPair.{w}) [ContractibleSpace ↥P.fst]
    (n : ℤ) (hn : n ≠ 0) (hnPrev : n - 1 ≠ 0) :
    hₚFunctor (C := C) n ⋙
        (evaluation TopPair.{w} C).obj P ≅
      hFunctor (C := C) (n - 1) ⋙
        (evaluation TopCat.{w} C).obj P.snd :=
  NatIso.ofComponents
    (fun E =>
      relativeBoundaryIsoOfIsZeroAmbient E.obj n P
        (by
          change IsZero ((E.H n).obj P.fst)
          exact E.isZero_of_contractible n hn ↥P.fst)
        (by
          change IsZero ((E.H (n - 1)).obj P.fst)
          exact E.isZero_of_contractible (n - 1) hnPrev ↥P.fst))
    (fun {E F} φ =>
      relativeBoundaryIsoOfIsZeroAmbient_hom_naturality_theory
        φ.hom n P
        (by
          change IsZero ((E.H n).obj P.fst)
          exact E.isZero_of_contractible n hn ↥P.fst)
        (by
          change IsZero ((E.H (n - 1)).obj P.fst)
          exact E.isZero_of_contractible (n - 1) hnPrev ↥P.fst)
        (by
          change IsZero ((F.H n).obj P.fst)
          exact F.isZero_of_contractible n hn ↥P.fst)
        (by
          change IsZero ((F.H (n - 1)).obj P.fst)
          exact F.isZero_of_contractible (n - 1) hnPrev ↥P.fst))

@[simp]
theorem relativeBoundaryNatIsoOfContractibleAmbient_app
    (P : TopPair.{w}) [ContractibleSpace ↥P.fst]
    (n : ℤ) (hn : n ≠ 0) (hnPrev : n - 1 ≠ 0)
    (E : OrdinaryHomologyTheory.{u, v, w} C) :
    (relativeBoundaryNatIsoOfContractibleAmbient
      (C := C) P n hn hnPrev).app E =
      relativeBoundaryIsoOfIsZeroAmbient E.obj n P
        (by
          change IsZero ((E.H n).obj P.fst)
          exact E.isZero_of_contractible n hn ↥P.fst)
        (by
          change IsZero ((E.H (n - 1)).obj P.fst)
          exact E.isZero_of_contractible (n - 1) hnPrev ↥P.fst) :=
  rfl

private noncomputable def relativeBoundaryIsoOfContractibleAmbient
    (E : OrdinaryHomologyTheory.{u, v, w} C)
    (P : TopPair.{w}) [ContractibleSpace ↥P.fst]
    (n : ℕ) (hn : n ≠ 0) :
    (E.Hₚ ((n + 1 : ℕ) : ℤ)).obj P ≅ (E.H (n : ℤ)).obj P.snd := by
  have hAmbientSucc : IsZero ((E.H ((n + 1 : ℕ) : ℤ)).obj P.fst) :=
    E.isZero_of_contractible ((n + 1 : ℕ) : ℤ) (by omega) ↥P.fst
  have hAmbient : IsZero ((E.H (n : ℤ)).obj P.fst) :=
    E.isZero_of_contractible (n : ℤ)
      (by simpa using (show (n : ℤ) ≠ 0 by exact_mod_cast hn)) ↥P.fst
  have hToRelative : E.obj.toRelative ((n + 1 : ℕ) : ℤ) P = 0 :=
    hAmbientSucc.eq_of_src _ _
  have hSubspace : E.obj.subspaceMap (n : ℤ) P = 0 :=
    hAmbient.eq_of_tgt _ _
  let S₁ := ShortComplex.mk
    (E.obj.toRelative ((n + 1 : ℕ) : ℤ) P)
    (E.obj.boundary ((n + 1 : ℕ) : ℤ) P)
    (HomologyTheoryData.IsExact.toRelative_comp_boundary
      E.obj ((n + 1 : ℕ) : ℤ) P)
  let S₂ := ShortComplex.mk
    (E.obj.boundary ((n + 1 : ℕ) : ℤ) P)
    (E.obj.subspaceMap (((n + 1 : ℕ) : ℤ) - 1) P)
    (HomologyTheoryData.IsExact.boundary_comp_subspaceMap
      E.obj ((n + 1 : ℕ) : ℤ) P)
  have hDegree : (((n + 1 : ℕ) : ℤ) - 1) = (n : ℤ) := by omega
  have hS₁f : S₁.f = 0 := hToRelative
  have hS₂g : S₂.g = 0 := by
    change E.obj.subspaceMap (((n + 1 : ℕ) : ℤ) - 1) P = 0
    rw [hDegree]
    exact hSubspace
  have hMono : Mono S₁.g :=
    (ShortComplex.exact_iff_mono S₁ hS₁f).mp
      (HomologyTheoryData.IsExact.exact_toRelative_boundary
        E.obj ((n + 1 : ℕ) : ℤ) P)
  have hEpi : Epi S₂.f :=
    (ShortComplex.exact_iff_epi S₂ hS₂g).mp
      (HomologyTheoryData.IsExact.exact_boundary_subspaceMap
        E.obj ((n + 1 : ℕ) : ℤ) P)
  letI : Mono S₁.g := hMono
  letI : Epi S₁.g := by
    change Epi (E.obj.boundary ((n + 1 : ℕ) : ℤ) P)
    change Epi S₂.f at hEpi
    exact hEpi
  letI : IsIso S₁.g := isIso_of_mono_of_epi S₁.g
  rw [← hDegree]
  exact @asIso C _ S₁.X₂ S₁.X₃ S₁.g _

/-- Positive-degree relative homology of the classical `(m+1)`-disk pair is
the homology of its boundary sphere. -/
noncomputable opaque classicalCellDiskPairBoundaryIso
    (E : OrdinaryHomologyTheory.{u, v, w} C)
    (m n : ℕ) (hn : n ≠ 0) :
    (E.Hₚ ((n + 1 : ℕ) : ℤ)).obj
        (Topology.CWComplex.classicalCellDiskPair.{w} (m + 1)) ≅
      (E.H (n : ℤ)).obj (TopCat.sphere.{w} m) := by
  let P := Topology.CWComplex.classicalCellDiskPair.{w} (m + 1)
  letI : ContractibleSpace ↥P.fst :=
    Topology.CWComplex.contractibleSpace_classicalCellDiskPair_fst (m + 1)
  exact relativeBoundaryIsoOfContractibleAmbient E P n hn ≪≫
    E.obj.absoluteIsoOfHomotopyEquiv
      (Topology.CWComplex.classicalCellBoundarySphereHomeomorph m).toHomotopyEquiv n

/-- Theory-natural relative homology comparison from a classical disk pair to
its standard boundary sphere. -/
noncomputable def classicalCellDiskPairBoundaryNatIso
    (m : ℕ) (n : ℤ) (hn : n ≠ 0) (hnPrev : n - 1 ≠ 0) :
    hₚFunctor (C := C) n ⋙
        (evaluation TopPair.{w} C).obj
          (Topology.CWComplex.classicalCellDiskPair.{w} (m + 1)) ≅
      hFunctor (C := C) (n - 1) ⋙
        (evaluation TopCat.{w} C).obj (TopCat.sphere.{w} m) :=
  relativeBoundaryNatIsoOfContractibleAmbient
      (C := C) (Topology.CWComplex.classicalCellDiskPair.{w} (m + 1))
        n hn hnPrev ≪≫
    Functor.isoWhiskerLeft forgetDimension
      (TopPair.GeneralizedHomologyTheory.classicalCellBoundarySphereNatIso
        (C := C) m (n - 1))

@[simp]
theorem classicalCellDiskPairBoundaryNatIso_app
    (m : ℕ) (n : ℤ) (hn : n ≠ 0) (hnPrev : n - 1 ≠ 0)
    (E : OrdinaryHomologyTheory.{u, v, w} C) :
    (classicalCellDiskPairBoundaryNatIso
      (C := C) m n hn hnPrev).app E =
      (relativeBoundaryNatIsoOfContractibleAmbient
        (C := C) (Topology.CWComplex.classicalCellDiskPair.{w} (m + 1))
          n hn hnPrev).app E ≪≫
        E.obj.closedBallPairUnitSphereIso
          (EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm (n - 1) :=
  rfl

end TopPair.OrdinaryHomologyTheory
