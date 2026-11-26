/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.Algebra.Homology.CartanEilenberg.RowHomologyZero
public import MathlibExt.Algebra.Homology.VerticalHomologyComplex
import MathlibExt.Algebra.Homology.HomologyDegreeTransport

/-!
# The degree-zero vertical-homology differential

Let P be a Cartan–Eilenberg resolution of L in an abelian category. The degree-zero row-homology
coordinates are PH₀,ₐ ⊕ PB₀,ₐ. The resolution differential preserves the PH₀ coordinate and
descends to the stored PB₀ differential on the quotient.

Its diagonal blocks are the PH₀ and PB₀ differentials. The block from homology to boundary is
zero, while the block from boundary to homology may be nonzero. These blocks describe the
vertical-homology differential in the original degree-zero coordinate.
-/

@[expose] public section

set_option autoImplicit false
set_option warningAsError true

noncomputable section

universe v u

open CategoryTheory CategoryTheory.Limits

namespace HomologicalComplex.CartanEilenbergResolution

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {L : ChainComplex C ℕ} (P : CartanEilenbergResolution L)

/-- Let C be abelian, L a nonnegative chain complex and P a Cartan–Eilenberg resolution of L. In
original degree zero, the resolution-degree-a row homology has coordinates PH₀,ₐ ⊕ PB₀,ₐ, using
the stored homology and outgoing-boundary resolutions. For a ∈ ℕ, the resolution differential
a+1 → a descends to a map Dₐ : PH₀,ₐ₊₁ ⊕ PB₀,ₐ₊₁ → PH₀,ₐ ⊕ PB₀,ₐ in these coordinates. -/
noncomputable def rowHomologyZeroCoordinateMap (a : ℕ) :
    ((P.homologyResolution 0).complex.X (a + 1) ⊞
        (P.boundaryResolution 0).complex.X (a + 1)) ⟶
      ((P.homologyResolution 0).complex.X a ⊞
        (P.boundaryResolution 0).complex.X a) :=
  have condition :
      (P.bicomplex.X (a + 1)).d 1 0 ≫
          (P.termResolution 0).complex.d (a + 1) a ≫
          P.rowHomologyZeroProjection a = 0 := by
    rw [← P.rowHomologyZeroCofork_π a]
    change (P.bicomplex.X (a + 1)).d 1 0 ≫
        (P.bicomplex.d (a + 1) a).f 0 ≫
        (P.rowHomologyZeroCofork a).π = 0
    rw [← Category.assoc, ← (P.bicomplex.d (a + 1) a).comm 1 0,
      Category.assoc, (P.rowHomologyZeroCofork a).condition, comp_zero]
  (CokernelCofork.IsColimit.desc'
    (P.rowHomologyZeroCoforkIsColimit (a + 1))
    ((P.termResolution 0).complex.d (a + 1) a ≫
      P.rowHomologyZeroProjection a)
    condition).1

/-- Let C be abelian, L a nonnegative chain complex and P a Cartan–Eilenberg resolution of L. In
original degree zero, the resolution-degree-a row homology has coordinates PH₀,ₐ ⊕ PB₀,ₐ, using
the stored homology and outgoing-boundary resolutions. Let rₐ be the explicit projection from
the term-resolution component to PH₀,ₐ ⊕ PB₀,ₐ. The descended map Dₐ satisfies Dₐ ∘ rₐ₊₁ = rₐ ∘
d_PT₀^{a+1,a}. -/
@[reassoc]
theorem rowHomologyZeroProjection_comp_coordinateMap (a : ℕ) :
    P.rowHomologyZeroProjection (a + 1) ≫
        P.rowHomologyZeroCoordinateMap a =
      (P.termResolution 0).complex.d (a + 1) a ≫
        P.rowHomologyZeroProjection a := by
  rw [← P.rowHomologyZeroCofork_π (a + 1)]
  exact (P.rowHomologyZeroCoforkIsColimit (a + 1)).fac _
    WalkingParallelPair.one

private theorem rowHomologyZeroProjection_comp_snd (a : ℕ) :
    P.rowHomologyZeroProjection a ≫ biprod.snd =
      (P.termComponentShortComplex a 0).g := by
  rw [P.rowHomologyZeroProjection_eq a]
  simp

private noncomputable def rowHomologyZeroSection (a : ℕ) :=
  (ShortComplex.Splitting.compLeft
    (P.cyclesComponentSplitting a 0)
    (P.termComponentSplitting a 0)).s

private theorem rowHomologyZeroSection_comp_projection (a : ℕ) :
    rowHomologyZeroSection P a ≫ P.rowHomologyZeroProjection a = 𝟙 _ := by
  rw [P.rowHomologyZeroProjection_eq a]
  exact (ShortComplex.Splitting.compLeft
    (P.cyclesComponentSplitting a 0)
    (P.termComponentSplitting a 0)).s_g

private theorem biprod_inl_comp_rowHomologyZeroSection (a : ℕ) :
    biprod.inl ≫ rowHomologyZeroSection P a =
      (P.cyclesComponentSplitting a 0).s ≫
        (P.termComponentShortComplex a 0).f := by
  change biprod.inl ≫
      (ShortComplex.Splitting.compLeft
        (P.cyclesComponentSplitting a 0)
        (P.termComponentSplitting a 0)).s = _
  rw [ShortComplex.Splitting.compLeft_s, biprod.inl_desc]
  rfl

private theorem termComponent_f_comp_d (a : ℕ) :
    (P.termComponentShortComplex (a + 1) 0).f ≫
        (P.termResolution 0).complex.d (a + 1) a =
      (P.cyclesResolution 0).complex.d (a + 1) a ≫
        (P.termComponentShortComplex a 0).f := by
  simpa only [termComponentShortComplex, ShortComplex.map_f,
    HomologicalComplex.eval_map] using
      (P.termHorseshoe 0).i.comm (a + 1) a

private theorem cyclesComponent_d_comp_g (a : ℕ) :
    (P.cyclesResolution 0).complex.d (a + 1) a ≫
        (P.cyclesComponentShortComplex a 0).g =
      (P.cyclesComponentShortComplex (a + 1) 0).g ≫
        (P.homologyResolution 0).complex.d (a + 1) a := by
  simpa only [cyclesComponentShortComplex, ShortComplex.map_g,
    HomologicalComplex.eval_map] using
      ((P.cyclesHorseshoe 0).p.comm (a + 1) a).symm

private theorem termComponent_d_comp_g (a : ℕ) :
    (P.termResolution 0).complex.d (a + 1) a ≫
        (P.termComponentShortComplex a 0).g =
      (P.termComponentShortComplex (a + 1) 0).g ≫
        (P.boundaryResolution 0).complex.d (a + 1) a := by
  simpa only [termComponentShortComplex, ShortComplex.map_g,
    HomologicalComplex.eval_map] using
      ((P.termHorseshoe 0).p.comm (a + 1) a).symm

/-- Let C be abelian, L a nonnegative chain complex and P a Cartan–Eilenberg resolution of L. In
original degree zero, the resolution-degree-a row homology has coordinates PH₀,ₐ ⊕ PB₀,ₐ, using
the stored homology and outgoing-boundary resolutions. The inclusion of the homology-resolution
coordinate commutes with Dₐ: Dₐ ∘ inl = inl ∘ d_PH₀^{a+1,a}. Thus PH₀ is preserved as a
subcomplex. -/
@[reassoc]
theorem biprod_inl_comp_rowHomologyZeroCoordinateMap (a : ℕ) :
    biprod.inl ≫ P.rowHomologyZeroCoordinateMap a =
      (P.homologyResolution 0).complex.d (a + 1) a ≫ biprod.inl := by
  calc
    biprod.inl ≫ P.rowHomologyZeroCoordinateMap a =
        (biprod.inl ≫
          (rowHomologyZeroSection P (a + 1) ≫
            P.rowHomologyZeroProjection (a + 1))) ≫
          P.rowHomologyZeroCoordinateMap a := by
      rw [rowHomologyZeroSection_comp_projection P (a + 1)]
      simp
    _ = (biprod.inl ≫ rowHomologyZeroSection P (a + 1)) ≫
        (P.rowHomologyZeroProjection (a + 1) ≫
          P.rowHomologyZeroCoordinateMap a) := by
      simp only [Category.assoc]
    _ = (biprod.inl ≫ rowHomologyZeroSection P (a + 1)) ≫
        ((P.termResolution 0).complex.d (a + 1) a ≫
          P.rowHomologyZeroProjection a) := by
      rw [P.rowHomologyZeroProjection_comp_coordinateMap a]
    _ = ((P.cyclesComponentSplitting (a + 1) 0).s ≫
          (P.termComponentShortComplex (a + 1) 0).f) ≫
        ((P.termResolution 0).complex.d (a + 1) a ≫
          P.rowHomologyZeroProjection a) := by
      rw [biprod_inl_comp_rowHomologyZeroSection P (a + 1)]
    _ = (P.cyclesComponentSplitting (a + 1) 0).s ≫
        ((P.termComponentShortComplex (a + 1) 0).f ≫
          (P.termResolution 0).complex.d (a + 1) a) ≫
        P.rowHomologyZeroProjection a := by
      simp only [Category.assoc]
    _ = (P.cyclesComponentSplitting (a + 1) 0).s ≫
        ((P.cyclesResolution 0).complex.d (a + 1) a ≫
          (P.termComponentShortComplex a 0).f) ≫
        P.rowHomologyZeroProjection a := by
      rw [termComponent_f_comp_d P a]
    _ = (P.cyclesComponentSplitting (a + 1) 0).s ≫
        (P.cyclesResolution 0).complex.d (a + 1) a ≫
        ((P.termComponentShortComplex a 0).f ≫
          P.rowHomologyZeroProjection a) := by
      simp only [Category.assoc]
    _ = (P.cyclesComponentSplitting (a + 1) 0).s ≫
        (P.cyclesResolution 0).complex.d (a + 1) a ≫
        ((P.cyclesComponentShortComplex a 0).g ≫ biprod.inl) := by
      rw [P.termComponent_f_comp_rowHomologyZeroProjection a]
    _ = (P.cyclesComponentSplitting (a + 1) 0).s ≫
        ((P.cyclesResolution 0).complex.d (a + 1) a ≫
          (P.cyclesComponentShortComplex a 0).g) ≫ biprod.inl := by
      simp only [Category.assoc]
    _ = (P.cyclesComponentSplitting (a + 1) 0).s ≫
        ((P.cyclesComponentShortComplex (a + 1) 0).g ≫
          (P.homologyResolution 0).complex.d (a + 1) a) ≫
        biprod.inl := by
      rw [cyclesComponent_d_comp_g P a]
      rfl
    _ = ((P.cyclesComponentSplitting (a + 1) 0).s ≫
          (P.cyclesComponentShortComplex (a + 1) 0).g) ≫
        (P.homologyResolution 0).complex.d (a + 1) a ≫ biprod.inl := by
      simp only [Category.assoc]
    _ = (P.homologyResolution 0).complex.d (a + 1) a ≫ biprod.inl := by
      rw [(P.cyclesComponentSplitting (a + 1) 0).s_g]
      simp

/-- Let C be abelian, L a nonnegative chain complex and P a Cartan–Eilenberg resolution of L. In
original degree zero, the resolution-degree-a row homology has coordinates PH₀,ₐ ⊕ PB₀,ₐ, using
the stored homology and outgoing-boundary resolutions. The boundary-resolution quotient
coordinate commutes with Dₐ: pr₂ ∘ Dₐ = d_PB₀^{a+1,a} ∘ pr₂. -/
@[reassoc]
theorem rowHomologyZeroCoordinateMap_comp_biprod_snd (a : ℕ) :
    P.rowHomologyZeroCoordinateMap a ≫ biprod.snd =
      biprod.snd ≫
        (P.boundaryResolution 0).complex.d (a + 1) a := by
  let _ : Epi (P.rowHomologyZeroProjection (a + 1)) := by
    rw [← P.rowHomologyZeroCofork_π (a + 1)]
    exact epi_of_isColimit_cofork
      (P.rowHomologyZeroCoforkIsColimit (a + 1))
  apply (cancel_epi (P.rowHomologyZeroProjection (a + 1))).1
  calc
    P.rowHomologyZeroProjection (a + 1) ≫
        (P.rowHomologyZeroCoordinateMap a ≫ biprod.snd) =
      (P.rowHomologyZeroProjection (a + 1) ≫
        P.rowHomologyZeroCoordinateMap a) ≫ biprod.snd :=
      (Category.assoc _ _ _).symm
    _ = ((P.termResolution 0).complex.d (a + 1) a ≫
        P.rowHomologyZeroProjection a) ≫ biprod.snd := by
      rw [P.rowHomologyZeroProjection_comp_coordinateMap a]
    _ = (P.termResolution 0).complex.d (a + 1) a ≫
        (P.rowHomologyZeroProjection a ≫ biprod.snd) :=
      Category.assoc _ _ _
    _ = (P.termResolution 0).complex.d (a + 1) a ≫
        (P.termComponentShortComplex a 0).g := by
      rw [rowHomologyZeroProjection_comp_snd P a]
    _ = (P.termComponentShortComplex (a + 1) 0).g ≫
        (P.boundaryResolution 0).complex.d (a + 1) a :=
      termComponent_d_comp_g P a
    _ = (P.rowHomologyZeroProjection (a + 1) ≫ biprod.snd) ≫
        (P.boundaryResolution 0).complex.d (a + 1) a := by
      rw [rowHomologyZeroProjection_comp_snd P (a + 1)]
    _ = P.rowHomologyZeroProjection (a + 1) ≫
        (biprod.snd ≫
          (P.boundaryResolution 0).complex.d (a + 1) a) :=
      Category.assoc _ _ _

/-- Let C be abelian, L a nonnegative chain complex and P a Cartan–Eilenberg resolution of L. In
original degree zero, the resolution-degree-a row homology has coordinates PH₀,ₐ ⊕ PB₀,ₐ, using
the stored homology and outgoing-boundary resolutions. The map PB₀,ₐ₊₁ → PH₀,ₐ obtained by
including the boundary coordinate, applying Dₐ, and projecting to the homology coordinate is the
possible cross component of this differential. -/
noncomputable def rowHomologyZeroCross (a : ℕ) :
    (P.boundaryResolution 0).complex.X (a + 1) ⟶
      (P.homologyResolution 0).complex.X a :=
  biprod.inr ≫ P.rowHomologyZeroCoordinateMap a ≫ biprod.fst

/-- Let C be abelian, L a nonnegative chain complex and P a Cartan–Eilenberg resolution of L. In
original degree zero, the resolution-degree-a row homology has coordinates PH₀,ₐ ⊕ PB₀,ₐ, using
the stored homology and outgoing-boundary resolutions. The map Dₐ has the stored PH₀ and PB₀
differentials on its diagonal, zero homology-to-boundary component, and the specified
boundary-to-homology cross component. These four blocks determine the full differential. -/
theorem rowHomologyZeroCoordinateMap_eq (a : ℕ) :
    P.rowHomologyZeroCoordinateMap a =
      Biprod.ofComponents
        ((P.homologyResolution 0).complex.d (a + 1) a) 0
        (P.rowHomologyZeroCross a)
        ((P.boundaryResolution 0).complex.d (a + 1) a) := by
  let M := Biprod.ofComponents
    ((P.homologyResolution 0).complex.d (a + 1) a) 0
    (P.rowHomologyZeroCross a)
    ((P.boundaryResolution 0).complex.d (a + 1) a)
  change P.rowHomologyZeroCoordinateMap a = M
  apply biprod.hom_ext
  · apply biprod.hom_ext'
    · have h := congrArg (fun f => f ≫ biprod.fst)
          (P.biprod_inl_comp_rowHomologyZeroCoordinateMap a)
      calc
        biprod.inl ≫ P.rowHomologyZeroCoordinateMap a ≫ biprod.fst =
            (P.homologyResolution 0).complex.d (a + 1) a := by
          simpa only [Category.assoc, biprod.inl_fst,
            Category.comp_id] using h
        _ = biprod.inl ≫ M ≫ biprod.fst := by simp [M]
    · calc
        biprod.inr ≫ P.rowHomologyZeroCoordinateMap a ≫ biprod.fst =
            P.rowHomologyZeroCross a := rfl
        _ = biprod.inr ≫ M ≫ biprod.fst := by simp [M]
  · apply biprod.hom_ext'
    · have h := congrArg (fun f => f ≫ biprod.snd)
          (P.biprod_inl_comp_rowHomologyZeroCoordinateMap a)
      calc
        biprod.inl ≫ P.rowHomologyZeroCoordinateMap a ≫ biprod.snd = 0 := by
          simpa only [Category.assoc, biprod.inl_snd,
            comp_zero] using h
        _ = biprod.inl ≫ M ≫ biprod.snd := by simp [M]
    · have h := congrArg (fun f => biprod.inr ≫ f)
          (P.rowHomologyZeroCoordinateMap_comp_biprod_snd a)
      calc
        biprod.inr ≫ P.rowHomologyZeroCoordinateMap a ≫ biprod.snd =
            (P.boundaryResolution 0).complex.d (a + 1) a := by
          simpa only [← Category.assoc, biprod.inr_snd,
            Category.id_comp] using h
        _ = biprod.inr ≫ M ≫ biprod.snd := by simp [M]

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
private theorem rowHomologyZeroIso_hom (a : ℕ) :
    (P.rowHomologyZeroIso a).hom =
      ((P.bicomplex.X a).homologyIsoSc' 1 0 0
        (by simp) (by simp)).hom ≫
        (P.rowHomologyZeroRightData a).homologyIso.hom := by
  rfl

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
/-- Let C be abelian, L a nonnegative chain complex and P a Cartan–Eilenberg resolution of L. In
original degree zero, the resolution-degree-a row homology has coordinates PH₀,ₐ ⊕ PB₀,ₐ, using
the stored homology and outgoing-boundary resolutions. The isomorphisms H₀(rowₐ) ≅ PH₀,ₐ ⊕ PB₀,ₐ
commute with the resolution-direction maps: the homology map of P.bicomplex.d(a+1,a) corresponds
to Dₐ. -/
@[reassoc]
theorem rowHomologyZeroIso_naturality (a : ℕ) :
    HomologicalComplex.homologyMap (P.bicomplex.d (a + 1) a) 0 ≫
        (P.rowHomologyZeroIso a).hom =
      (P.rowHomologyZeroIso (a + 1)).hom ≫
        P.rowHomologyZeroCoordinateMap a := by
  let φ := P.bicomplex.d (a + 1) a
  let ψ := (HomologicalComplex.shortComplexFunctor' C
    (ComplexShape.down ℕ) 1 0 0).map φ
  let γ : ShortComplex.RightHomologyMapData ψ
      (P.rowHomologyZeroRightData (a + 1))
      (P.rowHomologyZeroRightData a) :=
    ShortComplex.RightHomologyMapData.ofIsColimitCokernelCofork ψ
      ((P.bicomplex.X (a + 1)).shape 0 0 (by simp))
      (P.rowHomologyZeroCofork (a + 1))
      (P.rowHomologyZeroCoforkIsColimit (a + 1))
      ((P.bicomplex.X a).shape 0 0 (by simp))
      (P.rowHomologyZeroCofork a)
      (P.rowHomologyZeroCoforkIsColimit a)
      (P.rowHomologyZeroCoordinateMap a)
      (by
        dsimp only [ψ, φ]
        change (P.termResolution 0).complex.d (a + 1) a ≫
            (P.rowHomologyZeroCofork a).π =
          (P.rowHomologyZeroCofork (a + 1)).π ≫
            P.rowHomologyZeroCoordinateMap a
        rw [P.rowHomologyZeroCofork_π a,
          P.rowHomologyZeroCofork_π (a + 1)]
        exact (P.rowHomologyZeroProjection_comp_coordinateMap a).symm)
  have hH : γ.φH = P.rowHomologyZeroCoordinateMap a := by
    rfl
  rw [rowHomologyZeroIso_hom P a,
    rowHomologyZeroIso_hom P (a + 1)]
  simp only [Category.assoc]
  rw [HomologicalComplex.homologyIsoSc'_hom_naturality_assoc
    φ 1 0 0 (by simp) (by simp)]
  rw [γ.homologyMap_comm, hH]

/-- Let C be abelian, L a nonnegative chain complex and P a Cartan–Eilenberg resolution of L. In
original degree zero, the resolution-degree-a row homology has coordinates PH₀,ₐ ⊕ PB₀,ₐ, using
the stored homology and outgoing-boundary resolutions. Conjugating H₀(P.bicomplex.d(a+1,a)) by
the two row-homology coordinate isomorphisms gives exactly Dₐ. -/
theorem rowHomologyZeroIso_conjugation (a : ℕ) :
    (P.rowHomologyZeroIso (a + 1)).inv ≫
        HomologicalComplex.homologyMap (P.bicomplex.d (a + 1) a) 0 ≫
        (P.rowHomologyZeroIso a).hom =
      P.rowHomologyZeroCoordinateMap a := by
  rw [P.rowHomologyZeroIso_naturality]
  exact (P.rowHomologyZeroIso (a + 1)).inv_hom_id_assoc _

set_option backward.isDefEq.respectTransparency.types false in
/-- Let C be abelian, L a nonnegative chain complex and P a Cartan–Eilenberg resolution of L. In
original degree zero, the resolution-degree-a row homology has coordinates PH₀,ₐ ⊕ PB₀,ₐ, using
the stored homology and outgoing-boundary resolutions. In the vertical-homology chain complex at
original degree zero, the resolution differential has the PH₀ and PB₀ diagonal differentials,
zero homology-to-boundary block and the boundary-to-homology cross block. -/
theorem rowHomologyZeroIso_d (a : ℕ) :
    (P.rowHomologyZeroIso (a + 1)).inv ≫
        (P.bicomplex.verticalHomologyComplex 0).d (a + 1) a ≫
        (P.rowHomologyZeroIso a).hom =
      Biprod.ofComponents
        ((P.homologyResolution 0).complex.d (a + 1) a) 0
        (P.rowHomologyZeroCross a)
        ((P.boundaryResolution 0).complex.d (a + 1) a) := by
  change (P.rowHomologyZeroIso (a + 1)).inv ≫
      HomologicalComplex.homologyMap (P.bicomplex.d (a + 1) a) 0 ≫
      (P.rowHomologyZeroIso a).hom = _
  rw [P.rowHomologyZeroIso_conjugation,
    P.rowHomologyZeroCoordinateMap_eq]

end HomologicalComplex.CartanEilenbergResolution

end
