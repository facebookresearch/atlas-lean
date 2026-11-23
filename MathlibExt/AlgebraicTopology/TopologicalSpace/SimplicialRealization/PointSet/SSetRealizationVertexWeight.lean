/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.SimplicialSet.RealizationPresentation
public import
  MathlibExt.AlgebraicTopology.SimplicialSet.NondegenerateSimplexVertex
public import MathlibExt.AlgebraicTopology.SimplicialSet.RealizationPath
public import MathlibExt.AlgebraicTopology.TopologicalSpace.SimplicialRealization.PointSet.SSetRealizationOpenCellCover
public import MathlibExt.AlgebraicTopology.TopologicalSpace.SimplicialRealization.PointSet.SSetRealizationOpenCellInjective
public import MathlibExt.Analysis.Convex.StdSimplex
public import Mathlib.AlgebraicTopology.SimplicialSet.Nonsingular
public import Mathlib.Topology.Sets.Opens

/-!
# Global vertex weights on finite nonsingular realizations

For a finite nonsingular simplicial set `K`, this file constructs the global
barycentric weight of a vertex `p` on `|K|`.  On a nondegenerate-simplex
presentation, the weight is the sum of all coordinates whose simplex vertex
maps to `p`.

The presentation-level function is proved invariant under every generating
relation of the realized tautological colimit, then descended through
`SSet.isQuotientMap_sigmaToTop`.  No presentation is chosen in the definition
of the global weight.

The positive loci form a finite open cover.  Choosing the already available
unique nondegenerate interior carrier only after this construction gives an
exact boundary-correct membership criterion and a unique carrier position for
each star vertex.

No contraction, incidence edge, atlas, subdivision, or singular-set claim is
made here.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory Limits TopCat
open scoped Simplicial

namespace SSet

/-- The presentation-level weight of `p`, obtained by pushing all simplex
coordinates forward to the vertex set of `K`. -/
@[nolint unusedArguments]
noncomputable def sigmaVertexWeight (K : SSet.{u}) [K.Finite]
    [K.Nonsingular] (p : K _⦋0⦌)
    (x : Σ s : K.N, Convexity.StdSimplex ℝ (Fin (s.dim + 1))) : ℝ :=
  (x.2.map (simplexVertex K x.1)).weights p

/-- Presentation-level vertex weights are continuous on the sigma of
nondegenerate standard simplexes. -/
theorem continuous_sigmaVertexWeight (K : SSet.{u}) [K.Finite]
    [K.Nonsingular] (p : K _⦋0⦌) :
    Continuous (sigmaVertexWeight K p) := by
  apply continuous_sigma
  intro s
  exact (Convexity.StdSimplex.continuous_weights_apply (R := ℝ) p).comp
    (Convexity.StdSimplex.continuous_map ℝ (simplexVertex K s))

private noncomputable abbrev vertexWeightDiagram (K : SSet.{u}) :=
  SSet.realizationColimitPresentation.realizedTautologicalDiagram K

/-- The standard-simplex point underlying an arbitrary element of the
realized tautological diagram. -/
private noncomputable def diagramStdPoint (K : SSet.{u})
    (y : Σ j, (vertexWeightDiagram K).obj j) :
    Convexity.StdSimplex ℝ (Fin (y.1.left.len + 1)) :=
  y.1.left.toTopHomeo y.2

/-- The simplex of `K` underlying an arbitrary element of the realized
tautological diagram. -/
private noncomputable def diagramSimplex (K : SSet.{u})
    (y : Σ j, (vertexWeightDiagram K).obj j) :
    K.obj (Opposite.op y.1.left) :=
  SSet.yonedaEquiv y.1.hom

/-- Vertex labels of an arbitrary realized tautological-diagram element. -/
private noncomputable def diagramVertex (K : SSet.{u})
    (y : Σ j, (vertexWeightDiagram K).obj j) :
    Fin (y.1.left.len + 1) → K _⦋0⦌ := fun i =>
  K.map (SimplexCategory.const ⦋0⦌ y.1.left i).op (diagramSimplex K y)

/-- The whole vertex distribution of a realized tautological-diagram
element.  Naturality of this distribution is the quotient-invariance seam. -/
private noncomputable def diagramVertexDistribution (K : SSet.{u})
    (y : Σ j, (vertexWeightDiagram K).obj j) :
    Convexity.StdSimplex ℝ (K _⦋0⦌) :=
  (diagramStdPoint K y).map (diagramVertex K y)

private theorem diagramSimplex_map (K : SSet.{u})
    {j j' : CostructuredArrow CategoryTheory.uliftYoneda K} (f : j ⟶ j')
    (x : (vertexWeightDiagram K).obj j) :
    diagramSimplex K ⟨j, x⟩ =
      K.map f.left.op
        (diagramSimplex K ⟨j', (vertexWeightDiagram K).map f x⟩) := by
  classical
  have hw : SSet.stdSimplex.map f.left ≫ j'.hom = j.hom :=
    CostructuredArrow.w f
  have hnat : K.map f.left.op (SSet.yonedaEquiv j'.hom) =
      SSet.yonedaEquiv (SSet.stdSimplex.map f.left ≫ j'.hom) :=
    SSet.yonedaEquiv_naturality f.left j'.hom
  simp only [diagramSimplex, hnat, hw]

private theorem diagramVertex_map (K : SSet.{u})
    {j j' : CostructuredArrow CategoryTheory.uliftYoneda K} (f : j ⟶ j')
    (x : (vertexWeightDiagram K).obj j) (i : Fin (j.left.len + 1)) :
    diagramVertex K ⟨j, x⟩ i =
      diagramVertex K ⟨j', (vertexWeightDiagram K).map f x⟩
        (f.left.toOrderHom i) := by
  classical
  rw [diagramVertex, diagramVertex, diagramSimplex_map K f x,
    ← Functor.map_comp_apply, ← op_comp]
  congr 2

private theorem diagramStdPoint_map (K : SSet.{u})
    {j j' : CostructuredArrow CategoryTheory.uliftYoneda K} (f : j ⟶ j')
    (x : (vertexWeightDiagram K).obj j) :
    diagramStdPoint K ⟨j', (vertexWeightDiagram K).map f x⟩ =
      Convexity.StdSimplex.map f.left.toOrderHom
        (diagramStdPoint K ⟨j, x⟩) := by
  classical
  have h : (vertexWeightDiagram K).map f x =
      SSet.toTop.map (SSet.stdSimplex.map f.left) x := rfl
  rw [diagramStdPoint, diagramStdPoint, h]
  exact SimplexCategory.toTopHomeo_naturality_apply f.left x

private theorem diagramVertexDistribution_map (K : SSet.{u})
    {j j' : CostructuredArrow CategoryTheory.uliftYoneda K} (f : j ⟶ j')
    (x : (vertexWeightDiagram K).obj j) :
    diagramVertexDistribution K
        ⟨j', (vertexWeightDiagram K).map f x⟩ =
      diagramVertexDistribution K ⟨j, x⟩ := by
  classical
  rw [diagramVertexDistribution, diagramVertexDistribution,
    diagramStdPoint_map K f x, ← Convexity.StdSimplex.map_comp]
  congr 1
  funext i
  exact (diagramVertex_map K f x i).symm

private theorem diagramVertexDistribution_eq_of_eqvGen (K : SSet.{u})
    {x y : Σ j, (vertexWeightDiagram K).obj j}
    (h : Relation.EqvGen (vertexWeightDiagram K).ColimitTypeRel x y) :
    diagramVertexDistribution K x = diagramVertexDistribution K y := by
  induction h with
  | rel x y hxy =>
      obtain ⟨j, x⟩ := x
      obtain ⟨j', y⟩ := y
      rcases hxy with ⟨f, hf⟩
      dsimp only at hf ⊢
      rw [hf]
      exact (diagramVertexDistribution_map K f x).symm
  | refl x => rfl
  | symm x y _ ih => exact ih.symm
  | trans x y z _ _ ihxy ihyz => exact ihxy.trans ihyz

private theorem diagramStdPoint_sigmaPresent (K : SSet.{u}) (s : K.N)
    (q : Convexity.StdSimplex ℝ (Fin (s.dim + 1))) :
    diagramStdPoint K
        ⟨SSet.realizationColimitPresentation.sigmaPresentObj K s,
          SSet.realizationColimitPresentation.sigmaPresentPoint K ⟨s, q⟩⟩ =
      q := by
  change (⦋s.dim⦌.toTopHomeo) ((⦋s.dim⦌.toTopHomeo).symm q) = q
  exact Homeomorph.apply_symm_apply _ _

private theorem diagramSimplex_sigmaPresent (K : SSet.{u}) (s : K.N)
    (q : Convexity.StdSimplex ℝ (Fin (s.dim + 1))) :
    diagramSimplex K
        ⟨SSet.realizationColimitPresentation.sigmaPresentObj K s,
          SSet.realizationColimitPresentation.sigmaPresentPoint K ⟨s, q⟩⟩ =
      s.simplex := by
  classical
  have hhom :
      (CostructuredArrow.mk (SSet.yonedaEquiv.symm s.simplex)).hom =
        SSet.yonedaEquiv.symm s.simplex :=
    CostructuredArrow.mk_hom_eq_self _
  change SSet.yonedaEquiv
      (CostructuredArrow.mk (SSet.yonedaEquiv.symm s.simplex)).hom =
    s.simplex
  rw [hhom]
  exact Equiv.apply_symm_apply _ _

private theorem diagramVertex_sigmaPresent (K : SSet.{u}) (s : K.N)
    (q : Convexity.StdSimplex ℝ (Fin (s.dim + 1))) :
    diagramVertex K
        ⟨SSet.realizationColimitPresentation.sigmaPresentObj K s,
          SSet.realizationColimitPresentation.sigmaPresentPoint K ⟨s, q⟩⟩ =
      simplexVertex K s := by
  classical
  funext i
  rw [diagramVertex, diagramSimplex_sigmaPresent]
  rfl

private theorem diagramVertexDistribution_sigmaPresent (K : SSet.{u})
    (s : K.N) (q : Convexity.StdSimplex ℝ (Fin (s.dim + 1))) :
    diagramVertexDistribution K
        ⟨SSet.realizationColimitPresentation.sigmaPresentObj K s,
          SSet.realizationColimitPresentation.sigmaPresentPoint K ⟨s, q⟩⟩ =
      q.map (simplexVertex K s) := by
  rw [diagramVertexDistribution, diagramStdPoint_sigmaPresent,
    diagramVertex_sigmaPresent]
  rfl

/-- Presentation-level vertex weights are constant on every fiber of the
realization sigma quotient.  The proof uses the actual generated colimit
relation, rather than a chosen realization presentation. -/
theorem sigmaVertexWeight_factorsThrough (K : SSet.{u}) [K.Finite]
    [K.Nonsingular] (p : K _⦋0⦌) :
    Function.FactorsThrough (sigmaVertexWeight K p) (SSet.sigmaToTop K) := by
  intro x y hxy
  have heqv :=
    SSet.realizationColimitPresentation.sigmaToTop_eq_to_eqvGen_colimitTypeRel
      K x y hxy
  have hdist := diagramVertexDistribution_eq_of_eqvGen K heqv
  have hdist' : x.2.map (simplexVertex K x.1) =
      y.2.map (simplexVertex K y.1) :=
    (diagramVertexDistribution_sigmaPresent K x.1 x.2).symm.trans
      (hdist.trans (diagramVertexDistribution_sigmaPresent K y.1 y.2))
  exact congrArg
    (fun q : Convexity.StdSimplex ℝ (K _⦋0⦌) => q.weights p) hdist'

/-- The global barycentric weight of `p` on the realization of a finite
nonsingular simplicial set. -/
noncomputable def realizationVertexWeight (K : SSet.{u}) [K.Finite]
    [K.Nonsingular] (p : K _⦋0⦌) : C(SSet.toTop.obj K, ℝ) :=
  (SSet.isQuotientMap_sigmaToTop K).lift
    (f := ⟨SSet.sigmaToTop K,
      (SSet.isQuotientMap_sigmaToTop K).continuous⟩)
    ⟨sigmaVertexWeight K p, continuous_sigmaVertexWeight K p⟩
    (sigmaVertexWeight_factorsThrough K p)

/-- Exact evaluation of a global vertex weight on a sigma presentation. -/
@[simp]
theorem realizationVertexWeight_sigma (K : SSet.{u}) [K.Finite]
    [K.Nonsingular] (p : K _⦋0⦌) (s : K.N)
    (q : Convexity.StdSimplex ℝ (Fin (s.dim + 1))) :
    realizationVertexWeight K p (SSet.sigmaToTop K ⟨s, q⟩) =
      (q.map (simplexVertex K s)).weights p := by
  change ((SSet.isQuotientMap_sigmaToTop K).lift
    (f := ⟨SSet.sigmaToTop K,
      (SSet.isQuotientMap_sigmaToTop K).continuous⟩)
    ⟨sigmaVertexWeight K p, continuous_sigmaVertexWeight K p⟩
    (sigmaVertexWeight_factorsThrough K p))
      (SSet.sigmaToTop K ⟨s, q⟩) = _
  have h := (SSet.isQuotientMap_sigmaToTop K).lift_comp
    (f := ⟨SSet.sigmaToTop K,
      (SSet.isQuotientMap_sigmaToTop K).continuous⟩)
    ⟨sigmaVertexWeight K p, continuous_sigmaVertexWeight K p⟩
    (sigmaVertexWeight_factorsThrough K p)
  exact ContinuousMap.congr_fun h ⟨s, q⟩

/-- Global vertex weights are nonnegative. -/
theorem realizationVertexWeight_nonneg (K : SSet.{u}) [K.Finite]
    [K.Nonsingular] (p : K _⦋0⦌) (z : SSet.toTop.obj K) :
    0 ≤ realizationVertexWeight K p z := by
  obtain ⟨⟨s, q⟩, rfl⟩ := (SSet.isQuotientMap_sigmaToTop K).surjective z
  rw [realizationVertexWeight_sigma]
  exact (q.map (simplexVertex K s)).nonneg p

private abbrev vertexN (K : SSet.{u}) (p : K _⦋0⦌) : K.N :=
  SSet.N.mk p (by simp)

private def vertexIndex (K : SSet.{u}) (p : K _⦋0⦌) :
    Fin ((vertexN K p).dim + 1) :=
  ⟨0, Nat.zero_lt_succ _⟩

private noncomputable def vertexPoint (K : SSet.{u}) (p : K _⦋0⦌) :
    Convexity.StdSimplex ℝ (Fin ((vertexN K p).dim + 1)) :=
  Convexity.StdSimplex.single (vertexIndex K p)

private theorem simplexVertex_vertexN (K : SSet.{u}) (p : K _⦋0⦌) :
    simplexVertex K (vertexN K p) (vertexIndex K p) = p := by
  change (SSet.yonedaEquiv.symm p).app _
    (SSet.stdSimplex.obj₀Equiv.symm 0) = p
  rw [SSet.yonedaEquiv_symm_zero]
  simp [SSet.const]

private theorem sigmaToTop_vertexN (K : SSet.{u}) (p : K _⦋0⦌) :
    SSet.sigmaToTop K ⟨vertexN K p, vertexPoint K p⟩ =
      SSet.realizedVertex p := by
  unfold vertexPoint vertexIndex vertexN SSet.sigmaToTop SSet.realizedVertex
  congr 1

open Classical in
/-- At a realized vertex, the global weight is the Kronecker delta. -/
@[simp]
theorem realizationVertexWeight_realizedVertex (K : SSet.{u}) [K.Finite]
    [K.Nonsingular] (p q : K _⦋0⦌) :
    realizationVertexWeight K p (SSet.realizedVertex q) =
      if q = p then 1 else 0 := by
  rw [← sigmaToTop_vertexN K q, realizationVertexWeight_sigma]
  rw [vertexPoint, Convexity.StdSimplex.map_single,
    simplexVertex_vertexN,
    Convexity.StdSimplex.weights_single]
  rw [Finsupp.single_apply]

/-- The positive global-weight locus of a vertex. -/
noncomputable def nonsingularVertexStar (K : SSet.{u}) [K.Finite]
    [K.Nonsingular] (p : K _⦋0⦌) :
    TopologicalSpace.Opens (SSet.toTop.obj K) where
  carrier := realizationVertexWeight K p ⁻¹' Set.Ioi 0
  is_open' := isOpen_Ioi.preimage (realizationVertexWeight K p).continuous

/-- Membership in a vertex star is strict positivity of its global weight. -/
@[simp]
theorem mem_nonsingularVertexStar_iff (K : SSet.{u}) [K.Finite]
    [K.Nonsingular] (p : K _⦋0⦌) (z : SSet.toTop.obj K) :
    z ∈ nonsingularVertexStar K p ↔ 0 < realizationVertexWeight K p z :=
  Iff.rfl

/-- A realized vertex lies in its own positive star. -/
theorem realizedVertex_mem_nonsingularVertexStar (K : SSet.{u}) [K.Finite]
    [K.Nonsingular] (p : K _⦋0⦌) :
    SSet.realizedVertex p ∈ nonsingularVertexStar K p := by
  rw [mem_nonsingularVertexStar_iff,
    realizationVertexWeight_realizedVertex]
  simp

/-- The finite family of positive vertex stars covers the realization. -/
theorem exists_mem_nonsingularVertexStar (K : SSet.{u}) [K.Finite]
    [K.Nonsingular] (z : SSet.toTop.obj K) :
    ∃ p : K _⦋0⦌, z ∈ nonsingularVertexStar K p := by
  classical
  obtain ⟨⟨s, q⟩, rfl⟩ := (SSet.isQuotientMap_sigmaToTop K).surjective z
  have hsum : ∑ i, q.weights i = 1 := by
    rw [← Finsupp.sum_fintype q.weights (fun _ r => r) (by simp)]
    exact q.total
  have hpos : 0 < ∑ i, q.weights i := by
    rw [hsum]
    norm_num
  rw [Finset.sum_pos_iff_of_nonneg (fun i _ => q.nonneg i)] at hpos
  obtain ⟨i, hi⟩ : ∃ i, 0 < q.weights i := by simpa using hpos
  refine ⟨simplexVertex K s i, ?_⟩
  rw [mem_nonsingularVertexStar_iff, realizationVertexWeight_sigma,
    Convexity.StdSimplex.weights_map_apply]
  refine Finset.sum_pos' (fun j _ => q.nonneg j) ⟨i, ?_, hi⟩
  simp

/-- A nondegenerate strictly-positive presentation of a realization point. -/
structure InteriorCarrierAt (K : SSet.{u}) (z : SSet.toTop.obj K) where
  /-- The unique nondegenerate carrier simplex. -/
  carrier : K.N
  /-- Its strictly-positive standard-simplex point. -/
  point : Convexity.StdSimplex ℝ (Fin (carrier.dim + 1))
  /-- Every carrier coordinate is positive. -/
  point_pos : ∀ i, 0 < point.weights i
  /-- The presentation realizes to the specified point. -/
  sigma_eq : SSet.sigmaToTop K ⟨carrier, point⟩ = z

/-- The carrier simplex is independent of the chosen strictly-positive
nondegenerate presentation. -/
theorem InteriorCarrierAt.carrier_eq {K : SSet.{u}} {z : SSet.toTop.obj K}
    (a b : InteriorCarrierAt K z) : a.carrier = b.carrier := by
  apply SSet.carrier_eq_of_sigmaToTop_eq_of_interior K
    a.carrier b.carrier a.point b.point a.point_pos b.point_pos
  exact a.sigma_eq.trans b.sigma_eq.symm

/-- A fixed interior carrier presentation for a realization point.  It is
chosen only for the incidence API, after the global weights have descended. -/
noncomputable def realizationInteriorCarrier (K : SSet.{u})
    (z : SSet.toTop.obj K) : InteriorCarrierAt K z := by
  classical
  choose n s hs q hq hz using
    SSet.exists_nonDegenerate_interior_presentation K z
  refine ⟨SSet.N.mk s hs, q, ?_, ?_⟩
  · exact hq
  · exact hz

/-- A point belongs to `p`'s star exactly when its unique interior carrier
contains `p` as a simplex vertex.  In particular this statement uses the
lower-dimensional carrier at boundary points. -/
theorem mem_nonsingularVertexStar_iff_exists_position (K : SSet.{u})
    [K.Finite] [K.Nonsingular] (p : K _⦋0⦌) (z : SSet.toTop.obj K) :
    z ∈ nonsingularVertexStar K p ↔
      ∃ i : Fin ((realizationInteriorCarrier K z).carrier.dim + 1),
        simplexVertex K (realizationInteriorCarrier K z).carrier i = p := by
  classical
  let c := realizationInteriorCarrier K z
  constructor
  · intro hz
    rw [mem_nonsingularVertexStar_iff, ← c.sigma_eq,
      realizationVertexWeight_sigma,
      Convexity.StdSimplex.weights_map_apply] at hz
    rw [Finset.sum_pos_iff_of_nonneg (fun i _ => c.point.nonneg i)] at hz
    obtain ⟨i, hi, _⟩ := hz
    exact ⟨i, by simpa using hi⟩
  · rintro ⟨i, hi⟩
    have hi' : simplexVertex K c.carrier i = p := by
      simpa [c] using hi
    rw [mem_nonsingularVertexStar_iff, ← c.sigma_eq,
      realizationVertexWeight_sigma,
      Convexity.StdSimplex.weights_map_apply]
    refine Finset.sum_pos' (fun j _ => c.point.nonneg j)
      ⟨i, ?_, c.point_pos i⟩
    simp [hi']

/-- Vertex labels of a nondegenerate simplex in a nonsingular simplicial set
are injective. -/
theorem simplexVertex_injective (K : SSet.{u}) [K.Nonsingular] (s : K.N) :
    Function.Injective (simplexVertex K s) := by
  let x : K.nonDegenerate s.dim := ⟨s.simplex, s.nonDegenerate⟩
  have : Mono (SSet.yonedaEquiv.symm s.simplex) :=
    SSet.Nonsingular.mono x
  have h := CategoryTheory.injective_of_mono
    ((SSet.yonedaEquiv.symm s.simplex).app (Opposite.op ⦋0⦌))
  exact h.comp SSet.stdSimplex.obj₀Equiv.symm.injective

/-- The unique position of a star vertex in the chosen interior carrier. -/
noncomputable def nonsingularVertexStarPosition (K : SSet.{u}) [K.Finite]
    [K.Nonsingular] (p : K _⦋0⦌) (z : SSet.toTop.obj K)
    (hz : z ∈ nonsingularVertexStar K p) :
    Fin ((realizationInteriorCarrier K z).carrier.dim + 1) :=
  (mem_nonsingularVertexStar_iff_exists_position K p z).mp hz |>.choose

/-- The selected carrier position has the requested vertex label. -/
theorem nonsingularVertexStarPosition_vertex (K : SSet.{u}) [K.Finite]
    [K.Nonsingular] (p : K _⦋0⦌) (z : SSet.toTop.obj K)
    (hz : z ∈ nonsingularVertexStar K p) :
    simplexVertex K (realizationInteriorCarrier K z).carrier
        (nonsingularVertexStarPosition K p z hz) = p :=
  (mem_nonsingularVertexStar_iff_exists_position K p z).mp hz |>.choose_spec

/-- Any carrier position with label `p` is the selected position. -/
theorem nonsingularVertexStarPosition_unique (K : SSet.{u}) [K.Finite]
    [K.Nonsingular] (p : K _⦋0⦌) (z : SSet.toTop.obj K)
    (hz : z ∈ nonsingularVertexStar K p)
    (i : Fin ((realizationInteriorCarrier K z).carrier.dim + 1))
    (hi : simplexVertex K (realizationInteriorCarrier K z).carrier i = p) :
    i = nonsingularVertexStarPosition K p z hz := by
  apply simplexVertex_injective K (realizationInteriorCarrier K z).carrier
  rw [hi, nonsingularVertexStarPosition_vertex]

/-- Two star vertices have the same position in the common carrier exactly
when they are equal. -/
theorem nonsingularVertexStarPosition_eq_iff (K : SSet.{u}) [K.Finite]
    [K.Nonsingular] (p q : K _⦋0⦌) (z : SSet.toTop.obj K)
    (hp : z ∈ nonsingularVertexStar K p)
    (hq : z ∈ nonsingularVertexStar K q) :
    nonsingularVertexStarPosition K p z hp =
        nonsingularVertexStarPosition K q z hq ↔ p = q := by
  constructor
  · intro h
    rw [← nonsingularVertexStarPosition_vertex K p z hp,
      ← nonsingularVertexStarPosition_vertex K q z hq, h]
  · rintro rfl
    rfl

end SSet

end
