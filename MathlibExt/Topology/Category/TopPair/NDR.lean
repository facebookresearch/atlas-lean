/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua, Avocado
-/

module

public import MathlibExt.Topology.Category.TopPair.GoodPair
import Mathlib.Topology.Order.ProjIcc
import Mathlib.Topology.Algebra.Algebra

/-!
# Controlled neighborhood deformation retract data

An `NDRData P` is a Strøm-style controlled deformation for the embedded
subspace of a topological pair, strengthened by a control-monotonicity axiom:
its control vanishes exactly on the subspace, does not increase along a
global deformation fixed on the subspace, and the deformation endpoint reaches
the subspace wherever the control is less than one.

The monotonicity axiom is nonstandard: textbook NDR data (here
`StandardNDRData`) omits it.  Monotonicity is exactly what makes the global
deformation preserve the controlled neighborhood (`deformation_mem_neighborhood`),
which the descent to `GoodPairData` requires; the Hurewicz cofibration theorem
needs only standard data (see `NDRCofibration`).  `NDRData.toStandard` forgets
the axiom, while `StandardNDRData.toNDRData` restores it from an explicit
monotonicity proof.  The reverse conversion is not provable in general.

`StandardNDRData` and `NDRData` share the controlled neighborhood and its
basic lemmas; only the neighborhood deformation and the good-pair descent use
monotonicity.  Product and quotient constructors are developed separately.
-/

@[expose] public section

set_option autoImplicit false
set_option warningAsError true

noncomputable section

open CategoryTheory Filter Topology
open scoped unitInterval

universe u

namespace TopPair

/-- The bounded ratio `a / b` of interval elements, defined to be zero when
`b = 0`.  This isolates the one discontinuity shared by the NDR cylinder
retraction and the pushout-product deformation; composites with a relative
deformation stay continuous by the compact-time fixed-locus theorem. -/
noncomputable def boundedRatio (a b : unitInterval) : unitInterval :=
  if b = 0 then 0
  else Set.projIcc (0 : ℝ) 1 zero_le_one ((a : ℝ) / (b : ℝ))

@[simp]
theorem boundedRatio_zero_right (a : unitInterval) :
    boundedRatio a 0 = 0 := by
  simp [boundedRatio]

@[simp]
theorem boundedRatio_zero_left (b : unitInterval) :
    boundedRatio 0 b = 0 := by
  by_cases hb : b = 0
  · simp [hb]
  · apply Subtype.ext
    simp [boundedRatio, hb]

@[simp]
theorem boundedRatio_self_of_ne_zero
    (a : unitInterval) (ha : a ≠ 0) :
    boundedRatio a a = 1 := by
  apply Subtype.ext
  simp [boundedRatio, ha]

theorem continuousAt_boundedRatio_of_ne_zero
    {Z : Type*} [TopologicalSpace Z]
    (a b : Z → unitInterval) (z : Z)
    (ha : ContinuousAt a z) (hb : ContinuousAt b z)
    (hbz : b z ≠ 0) :
    ContinuousAt (fun w => boundedRatio (a w) (b w)) z := by
  have hbz' : (b z : ℝ) ≠ 0 := by
    intro h
    apply hbz
    apply Subtype.ext
    exact h
  have hdiv : ContinuousAt (fun w => (a w : ℝ) / (b w : ℝ)) z :=
    (continuous_subtype_val.continuousAt.comp ha).div
      (continuous_subtype_val.continuousAt.comp hb) hbz'
  have hproj : ContinuousAt
      (fun w => Set.projIcc (0 : ℝ) 1 zero_le_one
        ((a w : ℝ) / (b w : ℝ))) z :=
    continuous_projIcc.continuousAt.comp hdiv
  apply hproj.congr_of_eventuallyEq
  filter_upwards [hb.eventually_ne hbz] with w hw
  simp only [boundedRatio, hw, ↓reduceIte]

/-- Textbook (Strøm-style) neighborhood deformation retract data for a
topological pair, without any monotonicity requirement. -/
structure StandardNDRData (P : TopPair.{u}) where
  /-- Continuous control, vanishing precisely on the embedded subspace. -/
  control : C(P.fst, unitInterval)
  /-- Endpoint of the global deformation. -/
  endpoint : C(P.fst, P.fst)
  /-- Global deformation from the identity to `endpoint`, fixed on the
  embedded subspace. -/
  deformation :
    ContinuousMap.HomotopyRel (ContinuousMap.id P.fst) endpoint
      (Set.range P.map)
  /-- The zero set of the control is exactly the embedded subspace. -/
  control_eq_zero_iff (x : P.fst) :
    control x = 0 ↔ x ∈ Set.range P.map
  /-- On the controlled neighborhood, the endpoint lies in the embedded
  subspace. -/
  endpoint_mem_range (x : P.fst) (hx : control x < 1) :
    endpoint x ∈ Set.range P.map

namespace StandardNDRData

variable {P : TopPair.{u}} (s : StandardNDRData P)

/-- The canonical controlled open neighborhood. -/
def neighborhood : Set P.fst :=
  {x | s.control x < 1}

@[simp]
theorem mem_neighborhood (x : P.fst) :
    x ∈ s.neighborhood ↔ s.control x < 1 :=
  Iff.rfl

/-- The controlled neighborhood is open. -/
theorem isOpen_neighborhood : IsOpen s.neighborhood :=
  isOpen_Iio.preimage s.control.continuous

/-- The embedded subspace lies in the controlled neighborhood. -/
theorem range_subset_neighborhood :
    Set.range P.map ⊆ s.neighborhood := by
  intro x hx
  change s.control x < 1
  rw [(s.control_eq_zero_iff x).2 hx]
  exact zero_lt_one

include s in
/-- The embedded subspace is closed, as the zero fiber of the control. -/
theorem isClosed_range : IsClosed (Set.range P.map) := by
  have hzero : Set.range P.map = s.control ⁻¹' ({0} : Set unitInterval) := by
    ext x
    simp only [Set.mem_preimage, Set.mem_singleton_iff,
      s.control_eq_zero_iff]
  rw [hzero]
  exact isClosed_singleton.preimage s.control.continuous

/-- The deformation endpoint of a point in the controlled neighborhood lies
in the embedded subspace. -/
theorem endpoint_mem_range_of_mem {x : P.fst} (hx : x ∈ s.neighborhood) :
    s.endpoint x ∈ Set.range P.map :=
  s.endpoint_mem_range x hx

end StandardNDRData

/-- Controlled neighborhood deformation retract data for a topological
pair: standard NDR data plus control-nonincrease along the deformation.
The extra axiom is what keeps the deformation inside the controlled
neighborhood; see the module documentation. -/
structure NDRData (P : TopPair.{u}) where
  /-- Continuous control, vanishing precisely on the embedded subspace. -/
  control : C(P.fst, unitInterval)
  /-- Endpoint of the global deformation. -/
  endpoint : C(P.fst, P.fst)
  /-- Global deformation from the identity to `endpoint`, fixed on the
  embedded subspace. -/
  deformation :
    ContinuousMap.HomotopyRel (ContinuousMap.id P.fst) endpoint
      (Set.range P.map)
  /-- The zero set of the control is exactly the embedded subspace. -/
  control_eq_zero_iff (x : P.fst) :
    control x = 0 ↔ x ∈ Set.range P.map
  /-- The control does not increase during the deformation.  This
  nonstandard strengthening is used only to preserve the controlled
  neighborhood. -/
  control_deformation_le (t : unitInterval) (x : P.fst) :
    control (deformation (t, x)) ≤ control x
  /-- On the controlled neighborhood, the endpoint lies in the embedded
  subspace. -/
  endpoint_mem_range (x : P.fst) (hx : control x < 1) :
    endpoint x ∈ Set.range P.map

namespace NDRData

/-- Two controlled NDR data with the same control, endpoint, and deformation
values are equal; the remaining fields are properties. -/
@[ext]
theorem ext {P : TopPair.{u}} {d e : NDRData P}
    (h_control : ∀ x, d.control x = e.control x)
    (h_endpoint : ∀ x, d.endpoint x = e.endpoint x)
    (h_deformation : ∀ t x, d.deformation (t, x) = e.deformation (t, x)) :
    d = e := by
  obtain ⟨c₁, e₁, F₁, _, _, _⟩ := d
  obtain ⟨c₂, e₂, F₂, _, _, _⟩ := e
  have hc : c₁ = c₂ := ContinuousMap.ext h_control
  have he : e₁ = e₂ := ContinuousMap.ext h_endpoint
  subst hc
  subst he
  have hF : F₁ = F₂ :=
    ContinuousMap.HomotopyWith.ext (fun p => h_deformation p.1 p.2)
  subst hF
  rfl

variable {P : TopPair.{u}} (d : NDRData P)

/-- Forget the monotonicity axiom. -/
noncomputable def toStandard : StandardNDRData P where
  control := d.control
  endpoint := d.endpoint
  deformation := d.deformation
  control_eq_zero_iff := d.control_eq_zero_iff
  endpoint_mem_range := d.endpoint_mem_range

@[simp]
theorem toStandard_control : d.toStandard.control = d.control :=
  rfl

@[simp]
theorem toStandard_endpoint : d.toStandard.endpoint = d.endpoint :=
  rfl

@[simp]
theorem toStandard_deformation :
    d.toStandard.deformation = d.deformation :=
  rfl

/-- The canonical controlled open neighborhood. -/
def neighborhood : Set P.fst :=
  d.toStandard.neighborhood

@[simp]
theorem mem_neighborhood (x : P.fst) :
    x ∈ d.neighborhood ↔ d.control x < 1 :=
  d.toStandard.mem_neighborhood x

/-- The controlled neighborhood is open. -/
theorem isOpen_neighborhood : IsOpen d.neighborhood :=
  d.toStandard.isOpen_neighborhood

/-- The embedded subspace lies in the controlled neighborhood. -/
theorem range_subset_neighborhood :
    Set.range P.map ⊆ d.neighborhood :=
  d.toStandard.range_subset_neighborhood

include d in
/-- The embedded subspace is closed, as the zero fiber of the control. -/
theorem isClosed_range : IsClosed (Set.range P.map) :=
  d.toStandard.isClosed_range

/-- The global deformation preserves the controlled neighborhood.  This is
the one consequence of the monotonicity axiom. -/
theorem deformation_mem_neighborhood
    (t : unitInterval) {x : P.fst} (hx : x ∈ d.neighborhood) :
    d.deformation (t, x) ∈ d.neighborhood :=
  lt_of_le_of_lt (d.control_deformation_le t x) hx

/-- The deformation endpoint of a point in the controlled neighborhood lies
in the embedded subspace. -/
theorem endpoint_mem_range_of_mem {x : P.fst} (hx : x ∈ d.neighborhood) :
    d.endpoint x ∈ Set.range P.map :=
  d.toStandard.endpoint_mem_range_of_mem hx

/-- Retraction of the controlled neighborhood onto the original subspace
type. -/
noncomputable def retraction :
    TopCat.of d.neighborhood ⟶ P.snd :=
  TopCat.ofHom
    { toFun := fun x =>
        P.isEmbedding_map.toHomeomorph.symm
          ⟨d.endpoint x.1, d.endpoint_mem_range_of_mem x.2⟩
      continuous_toFun :=
        P.isEmbedding_map.toHomeomorph.symm.continuous.comp
          ((d.endpoint.continuous.comp continuous_subtype_val).subtype_mk _) }

/-- The pair inclusion after the controlled retraction is the deformation
endpoint. -/
@[simp]
theorem map_retraction (x : d.neighborhood) :
    P.map (d.retraction x) = d.endpoint x.1 := by
  exact congrArg Subtype.val
    (P.isEmbedding_map.toHomeomorph.apply_symm_apply
      ⟨d.endpoint x.1, d.endpoint_mem_range_of_mem x.2⟩)

/-- The global deformation restricted to the controlled neighborhood. -/
noncomputable def neighborhoodDeformation :
    ContinuousMap.HomotopyRel
      ((𝟙 (TopCat.of d.neighborhood)) :
        TopCat.of d.neighborhood ⟶ TopCat.of d.neighborhood).hom
      (d.retraction ≫
        TopPair.neighborhoodInclusion P d.neighborhood
          d.range_subset_neighborhood).hom
      (Set.range
        (TopPair.neighborhoodInclusion P d.neighborhood
          d.range_subset_neighborhood).hom) where
  toFun p :=
    ⟨d.deformation (p.1, p.2.1),
      d.deformation_mem_neighborhood p.1 p.2.2⟩
  continuous_toFun :=
    (d.deformation.continuous.comp
      (continuous_fst.prodMk
        (continuous_subtype_val.comp continuous_snd))).subtype_mk _
  map_zero_left x := by
    apply Subtype.ext
    exact d.deformation.apply_zero x.1
  map_one_left x := by
    apply Subtype.ext
    change d.deformation (1, x.1) = P.map (d.retraction x)
    rw [d.deformation.apply_one]
    exact (d.map_retraction x).symm
  prop' t x hx := by
    rcases hx with ⟨a, rfl⟩
    apply Subtype.ext
    change d.deformation (t, P.map a) = P.map a
    exact d.deformation.eq_fst t ⟨a, rfl⟩

/-- Controlled NDR data yields chosen good-pair data when the subspace is
nonempty. -/
noncomputable def toGoodPairData [Nonempty P.snd] : GoodPairData P where
  nonempty_snd := inferInstance
  isClosed_range := d.isClosed_range
  neighborhood := d.neighborhood
  isOpen_neighborhood := d.isOpen_neighborhood
  range_subset_neighborhood := d.range_subset_neighborhood
  retraction := d.retraction
  deformation := d.neighborhoodDeformation

@[simp]
theorem toGoodPairData_neighborhood [Nonempty P.snd] :
    d.toGoodPairData.neighborhood = d.neighborhood :=
  rfl

@[simp]
theorem toGoodPairData_retraction [Nonempty P.snd] :
    d.toGoodPairData.retraction = d.retraction :=
  rfl

@[simp]
theorem toGoodPairData_inclusion [Nonempty P.snd] :
    d.toGoodPairData.inclusion =
      TopPair.neighborhoodInclusion P d.neighborhood
        d.range_subset_neighborhood :=
  rfl

@[simp]
theorem toGoodPairData_deformation_apply [Nonempty P.snd]
    (t : unitInterval) (x : d.neighborhood) :
    d.toGoodPairData.deformation (t, x) =
      d.deformation (t, x.1) :=
  rfl

end NDRData

namespace StandardNDRData

variable {P : TopPair.{u}} (s : StandardNDRData P)

/-- Restore controlled NDR data from standard data plus an explicit
monotonicity proof. -/
noncomputable def toNDRData
    (hmono : ∀ (t : unitInterval) (x : P.fst),
      s.control (s.deformation (t, x)) ≤ s.control x) :
    NDRData P where
  control := s.control
  endpoint := s.endpoint
  deformation := s.deformation
  control_eq_zero_iff := s.control_eq_zero_iff
  control_deformation_le := hmono
  endpoint_mem_range := s.endpoint_mem_range

end StandardNDRData

end TopPair

end
