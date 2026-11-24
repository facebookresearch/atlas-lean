/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.Algebra.Homology.HomologicalComplex.Splitting
public import MathlibExt.Algebra.Homology.HomologicalComplex.HomologyProjection

/-!
# Split complexes and their homology complexes

Normalized generalized inverses give a retraction onto cycles. Their
complementary incoming projector descends to homology and gives a section
of the homology quotient. When the original complex has homology in every
degree, these maps form a homotopy equivalence with its zero-differential
homology complex.

The construction uses preadditivity, arbitrary complex shapes and
independent object, morphism and index universes. Homology for the target
complex follows from its zero differentials; a global category-with-homology
assumption is unnecessary.

## Source credit

The characterization generalizes Weibel, *An Introduction to Homological
Algebra* (1994), Exercise 1.4.4 and its published correction on page 18.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace HomologicalComplex

universe u v w

variable {C : Type u} [Category.{v} C]
  {ι : Type w} {c : ComplexShape ι}

section Preadditive

variable [Preadditive C] {K L : HomologicalComplex C c}

/-- A native homotopy equivalence with a zero-differential complex earns splitting data. -/
def Splitting.ofZeroDifferentialHomotopyEquiv
    (hL : ∀ i j : ι, L.d i j = 0) (e : HomotopyEquiv K L) : Splitting K where
  hom := e.homotopyHomInvId.symm.hom
  zero := e.homotopyHomInvId.symm.zero
  d_h_d i j := by
    let h : Homotopy (𝟙 K) (e.hom ≫ e.inv) := e.homotopyHomInvId.symm
    by_cases hij : c.Rel i j
    · have hId := h.comm j
      simp only [HomologicalComplex.id_f] at hId
      have hq : K.d i j ≫ (e.hom ≫ e.inv).f j = 0 := by
        change K.d i j ≫ (e.hom.f j ≫ e.inv.f j) = 0
        rw [← Category.assoc, ← e.hom.comm i j, hL i j, comp_zero, zero_comp]
      have hd : K.d i j ≫ dNext j h.hom = 0 := by
        change K.d i j ≫ (K.d j (c.next j) ≫ h.hom (c.next j) j) = 0
        rw [← Category.assoc, K.d_comp_d, zero_comp]
      have hp : prevD j h.hom = h.hom j i ≫ K.d i j := prevD_eq h.hom hij
      have he := congrArg (fun a : K.X j ⟶ K.X j => K.d i j ≫ a) hId
      simp only [Category.comp_id, Preadditive.comp_add, hq, hd, zero_add] at he
      rw [hp] at he
      dsimp only [h] at he
      simpa only [Category.assoc, add_zero] using he.symm
    · rw [K.shape i j hij]
      simp only [comp_zero]

/-- The earned inverse components retain the actual native comparison homotopy. -/
lemma Splitting.ofZeroDifferentialHomotopyEquiv_hom
    (hL : ∀ i j : ι, L.d i j = 0) (e : HomotopyEquiv K L) (i j : ι) :
    (Splitting.ofZeroDifferentialHomotopyEquiv hL e).hom i j =
      -e.homotopyHomInvId.hom i j := rfl

/-- Existence of a zero-differential homotopy comparison implies the literal split predicate. -/
lemma isSplit_of_homotopyEquiv_zeroDifferential
    (hL : ∀ i j : ι, L.d i j = 0) (e : HomotopyEquiv K L) : IsSplit K :=
  ⟨Splitting.ofZeroDifferentialHomotopyEquiv hL e⟩

end Preadditive

section Pointwise

variable [Preadditive C] {K : HomologicalComplex C c}

noncomputable section

/-- The complementary outgoing inverse projection lifts through the actual cycle kernel. -/
def Splitting.cyclesRetraction (s : Splitting K) (i : ι) [K.HasHomology i] : K.X i ⟶ K.cycles i :=
  K.liftCycles (𝟙 (K.X i) - dNext i s.normalize.hom) (c.next i) rfl (by
    change (𝟙 (K.X i) - K.d i (c.next i) ≫ s.normalize.hom (c.next i) i) ≫
      K.d i (c.next i) = 0
    rw [Preadditive.sub_comp, Category.id_comp]
    rw [Category.assoc, s.normalize.d_h_d i (c.next i), sub_self])

/-- Its composite with the native cycle inclusion is the outgoing complementary projection. -/
@[reassoc]
lemma Splitting.cyclesRetraction_iCycles (s : Splitting K) (i : ι) [K.HasHomology i] :
    s.cyclesRetraction i ≫ K.iCycles i = 𝟙 (K.X i) - dNext i s.normalize.hom :=
  K.liftCycles_i _ _ _ _

/-- The earned map is a genuine retraction of the native cycle inclusion. -/
@[reassoc]
lemma Splitting.iCycles_cyclesRetraction (s : Splitting K) (i : ι) [K.HasHomology i] :
    K.iCycles i ≫ s.cyclesRetraction i = 𝟙 (K.cycles i) := by
  have ha : K.iCycles i ≫ dNext i s.normalize.hom = 0 := by
    change K.iCycles i ≫ (K.d i (c.next i) ≫ s.normalize.hom (c.next i) i) = 0
    rw [← Category.assoc, K.iCycles_d, zero_comp]
  apply (cancel_mono (K.iCycles i)).1
  calc
    _ = K.iCycles i ≫ (𝟙 (K.X i) - dNext i s.normalize.hom) := by
      rw [Category.assoc, s.cyclesRetraction_iCycles i]
    _ = K.iCycles i := by rw [Preadditive.comp_sub, Category.comp_id, ha, sub_zero]
    _ = 𝟙 (K.cycles i) ≫ K.iCycles i := (Category.id_comp _).symm

/-- The incoming complementary projection descends the actual cycles inclusion to homology. -/
def Splitting.homologyInclusionComponent (s : Splitting K) (i : ι) [K.HasHomology i] :
    K.homology i ⟶ K.X i :=
  (K.sc i).descHomology (K.iCycles i ≫ (𝟙 (K.X i) - prevD i s.normalize.hom)) (by
    have hFactor : (K.sc i).toCycles ≫ K.iCycles i = K.d (c.prev i) i :=
      (K.sc i).toCycles_i
    have hZero : K.d (c.prev i) i ≫
        (𝟙 (K.X i) - s.normalize.hom i (c.prev i) ≫ K.d (c.prev i) i) = 0 := by
      rw [Preadditive.comp_sub, Category.comp_id,
        s.normalize.d_h_d (c.prev i) i, sub_self]
    have h := congrArg
      (fun f : K.X (c.prev i) ⟶ K.X i => f ≫
        (𝟙 (K.X i) - prevD i s.normalize.hom)) hFactor
    change (K.sc i).toCycles ≫
      (K.iCycles i ≫ (𝟙 (K.X i) - prevD i s.normalize.hom)) = 0
    exact (Category.assoc (K.sc i).toCycles (K.iCycles i)
      (𝟙 (K.X i) - prevD i s.normalize.hom)).symm.trans (h.trans hZero))

/-- Its quotient composite is the actual complementary cycles inclusion. -/
@[reassoc]
lemma Splitting.homologyπ_homologyInclusionComponent (s : Splitting K) (i : ι) [K.HasHomology i] :
    K.homologyπ i ≫ s.homologyInclusionComponent i =
      K.iCycles i ≫ (𝟙 (K.X i) - prevD i s.normalize.hom) :=
  (K.sc i).π_descHomology _ _

/-- The earned inclusion component lands in cycles for every differential pair. -/
@[reassoc]
lemma Splitting.homologyInclusionComponent_d (s : Splitting K) (i j : ι) [K.HasHomology i] :
    s.homologyInclusionComponent i ≫ K.d i j = 0 := by
  have hb : prevD i s.normalize.hom ≫ K.d i j = 0 := by
    change (s.normalize.hom i (c.prev i) ≫ K.d (c.prev i) i) ≫ K.d i j = 0
    rw [Category.assoc, K.d_comp_d, comp_zero]
  apply (cancel_epi (K.homologyπ i)).1
  calc
    _ = (K.iCycles i ≫ (𝟙 (K.X i) - prevD i s.normalize.hom)) ≫ K.d i j := by
      rw [← Category.assoc, s.homologyπ_homologyInclusionComponent i]
    _ = K.iCycles i ≫ K.d i j := by
      rw [Category.assoc, Preadditive.sub_comp, Category.id_comp, hb, sub_zero]
    _ = 0 := K.iCycles_d i j
    _ = K.homologyπ i ≫ 0 := comp_zero.symm

end

end Pointwise

section NativeHomology

variable [Preadditive C] {K : HomologicalComplex C c} [∀ i, K.HasHomology i]

noncomputable section

/-- The cycle retraction followed by the native quotient is an actual complex map. -/
def Splitting.homologyProjection (s : Splitting K) : K ⟶ homologyZeroComplex K where
  f i := s.cyclesRetraction i ≫ K.homologyπ i
  comm' i j _ := by
    change (s.cyclesRetraction i ≫ K.homologyπ i) ≫
        (0 : K.homology i ⟶ K.homology j) =
      K.d i j ≫ (s.cyclesRetraction j ≫ K.homologyπ j)
    rw [comp_zero]
    symm
    calc
      _ = K.toCycles i j ≫ (K.iCycles j ≫ s.cyclesRetraction j) ≫ K.homologyπ j := by
        rw [← K.toCycles_i i j]
        simp only [Category.assoc]
      _ = K.toCycles i j ≫ K.homologyπ j := by
        rw [s.iCycles_cyclesRetraction j, Category.id_comp]
      _ = 0 := K.toCycles_comp_homologyπ i j

/-- The projection retains its earned cycle retraction and the actual native quotient. -/
lemma Splitting.homologyProjection_f (s : Splitting K) (i : ι) :
    s.homologyProjection.f i = s.cyclesRetraction i ≫ K.homologyπ i := rfl

/-- The projection restricts on actual cycles to the original homology quotient. -/
@[reassoc]
lemma Splitting.iCycles_homologyProjection_f (s : Splitting K) (i : ι) :
    K.iCycles i ≫ s.homologyProjection.f i = K.homologyπ i := by
  change K.iCycles i ≫ (s.cyclesRetraction i ≫ K.homologyπ i) = K.homologyπ i
  rw [← Category.assoc, s.iCycles_cyclesRetraction i, Category.id_comp]

/-- The actual original differential vanishes after this earned projection. -/
@[reassoc]
lemma Splitting.d_homologyProjection_f (s : Splitting K) (i j : ι) :
    K.d i j ≫ s.homologyProjection.f j = 0 := by
  have h : s.homologyProjection.f i ≫ (0 : K.homology i ⟶ K.homology j) =
      K.d i j ≫ s.homologyProjection.f j := s.homologyProjection.comm i j
  exact h.symm.trans comp_zero

/-- The actual homology inclusions form the reverse complex map. -/
def Splitting.homologyInclusion (s : Splitting K) : homologyZeroComplex K ⟶ K where
  f i := s.homologyInclusionComponent i
  comm' i j _ := by
    change s.homologyInclusionComponent i ≫ K.d i j =
      (0 : K.homology i ⟶ K.homology j) ≫ s.homologyInclusionComponent j
    rw [zero_comp]
    exact s.homologyInclusionComponent_d i j

/-- Its components are the earned descents of the true cycle inclusions. -/
lemma Splitting.homologyInclusion_f (s : Splitting K) (i : ι) :
    s.homologyInclusion.f i = s.homologyInclusionComponent i := rfl

/-- The backward-forward composite is literally the identity on the native homology complex. -/
lemma Splitting.homologyInclusion_homologyProjection (s : Splitting K) :
    s.homologyInclusion ≫ s.homologyProjection = 𝟙 (homologyZeroComplex K) := by
  apply HomologicalComplex.Hom.ext
  funext i
  change s.homologyInclusionComponent i ≫ s.homologyProjection.f i = 𝟙 (K.homology i)
  have hb : prevD i s.normalize.hom ≫ s.homologyProjection.f i = 0 := by
    change (s.normalize.hom i (c.prev i) ≫ K.d (c.prev i) i) ≫
      s.homologyProjection.f i = 0
    rw [Category.assoc, s.d_homologyProjection_f (c.prev i) i, comp_zero]
  have hDescent := s.homologyπ_homologyInclusionComponent i
  have hCycle := s.iCycles_homologyProjection_f i
  have sectionIdentity {Z H X : C} (π : Z ⟶ H) [Epi π]
      (ι : Z ⟶ X) (a : H ⟶ X) (p : X ⟶ H) (b : X ⟶ X)
      (hDescent : π ≫ a = ι ≫ (𝟙 X - b)) (hCycle : ι ≫ p = π)
      (hb : b ≫ p = 0) : a ≫ p = 𝟙 H := by
    apply (cancel_epi π).1
    rw [← Category.assoc, hDescent, Category.assoc,
      Preadditive.sub_comp, Category.id_comp, hb, sub_zero, hCycle, Category.comp_id]
  exact sectionIdentity (K.homologyπ i) (K.iCycles i)
    (s.homologyInclusionComponent i) (s.homologyProjection.f i)
    (prevD i s.normalize.hom) hDescent hCycle hb

/-- The earned projection-inclusion endomorphism is an actual idempotent. -/
lemma Splitting.homologyProjectionInclusion_idempotent (s : Splitting K) :
    (s.homologyProjection ≫ s.homologyInclusion) ≫
        (s.homologyProjection ≫ s.homologyInclusion) =
      s.homologyProjection ≫ s.homologyInclusion := by
  calc
    _ = s.homologyProjection ≫
        (s.homologyInclusion ≫ s.homologyProjection) ≫ s.homologyInclusion := by
      simp only [Category.assoc]
    _ = s.homologyProjection ≫ s.homologyInclusion := by
      rw [s.homologyInclusion_homologyProjection, Category.id_comp]

/-- The forward-backward component is the complementary normalized homology projection. -/
lemma Splitting.homologyProjection_comp_homologyInclusion_f (s : Splitting K) (i : ι) :
    s.homologyProjection.f i ≫ s.homologyInclusion.f i =
      𝟙 (K.X i) - (dNext i s.normalize.hom + prevD i s.normalize.hom) := by
  let a : K.X i ⟶ K.X i := dNext i s.normalize.hom
  let b : K.X i ⟶ K.X i := prevD i s.normalize.hom
  have hab : a ≫ b = 0 := by
    change (K.d i (c.next i) ≫ s.normalize.hom (c.next i) i) ≫
      (s.normalize.hom i (c.prev i) ≫ K.d (c.prev i) i) = 0
    calc
      _ = K.d i (c.next i) ≫
          (s.normalize.hom (c.next i) i ≫ s.normalize.hom i (c.prev i)) ≫
            K.d (c.prev i) i := by simp only [Category.assoc]
      _ = 0 := by
        rw [s.normalize_hom_comp_hom (c.next i) i (c.prev i)]
        simp only [zero_comp, comp_zero]
  change (s.cyclesRetraction i ≫ K.homologyπ i) ≫
    s.homologyInclusionComponent i = 𝟙 (K.X i) - (a + b)
  calc
    _ = s.cyclesRetraction i ≫ (K.iCycles i ≫ (𝟙 (K.X i) - b)) := by
      rw [Category.assoc, s.homologyπ_homologyInclusionComponent i]
    _ = (𝟙 (K.X i) - a) ≫ (𝟙 (K.X i) - b) := by
      rw [← Category.assoc, s.cyclesRetraction_iCycles i]
    _ = 𝟙 (K.X i) - (a + b) := by
      simp only [Preadditive.sub_comp, Preadditive.comp_sub, Category.id_comp,
        Category.comp_id, hab]
      abel

/-- The actual normalized inverse maps give the forward-backward comparison homotopy. -/
def Splitting.homotopyIdHomologyProjectionInclusion (s : Splitting K) :
    Homotopy (𝟙 K) (s.homologyProjection ≫ s.homologyInclusion) where
  hom := s.normalize.hom
  zero := s.normalize.zero
  comm i := by
    rw [HomologicalComplex.id_f, HomologicalComplex.comp_f,
      s.homologyProjection_comp_homologyInclusion_f i]
    abel

/-- These earned complex maps and homotopies form a native homotopy equivalence. -/
def Splitting.homotopyEquivHomology (s : Splitting K) :
    HomotopyEquiv K (homologyZeroComplex K) where
  hom := s.homologyProjection
  inv := s.homologyInclusion
  homotopyHomInvId := s.homotopyIdHomologyProjectionInclusion.symm
  homotopyInvHomId := Homotopy.ofEq (s.homologyInclusion_homologyProjection)

/-- The comparison uses the actual earned projection. -/
lemma Splitting.homotopyEquivHomology_hom (s : Splitting K) :
    s.homotopyEquivHomology.hom = s.homologyProjection := rfl

/-- Its reverse is the actual earned inclusion. -/
lemma Splitting.homotopyEquivHomology_inv (s : Splitting K) :
    s.homotopyEquivHomology.inv = s.homologyInclusion := rfl

/-- Its forward-backward homotopy retains the negative normalized inverse components. -/
lemma Splitting.homotopyEquivHomology_homotopyHomInvId_hom
    (s : Splitting K) (i j : ι) :
    s.homotopyEquivHomology.homotopyHomInvId.hom i j = -s.normalize.hom i j := rfl

/-- The projection induces precisely the inverse canonical native homology comparison. -/
@[reassoc]
lemma Splitting.homologyProjection_homologyMap_hom (s : Splitting K) (i : ι) :
    homologyMap s.homologyProjection i ≫
        (homologyZeroComplexHomologyIso K i).hom = 𝟙 (K.homology i) := by
  let L : HomologicalComplex C c := homologyZeroComplex K
  let q : K ⟶ L := s.homologyProjection
  let e : L.homology i ≅ K.homology i := homologyZeroComplexHomologyIso K i
  let π : K.cycles i ⟶ K.homology i := K.homologyπ i
  let π' : L.cycles i ⟶ L.homology i := L.homologyπ i
  let z : K.cycles i ⟶ L.cycles i := cyclesMap q i
  let m : K.homology i ⟶ L.homology i := homologyMap q i
  have hm : π ≫ m = z ≫ π' := homologyπ_naturality q i
  have he : π' ≫ e.hom = L.iCycles i := homologyZeroComplexHomologyIso_π K i
  have hz : z ≫ L.iCycles i = K.iCycles i ≫ q.f i := cyclesMap_i q i
  have hq : K.iCycles i ≫ q.f i = π := s.iCycles_homologyProjection_f i
  apply (cancel_epi π).1
  change π ≫ (m ≫ e.hom) = π ≫ 𝟙 (K.homology i)
  have hFirst : π ≫ (m ≫ e.hom) = (π ≫ m) ≫ e.hom :=
    (Category.assoc π m e.hom).symm
  have hMap : (π ≫ m) ≫ e.hom = (z ≫ π') ≫ e.hom :=
    congrArg (fun t : K.cycles i ⟶ L.homology i => t ≫ e.hom) hm
  have hAssoc : (z ≫ π') ≫ e.hom = z ≫ (π' ≫ e.hom) :=
    Category.assoc z π' e.hom
  let ιL : L.cycles i ⟶ K.homology i := L.iCycles i
  have hCycle : z ≫ (π' ≫ e.hom) = z ≫ ιL :=
    congrArg (fun t : L.cycles i ⟶ K.homology i => z ≫ t) he
  have hNative : z ≫ ιL = K.iCycles i ≫ q.f i := hz
  have hLast : π = π ≫ 𝟙 (K.homology i) := (Category.comp_id π).symm
  exact hFirst.trans (hMap.trans (hAssoc.trans
    (hCycle.trans (hNative.trans (hq.trans hLast)))))

/-- The computed native homology map is the canonical comparison inverse. -/
lemma Splitting.homologyProjection_homologyMap (s : Splitting K) (i : ι) :
    homologyMap s.homologyProjection i = (homologyZeroComplexHomologyIso K i).inv := by
  apply (cancel_mono (homologyZeroComplexHomologyIso K i).hom).1
  exact (s.homologyProjection_homologyMap_hom i).trans
    (homologyZeroComplexHomologyIso K i).inv_hom_id.symm

/-- The reverse map induces the canonical native comparison, not a chosen homology map. -/
lemma Splitting.homologyInclusion_homologyMap (s : Splitting K) (i : ι) :
    homologyMap s.homologyInclusion i = (homologyZeroComplexHomologyIso K i).hom := by
  let e := homologyZeroComplexHomologyIso K i
  have h : homologyMap s.homologyInclusion i ≫ homologyMap s.homologyProjection i =
      𝟙 ((homologyZeroComplex K).homology i) := by
    rw [← homologyMap_comp, s.homologyInclusion_homologyProjection, homologyMap_id]
  apply (cancel_mono e.inv).1
  exact (show homologyMap s.homologyInclusion i ≫ e.inv = 𝟙 _ from by
    simpa only [s.homologyProjection_homologyMap i] using h).trans e.hom_inv_id.symm

/-- The earned projection is a quasi-isomorphism for the original native homology. -/
lemma Splitting.quasiIso_homologyProjection (s : Splitting K) :
    _root_.QuasiIso s.homologyProjection := by
  apply (quasiIso_iff s.homologyProjection).2
  intro i
  apply (quasiIsoAt_iff_isIso_homologyMap s.homologyProjection i).2
  rw [s.homologyProjection_homologyMap i]
  infer_instance

/-- The earned inclusion is a quasi-isomorphism for the original native homology. -/
lemma Splitting.quasiIso_homologyInclusion (s : Splitting K) :
    _root_.QuasiIso s.homologyInclusion := by
  apply (quasiIso_iff s.homologyInclusion).2
  intro i
  apply (quasiIsoAt_iff_isIso_homologyMap s.homologyInclusion i).2
  rw [s.homologyInclusion_homologyMap i]
  infer_instance

/-- Literal splitting is equivalent to homotopy equivalence with the original homology complex. -/
lemma isSplit_iff_homotopyEquiv_homologyZeroComplex (K : HomologicalComplex C c)
    [∀ i, K.HasHomology i] :
    IsSplit K ↔ Nonempty (HomotopyEquiv K (homologyZeroComplex K)) := by
  constructor
  · rintro ⟨s⟩
    exact ⟨s.homotopyEquivHomology⟩
  · rintro ⟨e⟩
    exact isSplit_of_homotopyEquiv_zeroDifferential (homologyZeroComplex_d K) e

end

end NativeHomology

end HomologicalComplex
