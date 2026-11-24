/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.Algebra.Homology.HomologicalComplex.CyclesComplex
public import Mathlib.Algebra.Homology.QuasiIso

/-!
# Projection onto the zero-differential homology complex

The fixed end complex retains the original native homology objects and maps
under only pointwise homology of that complex. The global homology-zero-complex
functor retains CategoryWithHomology. Target homology is earned from native
zero-differential data, with no replacement of the chosen cycles or quotients.
Across arbitrary complex shapes, projectivity of the actual outgoing images splits the first
cycles/term/image sequence degreewise. Its retractions followed by the native
homology quotients form a genuine complex map, and its induced homology map
is the canonical identity. The choices are generally not natural in the
original complex. No reverse complex map or splitting of the
boundaries/cycles/homology sequence is asserted.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits

namespace HomologicalComplex

universe u v w

variable {C : Type u} [Category.{v} C]
  {ι : Type w} {c : ComplexShape ι}

section NativeHomologyComplex

variable [HasZeroMorphisms C]

/-- Keep all original homology objects and maps, with zero differentials. -/
def homologyZeroComplexFunctor [CategoryWithHomology C] :
    HomologicalComplex C c ⥤ HomologicalComplex C c :=
  (Functor.pi' (fun i : ι => homologyFunctor C c i)) ⋙
    zeroDifferentialFunctor (C := C) c

/-- The zero-differential complex of the original homology objects. -/
def homologyZeroComplex (P : HomologicalComplex C c) [∀ i, P.HasHomology i] :
    HomologicalComplex C c :=
  (zeroDifferentialFunctor (C := C) c).obj (fun i => P.homology i)

/-- The target has native homology because both of its differentials are zero. -/
instance homologyZeroComplex_hasHomology (P : HomologicalComplex C c)
    [∀ i, P.HasHomology i] (i : ι) : (homologyZeroComplex P).HasHomology i :=
  ShortComplex.HasHomology.mk'
    (ShortComplex.HomologyData.ofZeros ((homologyZeroComplex P).sc i) rfl rfl)

/-- In a globally homological category this is the original global functor object. -/
lemma homologyZeroComplexFunctor_obj [CategoryWithHomology C]
    (P : HomologicalComplex C c) :
    (homologyZeroComplexFunctor (C := C) (c := c)).obj P = homologyZeroComplex P := rfl

/-- Native homology maps give the zero-complex map for just these two endpoints. -/
def homologyZeroComplexMap {P Q : HomologicalComplex C c}
    [∀ i, P.HasHomology i] [∀ i, Q.HasHomology i] (f : P ⟶ Q) :
    homologyZeroComplex P ⟶ homologyZeroComplex Q :=
  (zeroDifferentialFunctor (C := C) c).map (fun i => homologyMap f i)

/-- Its component is the original native map on homology. -/
lemma homologyZeroComplexMap_f {P Q : HomologicalComplex C c}
    [∀ i, P.HasHomology i] [∀ i, Q.HasHomology i] (f : P ⟶ Q) (i : ι) :
    (homologyZeroComplexMap f).f i = homologyMap f i := rfl

/-- The fixed-endpoint construction preserves the actual identity. -/
lemma homologyZeroComplexMap_id (P : HomologicalComplex C c)
    [∀ i, P.HasHomology i] :
    homologyZeroComplexMap (𝟙 P) = 𝟙 (homologyZeroComplex P) := by
  apply HomologicalComplex.Hom.ext
  funext i
  exact homologyMap_id P i

/-- The fixed-endpoint construction preserves the original composition order. -/
lemma homologyZeroComplexMap_comp {P Q R : HomologicalComplex C c}
    [∀ i, P.HasHomology i] [∀ i, Q.HasHomology i] [∀ i, R.HasHomology i]
    (f : P ⟶ Q) (g : Q ⟶ R) :
    homologyZeroComplexMap (f ≫ g) = homologyZeroComplexMap f ≫ homologyZeroComplexMap g := by
  apply HomologicalComplex.Hom.ext
  funext i
  exact homologyMap_comp f g i

/-- The original global functor uses the same native fixed-endpoint map. -/
lemma homologyZeroComplexFunctor_map_eq [CategoryWithHomology C]
    {P Q : HomologicalComplex C c} (f : P ⟶ Q) :
    (homologyZeroComplexFunctor (C := C) (c := c)).map f = homologyZeroComplexMap f := by
  apply HomologicalComplex.Hom.ext
  funext i
  rfl

/-- Every term is the literal original homology object. -/
lemma homologyZeroComplex_X (P : HomologicalComplex C c) [∀ j, P.HasHomology j]
    (i : ι) :
    (homologyZeroComplex P).X i = P.homology i := rfl

/-- The differential vanishes at every pair, without a bound on the shape. -/
lemma homologyZeroComplex_d (P : HomologicalComplex C c) [∀ k, P.HasHomology k]
    (i j : ι) :
    (homologyZeroComplex P).d i j = 0 := rfl

/-- The induced complex map retains the actual native homology map. -/
lemma homologyZeroComplexFunctor_map_f [CategoryWithHomology C]
    {P Q : HomologicalComplex C c}
    (f : P ⟶ Q) (i : ι) :
    ((homologyZeroComplexFunctor (C := C) (c := c)).map f).f i =
      homologyMap f i := rfl

/-- The native zero-differential cycle and quotient isos compute its homology. -/
def homologyZeroComplexHomologyIso (P : HomologicalComplex C c)
    [∀ j, P.HasHomology j] (i : ι) :
    (homologyZeroComplex P).homology i ≅ P.homology i :=
  let K := homologyZeroComplex P
  (K.isoHomologyπ (c.prev i) i rfl (by rfl)).symm ≪≫
    K.iCyclesIso i (c.next i) rfl (by rfl)

/-- The canonical zero-differential comparison preserves the original cycle inclusion. -/
@[reassoc]
lemma homologyZeroComplexHomologyIso_π (P : HomologicalComplex C c)
    [∀ j, P.HasHomology j] (i : ι) :
    (homologyZeroComplex P).homologyπ i ≫
        (homologyZeroComplexHomologyIso P i).hom =
      (homologyZeroComplex P).iCycles i := by
  let K : HomologicalComplex C c := homologyZeroComplex P
  let π : K.cycles i ⟶ K.homology i := K.homologyπ i
  let a : K.cycles i ≅ K.homology i := K.isoHomologyπ (c.prev i) i rfl (by rfl)
  let b : K.cycles i ≅ P.homology i := K.iCyclesIso i (c.next i) rfl (by rfl)
  have ha : π ≫ a.inv = 𝟙 (K.cycles i) :=
    K.isoHomologyπ_hom_inv_id (c.prev i) i rfl (by rfl)
  change π ≫ (a.inv ≫ b.hom) = K.iCycles i
  exact (Category.assoc π a.inv b.hom).symm.trans
    ((congrArg (fun t : K.cycles i ⟶ K.cycles i => t ≫ b.hom) ha).trans
      (Category.id_comp b.hom))

/-- The canonical comparison is natural under only endpoint-local homology. -/
lemma homologyZeroComplexHomologyIso_map_naturality {P Q : HomologicalComplex C c}
    [∀ j, P.HasHomology j] [∀ j, Q.HasHomology j]
    (f : P ⟶ Q) (i : ι) :
    homologyMap (homologyZeroComplexMap f) i ≫
        (homologyZeroComplexHomologyIso Q i).hom =
      (homologyZeroComplexHomologyIso P i).hom ≫ homologyMap f i := by
  let K : HomologicalComplex C c := homologyZeroComplex P
  let L : HomologicalComplex C c := homologyZeroComplex Q
  let a : K ⟶ L := homologyZeroComplexMap f
  let e : K.homology i ≅ P.homology i := homologyZeroComplexHomologyIso P i
  let e' : L.homology i ≅ Q.homology i := homologyZeroComplexHomologyIso Q i
  let π : K.cycles i ⟶ K.homology i := K.homologyπ i
  let π' : L.cycles i ⟶ L.homology i := L.homologyπ i
  let z : K.cycles i ⟶ L.cycles i := cyclesMap a i
  let m : K.homology i ⟶ L.homology i := homologyMap a i
  let n : P.homology i ⟶ Q.homology i := homologyMap f i
  have hm : π ≫ m = z ≫ π' := homologyπ_naturality a i
  have he : π ≫ e.hom = K.iCycles i := homologyZeroComplexHomologyIso_π P i
  have he' : π' ≫ e'.hom = L.iCycles i := homologyZeroComplexHomologyIso_π Q i
  have hz : z ≫ L.iCycles i = K.iCycles i ≫ n := cyclesMap_i a i
  apply (cancel_epi π).1
  change π ≫ (m ≫ e'.hom) = π ≫ (e.hom ≫ n)
  have hFirst : π ≫ (m ≫ e'.hom) = (π ≫ m) ≫ e'.hom :=
    (Category.assoc π m e'.hom).symm
  have hMap : (π ≫ m) ≫ e'.hom = (z ≫ π') ≫ e'.hom :=
    congrArg (fun t : K.cycles i ⟶ L.homology i => t ≫ e'.hom) hm
  have hAssoc : (z ≫ π') ≫ e'.hom = z ≫ (π' ≫ e'.hom) :=
    Category.assoc z π' e'.hom
  let ιL : L.cycles i ⟶ Q.homology i := L.iCycles i
  let ιK : K.cycles i ⟶ P.homology i := K.iCycles i
  have hCycle : z ≫ (π' ≫ e'.hom) = z ≫ ιL :=
    congrArg (fun t : L.cycles i ⟶ Q.homology i => z ≫ t) he'
  have hNative : z ≫ ιL = ιK ≫ n := hz
  have hSource : ιK ≫ n = (π ≫ e.hom) ≫ n :=
    congrArg (fun t : K.cycles i ⟶ P.homology i => t ≫ n) he.symm
  have hLast : (π ≫ e.hom) ≫ n = π ≫ (e.hom ≫ n) :=
    Category.assoc π e.hom n
  exact hFirst.trans (hMap.trans (hAssoc.trans
    (hCycle.trans (hNative.trans (hSource.trans hLast)))))


/-- The original global-functor naturality statement specializes the local law. -/
lemma homologyZeroComplexHomologyIso_naturality [CategoryWithHomology C]
    {P Q : HomologicalComplex C c} (f : P ⟶ Q) (i : ι) :
    homologyMap ((homologyZeroComplexFunctor (C := C) (c := c)).map f) i ≫
        (homologyZeroComplexHomologyIso Q i).hom =
      (homologyZeroComplexHomologyIso P i).hom ≫ homologyMap f i :=
  homologyZeroComplexHomologyIso_map_naturality f i

end NativeHomologyComplex

section AbelianProjection

variable [Abelian C]

/-- Actual image projectivity chooses a degree retraction and earns a genuine complex map. -/
def homologyProjection (P : HomologicalComplex C c)
    (hI : ∀ i : ι, Projective (Abelian.image (P.d i (c.next i)))) :
    P ⟶ homologyZeroComplex P := by
  let r (i : ι) : P.X i ⟶ P.cycles i := by
    let : Projective (Abelian.image (P.d i (c.next i))) := hI i
    exact (cyclesImageSequenceSplitting P i (c.next i) rfl).r
  have hr (i : ι) : P.iCycles i ≫ r i = 𝟙 (P.cycles i) := by
    let : Projective (Abelian.image (P.d i (c.next i))) := hI i
    exact (cyclesImageSequenceSplitting P i (c.next i) rfl).f_r
  refine
    { f i := r i ≫ P.homologyπ i
      comm' i j _ := ?_ }
  let t : P.X i ⟶ P.cycles j := P.toCycles i j
  let z : P.cycles j ⟶ P.X j := P.iCycles j
  let π : P.cycles j ⟶ P.homology j := P.homologyπ j
  have hz : t ≫ z = P.d i j := P.toCycles_i i j
  have h : P.d i j ≫ (r j ≫ π) = 0 := by
    calc
      _ = (t ≫ z) ≫ (r j ≫ π) := congrArg (fun a => a ≫ r j ≫ π) hz.symm
      _ = t ≫ z ≫ r j ≫ π := Category.assoc t z (r j ≫ π)
      _ = t ≫ (z ≫ r j) ≫ π :=
        congrArg (fun a : P.cycles j ⟶ P.homology j => t ≫ a)
          (Category.assoc z (r j) π).symm
      _ = t ≫ (𝟙 (P.cycles j)) ≫ π :=
        congrArg (fun a : P.cycles j ⟶ P.cycles j => t ≫ a ≫ π) (hr j)
      _ = t ≫ π := congrArg (fun a => t ≫ a) (Category.id_comp π)
      _ = 0 := P.toCycles_comp_homologyπ i j
  change (r i ≫ P.homologyπ i) ≫ (0 : P.homology i ⟶ P.homology j) =
    P.d i j ≫ (r j ≫ π)
  exact CategoryTheory.Limits.comp_zero.trans h.symm

/-- The chosen projection is the actual degree retraction followed by the native quotient. -/
lemma homologyProjection_f (P : HomologicalComplex C c)
    (hI : ∀ i : ι, Projective (Abelian.image (P.d i (c.next i)))) (i : ι) :
    (homologyProjection P hI).f i =
      (letI : Projective (Abelian.image (P.d i (c.next i))) := hI i
       (cyclesImageSequenceSplitting P i (c.next i) rfl).r) ≫ P.homologyπ i := rfl

/-- Its restriction to actual cycles is precisely the original homology quotient. -/
@[reassoc]
lemma iCycles_homologyProjection_f (P : HomologicalComplex C c)
    (hI : ∀ i : ι, Projective (Abelian.image (P.d i (c.next i)))) (i : ι) :
    P.iCycles i ≫ (homologyProjection P hI).f i = P.homologyπ i := by
  let : Projective (Abelian.image (P.d i (c.next i))) := hI i
  let s : (cyclesImageSequence P i (c.next i)).Splitting :=
    cyclesImageSequenceSplitting P i (c.next i) rfl
  let r : P.X i ⟶ P.cycles i := s.r
  let π : P.cycles i ⟶ P.homology i := P.homologyπ i
  have hr : P.iCycles i ≫ r = 𝟙 (P.cycles i) := s.f_r
  change P.iCycles i ≫ (r ≫ π) = π
  exact (Category.assoc (P.iCycles i) r π).symm.trans
    ((congrArg (fun t : P.cycles i ⟶ P.cycles i => t ≫ π) hr).trans
      (Category.id_comp π))

/-- The true original differential gives zero after the projection in every shape. -/
@[reassoc]
lemma d_homologyProjection_f (P : HomologicalComplex C c)
    (hI : ∀ i : ι, Projective (Abelian.image (P.d i (c.next i)))) (i j : ι) :
    P.d i j ≫ (homologyProjection P hI).f j = 0 := by
  let q : P ⟶ homologyZeroComplex P := homologyProjection P hI
  have h : q.f i ≫ (0 : P.homology i ⟶ P.homology j) = P.d i j ≫ q.f j :=
    q.comm i j
  exact h.symm.trans CategoryTheory.Limits.comp_zero

/-- The actual induced homology map is identity after the native zero-complex comparison. -/
@[reassoc]
lemma homologyProjection_homologyMap_hom (P : HomologicalComplex C c)
    (hI : ∀ i : ι, Projective (Abelian.image (P.d i (c.next i)))) (i : ι) :
    homologyMap (homologyProjection P hI) i ≫
        (homologyZeroComplexHomologyIso P i).hom = 𝟙 (P.homology i) := by
  let K : HomologicalComplex C c := homologyZeroComplex P
  let q : P ⟶ K := homologyProjection P hI
  let e : K.homology i ≅ P.homology i := homologyZeroComplexHomologyIso P i
  let π : P.cycles i ⟶ P.homology i := P.homologyπ i
  let π' : K.cycles i ⟶ K.homology i := K.homologyπ i
  let z : P.cycles i ⟶ K.cycles i := cyclesMap q i
  let m : P.homology i ⟶ K.homology i := homologyMap q i
  have hm : π ≫ m = z ≫ π' := homologyπ_naturality q i
  have he : π' ≫ e.hom = K.iCycles i := homologyZeroComplexHomologyIso_π P i
  have hz : z ≫ K.iCycles i = P.iCycles i ≫ q.f i := cyclesMap_i q i
  have hq : P.iCycles i ≫ q.f i = π := iCycles_homologyProjection_f P hI i
  apply (cancel_epi π).1
  change π ≫ (m ≫ e.hom) = π ≫ 𝟙 (P.homology i)
  have hFirst : π ≫ (m ≫ e.hom) = (π ≫ m) ≫ e.hom :=
    (Category.assoc π m e.hom).symm
  have hMap : (π ≫ m) ≫ e.hom = (z ≫ π') ≫ e.hom :=
    congrArg (fun t : P.cycles i ⟶ K.homology i => t ≫ e.hom) hm
  have hAssoc : (z ≫ π') ≫ e.hom = z ≫ (π' ≫ e.hom) :=
    Category.assoc z π' e.hom
  let ιK : K.cycles i ⟶ P.homology i := K.iCycles i
  have hCycle : z ≫ (π' ≫ e.hom) = z ≫ ιK :=
    congrArg (fun t : K.cycles i ⟶ P.homology i => z ≫ t) he
  have hNative : z ≫ ιK = P.iCycles i ≫ q.f i := hz
  have hLast : π = π ≫ 𝟙 (P.homology i) := (Category.comp_id π).symm
  exact hFirst.trans (hMap.trans (hAssoc.trans
    (hCycle.trans (hNative.trans (hq.trans hLast)))))

/-- The induced map is the inverse of the earned native zero-differential comparison. -/
lemma homologyProjection_homologyMap (P : HomologicalComplex C c)
    (hI : ∀ i : ι, Projective (Abelian.image (P.d i (c.next i)))) (i : ι) :
    homologyMap (homologyProjection P hI) i = (homologyZeroComplexHomologyIso P i).inv := by
  let e : (homologyZeroComplex P).homology i ≅ P.homology i :=
    homologyZeroComplexHomologyIso P i
  apply (cancel_mono e.hom).1
  exact (homologyProjection_homologyMap_hom P hI i).trans e.inv_hom_id.symm

/-- Image projectivity alone makes the constructed projection a quasi-isomorphism. -/
lemma quasiIso_homologyProjection (P : HomologicalComplex C c)
    (hI : ∀ i : ι, Projective (Abelian.image (P.d i (c.next i)))) :
    _root_.QuasiIso (homologyProjection P hI) := by
  apply (quasiIso_iff (homologyProjection P hI)).2
  intro i
  apply (quasiIsoAt_iff_isIso_homologyMap (homologyProjection P hI) i).2
  rw [homologyProjection_homologyMap P hI i]
  infer_instance

end AbelianProjection

end HomologicalComplex
