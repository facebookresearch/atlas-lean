/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.Algebra.Homology.HomologicalComplex.SplittingFunctorCoherence
public import MathlibExt.Algebra.Homology.HomologicalComplex.SplitExact

/-!
# Normalized degree projectors and their coherence

The incoming and outgoing native degree projectors are orthogonal. Their
complement is an actual idempotent complex endomorphism, homotopic to identity.
This construction requires only preadditivity, arbitrary complex shape and
independent category/index universes. Homology is needed only for later
identification with the original homology coordinate.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits HomologicalComplex

namespace HomologicalComplex.Splitting

universe u v w uD vD

variable {C : Type u} [Category.{v} C] [Preadditive C]
  {ι : Type w} {c : ComplexShape ι} {K L : HomologicalComplex C c}

/-- The outgoing normalized projector followed by the incoming one is zero. -/
lemma normalize_dNext_comp_prevD (s : Splitting K) (i : ι) :
    dNext i s.normalize.hom ≫ prevD i s.normalize.hom = 0 := by
  change (K.d i (c.next i) ≫ s.normalize.hom (c.next i) i) ≫
    (s.normalize.hom i (c.prev i) ≫ K.d (c.prev i) i) = 0
  calc
    _ = K.d i (c.next i) ≫
        (s.normalize.hom (c.next i) i ≫ s.normalize.hom i (c.prev i)) ≫
          K.d (c.prev i) i := by simp only [Category.assoc]
    _ = 0 := by
      rw [s.normalize_hom_comp_hom]
      simp only [zero_comp, comp_zero]

/-- The incoming normalized projector followed by the outgoing one is zero. -/
lemma normalize_prevD_comp_dNext (s : Splitting K) (i : ι) :
    prevD i s.normalize.hom ≫ dNext i s.normalize.hom = 0 := by
  change (s.normalize.hom i (c.prev i) ≫ K.d (c.prev i) i) ≫
    (K.d i (c.next i) ≫ s.normalize.hom (c.next i) i) = 0
  calc
    _ = s.normalize.hom i (c.prev i) ≫
        (K.d (c.prev i) i ≫ K.d i (c.next i)) ≫
          s.normalize.hom (c.next i) i := by simp only [Category.assoc]
    _ = 0 := by
      rw [K.d_comp_d]
      simp only [zero_comp, comp_zero]

/-- The complementary normalized degree endomorphism, defined without homology objects. -/
def normalizedHomologyProjectorComponent (s : Splitting K) (i : ι) : K.X i ⟶ K.X i :=
  𝟙 (K.X i) - (dNext i s.normalize.hom + prevD i s.normalize.hom)

/-- The complementary degree projector is idempotent in every shape. -/
lemma normalizedHomologyProjectorComponent_idempotent (s : Splitting K) (i : ι) :
    s.normalizedHomologyProjectorComponent i ≫ s.normalizedHomologyProjectorComponent i =
      s.normalizedHomologyProjectorComponent i := by
  have ha : dNext i s.normalize.hom ≫ dNext i s.normalize.hom =
      dNext i s.normalize.hom := s.normalize.d_hom_idempotent i (c.next i)
  have hb : prevD i s.normalize.hom ≫ prevD i s.normalize.hom =
      prevD i s.normalize.hom := s.normalize.hom_d_idempotent i (c.prev i)
  have hab := s.normalize_dNext_comp_prevD i
  have hba := s.normalize_prevD_comp_dNext i
  have hsum : (dNext i s.normalize.hom + prevD i s.normalize.hom) ≫
      (dNext i s.normalize.hom + prevD i s.normalize.hom) =
        dNext i s.normalize.hom + prevD i s.normalize.hom := by
    simp only [Preadditive.add_comp, Preadditive.comp_add, ha, hb, hab, hba,
      zero_add, add_zero]
  exact CategoryTheory.Idempotents.idem_of_id_sub_idem _ hsum

/-- The complementary normalized degree projector is killed by every outgoing differential. -/
@[reassoc]
lemma normalizedHomologyProjectorComponent_d (s : Splitting K) (i j : ι) :
    s.normalizedHomologyProjectorComponent i ≫ K.d i j = 0 := by
  by_cases hij : c.Rel i j
  · have ha : dNext i s.normalize.hom ≫ K.d i j = K.d i j := by
      change (K.d i (c.next i) ≫ s.normalize.hom (c.next i) i) ≫ K.d i j = _
      rw [c.next_eq' hij, Category.assoc]
      exact s.normalize.d_h_d i j
    have hb : prevD i s.normalize.hom ≫ K.d i j = 0 := by
      change (s.normalize.hom i (c.prev i) ≫ K.d (c.prev i) i) ≫ K.d i j = 0
      rw [Category.assoc, K.d_comp_d, comp_zero]
    simp only [normalizedHomologyProjectorComponent, Preadditive.sub_comp,
      Preadditive.add_comp, Category.id_comp, ha, hb, add_zero, sub_self]
  · rw [K.shape i j hij, comp_zero]

/-- Every incoming differential is killed by the complementary normalized degree projector. -/
@[reassoc]
lemma d_normalizedHomologyProjectorComponent (s : Splitting K) (i j : ι) :
    K.d i j ≫ s.normalizedHomologyProjectorComponent j = 0 := by
  by_cases hij : c.Rel i j
  · have ha : K.d i j ≫ dNext j s.normalize.hom = 0 := by
      change K.d i j ≫ (K.d j (c.next j) ≫ s.normalize.hom (c.next j) j) = 0
      rw [← Category.assoc, K.d_comp_d, zero_comp]
    have hb : K.d i j ≫ prevD j s.normalize.hom = K.d i j := by
      change K.d i j ≫ s.normalize.hom j (c.prev j) ≫ K.d (c.prev j) j = _
      rw [c.prev_eq' hij]
      exact s.normalize.d_h_d i j
    simp only [normalizedHomologyProjectorComponent, Preadditive.comp_sub,
      Preadditive.comp_add, Category.comp_id, ha, hb, zero_add, sub_self]
  · rw [K.shape i j hij, zero_comp]

/-- Actual normalized inverse maps earn a complex endomorphism without homology assumptions. -/
def normalizedHomologyProjector (s : Splitting K) : K ⟶ K where
  f := s.normalizedHomologyProjectorComponent
  comm' i j _ := by
    rw [s.normalizedHomologyProjectorComponent_d, s.d_normalizedHomologyProjectorComponent]

/-- The earned complex endomorphism has the complementary native degree formula. -/
@[simp]
lemma normalizedHomologyProjector_f (s : Splitting K) (i : ι) :
    s.normalizedHomologyProjector.f i =
      𝟙 (K.X i) - (dNext i s.normalize.hom + prevD i s.normalize.hom) := rfl

/-- The earned complex endomorphism is idempotent. -/
lemma normalizedHomologyProjector_idempotent (s : Splitting K) :
    s.normalizedHomologyProjector ≫ s.normalizedHomologyProjector =
      s.normalizedHomologyProjector := by
  ext i
  exact s.normalizedHomologyProjectorComponent_idempotent i

/-- Normalized inverse components earn a native homotopy from identity to the projector. -/
def homotopyIdNormalizedHomologyProjector (s : Splitting K) :
    Homotopy (𝟙 K) s.normalizedHomologyProjector where
  hom := s.normalize.hom
  zero := s.normalize.zero
  comm i := by
    rw [HomologicalComplex.id_f, normalizedHomologyProjector_f]
    abel

/-- The actual deformation homotopy retains the normalized inverse family. -/
lemma homotopyIdNormalizedHomologyProjector_hom (s : Splitting K) (i j : ι) :
    s.homotopyIdNormalizedHomologyProjector.hom i j = s.normalize.hom i j := rfl

/-- Native acyclicity makes the earned complementary projector vanish. -/
lemma normalizedHomologyProjector_eq_zero (s : Splitting K) (hK : K.Acyclic) :
    s.normalizedHomologyProjector = 0 := by
  ext i
  simp only [normalizedHomologyProjector_f, HomologicalComplex.zero_f,
    ← s.normalize_sum_id hK i, sub_self]

/-- Outgoing degree projectors are conjugated by actual complex isomorphisms. -/
lemma ofIso_dNext_hom (s : Splitting K) (e : K ≅ L) (i : ι) :
    dNext i (s.ofIso e).hom = e.inv.f i ≫ dNext i s.hom ≫ e.hom.f i := by
  change L.d i (c.next i) ≫ e.inv.f (c.next i) ≫ s.hom (c.next i) i ≫ e.hom.f i =
    e.inv.f i ≫ (K.d i (c.next i) ≫ s.hom (c.next i) i) ≫ e.hom.f i
  rw [← e.inv.comm_assoc i (c.next i)]
  simp only [Category.assoc]

/-- Incoming degree projectors are conjugated by actual complex isomorphisms. -/
lemma ofIso_prevD_hom (s : Splitting K) (e : K ≅ L) (i : ι) :
    prevD i (s.ofIso e).hom = e.inv.f i ≫ prevD i s.hom ≫ e.hom.f i := by
  change (e.inv.f i ≫ s.hom i (c.prev i) ≫ e.hom.f (c.prev i)) ≫ L.d (c.prev i) i =
    e.inv.f i ≫ (s.hom i (c.prev i) ≫ K.d (c.prev i) i) ≫ e.hom.f i
  simp only [Category.assoc]
  rw [e.hom.comm (c.prev i) i]

/-- Isomorphism transport retains the actual complementary normalized degree projector. -/
lemma normalizedHomologyProjectorComponent_ofIso (s : Splitting K) (e : K ≅ L) (i : ι) :
    (s.ofIso e).normalizedHomologyProjectorComponent i =
      e.inv.f i ≫ s.normalizedHomologyProjectorComponent i ≫ e.hom.f i := by
  have hi : e.inv.f i ≫ e.hom.f i = 𝟙 (L.X i) := by
    simpa only [HomologicalComplex.comp_f, HomologicalComplex.id_f] using
      congrArg (fun f : L ⟶ L => f.f i) e.inv_hom_id
  simp only [normalizedHomologyProjectorComponent, ofIso_normalize,
    ofIso_dNext_hom, ofIso_prevD_hom, Preadditive.comp_sub, Preadditive.sub_comp,
    Preadditive.comp_add, Preadditive.add_comp, Category.assoc,
    Category.comp_id, Category.id_comp, hi]

/-- The earned native projector is transported by the actual complex isomorphism. -/
lemma normalizedHomologyProjector_ofIso (s : Splitting K) (e : K ≅ L) :
    e.inv ≫ s.normalizedHomologyProjector ≫ e.hom =
      (s.ofIso e).normalizedHomologyProjector := by
  ext i
  exact (s.normalizedHomologyProjectorComponent_ofIso e i).symm

variable {D : Type uD} [Category.{vD} D] [Preadditive D]

/-- Outgoing native degree projectors commute with a zero-preserving base functor. -/
lemma map_dNext_hom (s : Splitting K) (F : C ⥤ D) [F.PreservesZeroMorphisms] (i : ι) :
    dNext i (s.map F).hom = F.map (dNext i s.hom) := by
  change F.map (K.d i (c.next i)) ≫ F.map (s.hom (c.next i) i) =
    F.map (K.d i (c.next i) ≫ s.hom (c.next i) i)
  rw [Functor.map_comp]

/-- Incoming native degree projectors commute with a zero-preserving base functor. -/
lemma map_prevD_hom (s : Splitting K) (F : C ⥤ D) [F.PreservesZeroMorphisms] (i : ι) :
    prevD i (s.map F).hom = F.map (prevD i s.hom) := by
  change F.map (s.hom i (c.prev i)) ≫ F.map (K.d (c.prev i) i) =
    F.map (s.hom i (c.prev i) ≫ K.d (c.prev i) i)
  rw [Functor.map_comp]

/-- An additive functor maps the actual complementary normalized degree projector. -/
lemma normalizedHomologyProjectorComponent_map (s : Splitting K)
    (F : C ⥤ D) [F.Additive] (i : ι) :
    (s.map F).normalizedHomologyProjectorComponent i =
      F.map (s.normalizedHomologyProjectorComponent i) := by
  simp only [normalizedHomologyProjectorComponent, map_normalize,
    map_dNext_hom, map_prevD_hom, Functor.map_sub, Functor.map_add, F.map_id]
  rfl

/-- An additive functor maps the earned complex projector itself. -/
lemma normalizedHomologyProjector_map (s : Splitting K) (F : C ⥤ D) [F.Additive] :
    (F.mapHomologicalComplex c).map s.normalizedHomologyProjector =
      (s.map F).normalizedHomologyProjector := by
  ext i
  exact (s.normalizedHomologyProjectorComponent_map F i).symm

end HomologicalComplex.Splitting
