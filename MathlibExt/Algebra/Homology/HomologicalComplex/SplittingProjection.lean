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
# Normalized complementary projectors of split complexes

A splitting in a preadditive category yields normalized outgoing and
incoming idempotents D_i and B_i. Their cross-composites vanish, so
P_i=1−D_i−B_i is an idempotent that kills every differential and forms
a complex endomorphism homotopic to the identity.

These projectors are compatible with complex isomorphisms and additive
functors. Acyclicity makes the complementary projector zero.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits HomologicalComplex

namespace HomologicalComplex.Splitting

universe u v w uD vD

variable {C : Type u} [Category.{v} C] [Preadditive C]
  {ι : Type w} {c : ComplexShape ι} {K L : HomologicalComplex C c}

/--
Let K be a complex of arbitrary shape c in a preadditive category C and let s be a splitting.
With n=s.normalize.hom, set Dᵢ=dᵢ,next(i)≫n_next(i),i, Bᵢ=n_i,prev(i)≫d_prev(i),i and
Pᵢ=1_{Kᵢ}−(Dᵢ+Bᵢ). The normalized outgoing and incoming projectors are orthogonal: Dᵢ≫Bᵢ=0 at
every i.
-/
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

/--
Let K be a complex of arbitrary shape c in a preadditive category C and let s be a splitting.
With n=s.normalize.hom, set Dᵢ=dᵢ,next(i)≫n_next(i),i, Bᵢ=n_i,prev(i)≫d_prev(i),i and
Pᵢ=1_{Kᵢ}−(Dᵢ+Bᵢ). The incoming and outgoing projectors are orthogonal in the reverse order as
well: Bᵢ≫Dᵢ=0.
-/
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

/--
Let K be a complex of arbitrary shape c in a preadditive category C and let s be a splitting.
With n=s.normalize.hom, set Dᵢ=dᵢ,next(i)≫n_next(i),i, Bᵢ=n_i,prev(i)≫d_prev(i),i and
Pᵢ=1_{Kᵢ}−(Dᵢ+Bᵢ). The complementary degree endomorphism is Pᵢ. It is defined solely from the
splitting and differentials, without requiring a homology object at i.
-/
def normalizedHomologyProjectorComponent (s : Splitting K) (i : ι) : K.X i ⟶ K.X i :=
  𝟙 (K.X i) - (dNext i s.normalize.hom + prevD i s.normalize.hom)

/--
Let K be a complex of arbitrary shape c in a preadditive category C and let s be a splitting.
With n=s.normalize.hom, set Dᵢ=dᵢ,next(i)≫n_next(i),i, Bᵢ=n_i,prev(i)≫d_prev(i),i and
Pᵢ=1_{Kᵢ}−(Dᵢ+Bᵢ). At every degree i, Pᵢ≫Pᵢ=Pᵢ. The identity follows from the idempotence and
mutual orthogonality of Dᵢ and Bᵢ.
-/
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

/--
Let K be a complex of arbitrary shape c in a preadditive category C and let s be a splitting.
With n=s.normalize.hom, set Dᵢ=dᵢ,next(i)≫n_next(i),i, Bᵢ=n_i,prev(i)≫d_prev(i),i and
Pᵢ=1_{Kᵢ}−(Dᵢ+Bᵢ). For every i,j, Pᵢ≫K.d i j=0: the normalized complementary coordinate lies
in the cycles.
-/
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

/--
Let K be a complex of arbitrary shape c in a preadditive category C and let s be a splitting.
With n=s.normalize.hom, set Dᵢ=dᵢ,next(i)≫n_next(i),i, Bᵢ=n_i,prev(i)≫d_prev(i),i and
Pᵢ=1_{Kᵢ}−(Dᵢ+Bᵢ). For every i,j, K.d i j≫Pⱼ=0: the complementary coordinate kills the
incoming boundaries.
-/
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

/--
Let K be a complex of arbitrary shape c in a preadditive category C and s a splitting. Set
n=s.normalize.hom, Dᵢ=dᵢ,next(i)≫n_next(i),i, Bᵢ=n_i,prev(i)≫d_prev(i),i and Pᵢ=1−(Dᵢ+Bᵢ). The
maps Pᵢ form a complex endomorphism because Pᵢ≫dᵢⱼ=dᵢⱼ≫Pⱼ=0. No homology existence is assumed.
-/
def normalizedHomologyProjector (s : Splitting K) : K ⟶ K where
  f := s.normalizedHomologyProjectorComponent
  comm' i j _ := by
    rw [s.normalizedHomologyProjectorComponent_d, s.d_normalizedHomologyProjectorComponent]

/--
Let K be a complex of arbitrary shape c in a preadditive category C and let s be a splitting.
With n=s.normalize.hom, set Dᵢ=dᵢ,next(i)≫n_next(i),i, Bᵢ=n_i,prev(i)≫d_prev(i),i and
Pᵢ=1_{Kᵢ}−(Dᵢ+Bᵢ). The degree-i component of the resulting complex endomorphism is exactly
1_{Kᵢ}−(Dᵢ+Bᵢ).
-/
@[simp]
lemma normalizedHomologyProjector_f (s : Splitting K) (i : ι) :
    s.normalizedHomologyProjector.f i =
      𝟙 (K.X i) - (dNext i s.normalize.hom + prevD i s.normalize.hom) := rfl

/--
Let K be a complex of arbitrary shape c in a preadditive category C and let s be a splitting.
With n=s.normalize.hom, set Dᵢ=dᵢ,next(i)≫n_next(i),i, Bᵢ=n_i,prev(i)≫d_prev(i),i and
Pᵢ=1_{Kᵢ}−(Dᵢ+Bᵢ). For the complex endomorphism P with components Pᵢ, P≫P=P.
-/
lemma normalizedHomologyProjector_idempotent (s : Splitting K) :
    s.normalizedHomologyProjector ≫ s.normalizedHomologyProjector =
      s.normalizedHomologyProjector := by
  ext i
  exact s.normalizedHomologyProjectorComponent_idempotent i

/--
Let K be a complex of arbitrary shape c in a preadditive category C and let s be a splitting.
With n=s.normalize.hom, set Dᵢ=dᵢ,next(i)≫n_next(i),i, Bᵢ=n_i,prev(i)≫d_prev(i),i and
Pᵢ=1_{Kᵢ}−(Dᵢ+Bᵢ). The family n supplies a homotopy 1_K∼P, since 1_{Kᵢ}=Pᵢ+Dᵢ+Bᵢ at every i.
-/
def homotopyIdNormalizedHomologyProjector (s : Splitting K) :
    Homotopy (𝟙 K) s.normalizedHomologyProjector where
  hom := s.normalize.hom
  zero := s.normalize.zero
  comm i := by
    rw [HomologicalComplex.id_f, normalizedHomologyProjector_f]
    abel

/--
Let K be a complex of arbitrary shape c in a preadditive category C and let s be a splitting.
With n=s.normalize.hom, set Dᵢ=dᵢ,next(i)≫n_next(i),i, Bᵢ=n_i,prev(i)≫d_prev(i),i and
Pᵢ=1_{Kᵢ}−(Dᵢ+Bᵢ). The component of the homotopy 1_K∼P from degree i to reversed degree j is
nᵢⱼ=s.normalize.hom i j.
-/
lemma homotopyIdNormalizedHomologyProjector_hom (s : Splitting K) (i j : ι) :
    s.homotopyIdNormalizedHomologyProjector.hom i j = s.normalize.hom i j := rfl

/--
Let K be a complex of arbitrary shape c in a preadditive category C and let s be a splitting.
With n=s.normalize.hom, set Dᵢ=dᵢ,next(i)≫n_next(i),i, Bᵢ=n_i,prev(i)≫d_prev(i),i and
Pᵢ=1_{Kᵢ}−(Dᵢ+Bᵢ). If K is acyclic, meaning every degreewise short complex is exact, the
complex endomorphism P is zero.
-/
lemma normalizedHomologyProjector_eq_zero (s : Splitting K) (hK : K.Acyclic) :
    s.normalizedHomologyProjector = 0 := by
  ext i
  simp only [normalizedHomologyProjector_f, HomologicalComplex.zero_f,
    ← s.normalize_sum_id hK i, sub_self]

/--
Let K,L be c-complexes in a preadditive category C, s a splitting of K and e:K≅L a complex
isomorphism. The differential-first projector of the transported splitting satisfies dNext
i(s.ofIso e).hom = e.inv.f i≫dNext i s.hom≫e.hom.f i.
-/
lemma ofIso_dNext_hom (s : Splitting K) (e : K ≅ L) (i : ι) :
    dNext i (s.ofIso e).hom = e.inv.f i ≫ dNext i s.hom ≫ e.hom.f i := by
  change L.d i (c.next i) ≫ e.inv.f (c.next i) ≫ s.hom (c.next i) i ≫ e.hom.f i =
    e.inv.f i ≫ (K.d i (c.next i) ≫ s.hom (c.next i) i) ≫ e.hom.f i
  rw [← e.inv.comm_assoc i (c.next i)]
  simp only [Category.assoc]

/--
Let K,L be c-complexes in a preadditive category C, s a splitting of K and e:K≅L a complex
isomorphism. The inverse-first projector of the transported splitting satisfies prevD
i(s.ofIso e).hom = e.inv.f i≫prevD i s.hom≫e.hom.f i.
-/
lemma ofIso_prevD_hom (s : Splitting K) (e : K ≅ L) (i : ι) :
    prevD i (s.ofIso e).hom = e.inv.f i ≫ prevD i s.hom ≫ e.hom.f i := by
  change (e.inv.f i ≫ s.hom i (c.prev i) ≫ e.hom.f (c.prev i)) ≫ L.d (c.prev i) i =
    e.inv.f i ≫ (s.hom i (c.prev i) ≫ K.d (c.prev i) i) ≫ e.hom.f i
  simp only [Category.assoc]
  rw [e.hom.comm (c.prev i) i]

/--
Let K,L be c-complexes in a preadditive category C, s a splitting of K and e:K≅L a complex
isomorphism. If Pᵢ is the complementary normalized projector for s, its counterpart on L is
e.inv.f i≫Pᵢ≫e.hom.f i.
-/
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

/--
Let K,L be c-complexes in a preadditive category C, s a splitting of K and e:K≅L a complex
isomorphism. For the normalized complex projector P_s, the transported projector is
e.inv≫P_s≫e.hom = P_{s.ofIso e}.
-/
lemma normalizedHomologyProjector_ofIso (s : Splitting K) (e : K ≅ L) :
    e.inv ≫ s.normalizedHomologyProjector ≫ e.hom =
      (s.ofIso e).normalizedHomologyProjector := by
  ext i
  exact (s.normalizedHomologyProjectorComponent_ofIso e i).symm

variable {D : Type uD} [Category.{vD} D] [Preadditive D]

/--
Let C,D be preadditive categories, K a c-complex in C, s a splitting of K and F:C⥤D a functor
preserving zero morphisms. The differential-first endomorphism formed from the mapped
splitting is dNext i(s.map F).hom = F.map(dNext i s.hom).
-/
lemma map_dNext_hom (s : Splitting K) (F : C ⥤ D) [F.PreservesZeroMorphisms] (i : ι) :
    dNext i (s.map F).hom = F.map (dNext i s.hom) := by
  change F.map (K.d i (c.next i)) ≫ F.map (s.hom (c.next i) i) =
    F.map (K.d i (c.next i) ≫ s.hom (c.next i) i)
  rw [Functor.map_comp]

/--
Let C,D be preadditive categories, K a c-complex in C, s a splitting of K and F:C⥤D a functor
preserving zero morphisms. The inverse-first endomorphism formed from the mapped splitting is
prevD i(s.map F).hom = F.map(prevD i s.hom).
-/
lemma map_prevD_hom (s : Splitting K) (F : C ⥤ D) [F.PreservesZeroMorphisms] (i : ι) :
    prevD i (s.map F).hom = F.map (prevD i s.hom) := by
  change F.map (s.hom i (c.prev i)) ≫ F.map (K.d (c.prev i) i) =
    F.map (s.hom i (c.prev i) ≫ K.d (c.prev i) i)
  rw [Functor.map_comp]

/--
Let C,D be preadditive categories, K a c-complex with splitting s, and F:C⥤D an additive
functor. The complementary normalized degree projector of s.map F is F(Pᵢ), where Pᵢ=1−dNext i
s.normalize.hom−prevD i s.normalize.hom.
-/
lemma normalizedHomologyProjectorComponent_map (s : Splitting K)
    (F : C ⥤ D) [F.Additive] (i : ι) :
    (s.map F).normalizedHomologyProjectorComponent i =
      F.map (s.normalizedHomologyProjectorComponent i) := by
  simp only [normalizedHomologyProjectorComponent, map_normalize,
    map_dNext_hom, map_prevD_hom, Functor.map_sub, Functor.map_add, F.map_id]
  rfl

/--
Let C,D be preadditive categories, K a c-complex with splitting s, and F:C⥤D an additive
functor. Applying F termwise to the normalized projector P_s:K→K gives the normalized
projector of the mapped splitting: F(P_s)=P_{s.map F}.
-/
lemma normalizedHomologyProjector_map (s : Splitting K) (F : C ⥤ D) [F.Additive] :
    (F.mapHomologicalComplex c).map s.normalizedHomologyProjector =
      (s.map F).normalizedHomologyProjector := by
  ext i
  exact (s.normalizedHomologyProjectorComponent_map F i).symm

end HomologicalComplex.Splitting
