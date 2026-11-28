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
# Zero-differential homology complexes and projective-image projections

The degreewise homology objects of a complex form a complex H(P) with
zero differentials. Its maps are induced homology maps, and H_i(H(P)) is
canonically H_i(P).

In an abelian category, projectivity of every outgoing differential image
splits the cycle–term–image sequence. The resulting cycle retractions give
a morphism P→H(P) inducing isomorphisms in every homology degree.
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

/--
Let C have zero morphisms and homology for all short complexes, and fix an arbitrary complex
shape c. Sending a complex P to H(P), whose terms are Hᵢ(P) and whose differentials vanish,
defines an endofunctor on c-complexes. Its degree-i map on f is the induced map Hᵢ(f).
-/
def homologyZeroComplexFunctor [CategoryWithHomology C] :
    HomologicalComplex C c ⥤ HomologicalComplex C c :=
  (Functor.pi' (fun i : ι => homologyFunctor C c i)) ⋙
    zeroDifferentialFunctor (C := C) c

/--
Let C be a category with zero morphisms and let P be a complex of arbitrary shape c with
homology at every degree. Write H(P) for the complex with term Hᵢ(P) and zero differentials.
The construction retains every original homology object as H(P)ᵢ=Hᵢ(P); all maps H(P).d i j
are zero.
-/
def homologyZeroComplex (P : HomologicalComplex C c) [∀ i, P.HasHomology i] :
    HomologicalComplex C c :=
  (zeroDifferentialFunctor (C := C) c).obj (fun i => P.homology i)

/--
Let C be a category with zero morphisms and let P be a complex of arbitrary shape c with
homology at every degree. Write H(P) for the complex with term Hᵢ(P) and zero differentials.
The complex H(P) itself has homology at every degree i, since its incoming and outgoing
differentials are zero.
-/
instance homologyZeroComplex_hasHomology (P : HomologicalComplex C c)
    [∀ i, P.HasHomology i] (i : ι) : (homologyZeroComplex P).HasHomology i :=
  ShortComplex.HasHomology.mk'
    (ShortComplex.HomologyData.ofZeros ((homologyZeroComplex P).sc i) rfl rfl)

/--
Let C have zero morphisms and homology for all short complexes, and fix an arbitrary complex
shape c. At each c-complex P, the object of the homology-zero-complex functor equals H(P), the
complex of its degreewise homology objects with zero differential.
-/
lemma homologyZeroComplexFunctor_obj [CategoryWithHomology C]
    (P : HomologicalComplex C c) :
    (homologyZeroComplexFunctor (C := C) (c := c)).obj P = homologyZeroComplex P := rfl

/--
Let C have zero morphisms and let f:P→Q be a map of c-complexes, both with homology at every
degree. The induced maps Hᵢ(f):Hᵢ(P)→Hᵢ(Q) assemble into a morphism H(P)→H(Q) of
zero-differential complexes.
-/
def homologyZeroComplexMap {P Q : HomologicalComplex C c}
    [∀ i, P.HasHomology i] [∀ i, Q.HasHomology i] (f : P ⟶ Q) :
    homologyZeroComplex P ⟶ homologyZeroComplex Q :=
  (zeroDifferentialFunctor (C := C) c).map (fun i => homologyMap f i)

/--
Let C have zero morphisms and let f:P→Q be a map of c-complexes, both with homology at every
degree. In every degree i, the component of H(P)→H(Q) is precisely Hᵢ(f).
-/
lemma homologyZeroComplexMap_f {P Q : HomologicalComplex C c}
    [∀ i, P.HasHomology i] [∀ i, Q.HasHomology i] (f : P ⟶ Q) (i : ι) :
    (homologyZeroComplexMap f).f i = homologyMap f i := rfl

/--
Let C be a category with zero morphisms and let P be a complex of arbitrary shape c with
homology at every degree. Write H(P) for the complex with term Hᵢ(P) and zero differentials.
The identity morphism of P induces the identity of H(P): homologyZeroComplexMap(1_P)=1_{H(P)}.
-/
lemma homologyZeroComplexMap_id (P : HomologicalComplex C c)
    [∀ i, P.HasHomology i] :
    homologyZeroComplexMap (𝟙 P) = 𝟙 (homologyZeroComplex P) := by
  apply HomologicalComplex.Hom.ext
  funext i
  exact homologyMap_id P i

/--
Let C have zero morphisms and P,Q,R be c-complexes with homology at every degree. For f:P→Q
and g:Q→R, the induced maps of zero-differential homology complexes satisfy H(f≫g)=H(f)≫H(g).
-/
lemma homologyZeroComplexMap_comp {P Q R : HomologicalComplex C c}
    [∀ i, P.HasHomology i] [∀ i, Q.HasHomology i] [∀ i, R.HasHomology i]
    (f : P ⟶ Q) (g : Q ⟶ R) :
    homologyZeroComplexMap (f ≫ g) = homologyZeroComplexMap f ≫ homologyZeroComplexMap g := by
  apply HomologicalComplex.Hom.ext
  funext i
  exact homologyMap_comp f g i

/--
Let C have zero morphisms and homology for all short complexes, and fix an arbitrary complex
shape c. For f:P→Q, the endofunctor's map is exactly the complex morphism H(P)→H(Q) assembled
from the maps Hᵢ(f).
-/
lemma homologyZeroComplexFunctor_map_eq [CategoryWithHomology C]
    {P Q : HomologicalComplex C c} (f : P ⟶ Q) :
    (homologyZeroComplexFunctor (C := C) (c := c)).map f = homologyZeroComplexMap f := by
  apply HomologicalComplex.Hom.ext
  funext i
  rfl

/--
Let C be a category with zero morphisms and let P be a complex of arbitrary shape c with
homology at every degree. Write H(P) for the complex with term Hᵢ(P) and zero differentials.
At every i, (homologyZeroComplex P).X i = P.homology i; no reindexing or replacement of the
original homology object occurs.
-/
lemma homologyZeroComplex_X (P : HomologicalComplex C c) [∀ j, P.HasHomology j]
    (i : ι) :
    (homologyZeroComplex P).X i = P.homology i := rfl

/--
Let C be a category with zero morphisms and let P be a complex of arbitrary shape c with
homology at every degree. Write H(P) for the complex with term Hᵢ(P) and zero differentials.
At all pairs of indices i,j, the differential of H(P) is zero: H(P).d i j = 0.
-/
lemma homologyZeroComplex_d (P : HomologicalComplex C c) [∀ k, P.HasHomology k]
    (i j : ι) :
    (homologyZeroComplex P).d i j = 0 := rfl

/--
Let C have zero morphisms and homology for all short complexes, and fix an arbitrary complex
shape c. For a morphism f:P→Q of c-complexes, the degree-i component of its image under the
homology-zero-complex functor is Hᵢ(f).
-/
lemma homologyZeroComplexFunctor_map_f [CategoryWithHomology C]
    {P Q : HomologicalComplex C c}
    (f : P ⟶ Q) (i : ι) :
    ((homologyZeroComplexFunctor (C := C) (c := c)).map f).f i =
      homologyMap f i := rfl

/--
Let C be a category with zero morphisms and let P be a complex of arbitrary shape c with
homology at every degree. Write H(P) for the complex with term Hᵢ(P) and zero differentials.
The zero differentials give a canonical isomorphism ηᵢ:Hᵢ(H(P))≅Hᵢ(P), identifying its cycles
and their homology quotient with the original term Hᵢ(P).
-/
def homologyZeroComplexHomologyIso (P : HomologicalComplex C c)
    [∀ j, P.HasHomology j] (i : ι) :
    (homologyZeroComplex P).homology i ≅ P.homology i :=
  let K := homologyZeroComplex P
  (K.isoHomologyπ (c.prev i) i rfl (by rfl)).symm ≪≫
    K.iCyclesIso i (c.next i) rfl (by rfl)

/--
Let C be a category with zero morphisms and let P be a complex of arbitrary shape c with
homology at every degree. Write H(P) for the complex with term Hᵢ(P) and zero differentials.
For ηᵢ:Hᵢ(H(P))≅Hᵢ(P), the homology quotient of H(P) followed by ηᵢ.hom equals its cycle
inclusion into H(P)ᵢ=Hᵢ(P).
-/
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

/--
Let C have zero morphisms and let f:P→Q be a map of c-complexes, both with homology at every
degree. For the canonical identifications η_P,η_Q in degree i, Hᵢ(H(f))≫η_Q.hom =
η_P.hom≫Hᵢ(f). Only the two complexes' degreewise homology existence is required.
-/
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


/--
Let C have zero morphisms and homology for all short complexes, and fix an arbitrary complex
shape c. For f:P→Q and degree i, the canonical identifications η_P:Hᵢ(H(P))≅Hᵢ(P) and
η_Q:Hᵢ(H(Q))≅Hᵢ(Q) satisfy Hᵢ(H(f))≫η_Q.hom=η_P.hom≫Hᵢ(f), for H the homology-zero-complex
functor.
-/
lemma homologyZeroComplexHomologyIso_naturality [CategoryWithHomology C]
    {P Q : HomologicalComplex C c} (f : P ⟶ Q) (i : ι) :
    homologyMap ((homologyZeroComplexFunctor (C := C) (c := c)).map f) i ≫
        (homologyZeroComplexHomologyIso Q i).hom =
      (homologyZeroComplexHomologyIso P i).hom ≫ homologyMap f i :=
  homologyZeroComplexHomologyIso_map_naturality f i

end NativeHomologyComplex

section AbelianProjection

variable [Abelian C]

/--
Let P be a complex of shape c in an abelian category C. Assume the image of P.d i (c.next i)
is projective for every i. For each degree choose the cycle retraction rᵢ:Pᵢ→Zᵢ(P) furnished
by splitting 0→Zᵢ(P)→Pᵢ→im(dᵢ,next(i))→0. The maps rᵢ followed by the homology quotient
πᵢ:Zᵢ(P)→Hᵢ(P) assemble into a morphism Π:P→H(P), where H(P) has zero differentials.
-/
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

/--
Let P be a complex of shape c in an abelian category C. Assume the image of P.d i (c.next i)
is projective for every i. For each degree choose the cycle retraction rᵢ:Pᵢ→Zᵢ(P) furnished
by splitting 0→Zᵢ(P)→Pᵢ→im(dᵢ,next(i))→0. The constructed projection Π:P→H(P) has degree-i
component Π.f i=rᵢ≫πᵢ. The retraction is the one chosen by the outgoing-image short-exact
splitting.
-/
lemma homologyProjection_f (P : HomologicalComplex C c)
    (hI : ∀ i : ι, Projective (Abelian.image (P.d i (c.next i)))) (i : ι) :
    (homologyProjection P hI).f i =
      (letI : Projective (Abelian.image (P.d i (c.next i))) := hI i
       (cyclesImageSequenceSplitting P i (c.next i) rfl).r) ≫ P.homologyπ i := rfl

/--
Let P be a complex of shape c in an abelian category C. Assume the image of P.d i (c.next i)
is projective for every i. For the constructed Π:P→H(P), restricting Π.f i to the cycles gives
their original quotient: P.iCycles i≫Π.f i=P.homologyπ i.
-/
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

/--
Let P be a complex of shape c in an abelian category C. Assume the image of P.d i (c.next i)
is projective for every i. The constructed Π:P→H(P) kills every incoming differential: P.d i
j≫Π.f j=0 for all i,j.
-/
@[reassoc]
lemma d_homologyProjection_f (P : HomologicalComplex C c)
    (hI : ∀ i : ι, Projective (Abelian.image (P.d i (c.next i)))) (i j : ι) :
    P.d i j ≫ (homologyProjection P hI).f j = 0 := by
  let q : P ⟶ homologyZeroComplex P := homologyProjection P hI
  have h : q.f i ≫ (0 : P.homology i ⟶ P.homology j) = P.d i j ≫ q.f j :=
    q.comm i j
  exact h.symm.trans CategoryTheory.Limits.comp_zero

/--
Let P be a complex of shape c in an abelian category C. Assume the image of P.d i (c.next i)
is projective for every i. For Π:P→H(P) and the canonical ηᵢ:Hᵢ(H(P))≅Hᵢ(P), the induced map
satisfies Hᵢ(Π)≫ηᵢ.hom=1_{Hᵢ(P)}.
-/
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

/--
Let P be a complex of shape c in an abelian category C. Assume the image of P.d i (c.next i)
is projective for every i. The map induced by Π:P→H(P) in degree i is ηᵢ.inv, where
ηᵢ:Hᵢ(H(P))≅Hᵢ(P) is the canonical zero-differential identification.
-/
lemma homologyProjection_homologyMap (P : HomologicalComplex C c)
    (hI : ∀ i : ι, Projective (Abelian.image (P.d i (c.next i)))) (i : ι) :
    homologyMap (homologyProjection P hI) i = (homologyZeroComplexHomologyIso P i).inv := by
  let e : (homologyZeroComplex P).homology i ≅ P.homology i :=
    homologyZeroComplexHomologyIso P i
  apply (cancel_mono e.hom).1
  exact (homologyProjection_homologyMap_hom P hI i).trans e.inv_hom_id.symm

/--
Let P be a complex of shape c in an abelian category C. Assume the image of P.d i (c.next i)
is projective for every i. The constructed projection Π:P→H(P) is a quasi-isomorphism, since
it induces the inverse of the canonical isomorphism Hᵢ(H(P))≅Hᵢ(P) at every i. Projectivity of
the terms themselves is not required.
-/
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
