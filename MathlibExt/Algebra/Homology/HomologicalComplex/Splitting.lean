/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import Mathlib.Algebra.Homology.Homotopy

/-!
# Generalized-inverse splittings of homological complexes

For a complex K of shape c in a category with zero morphisms, splitting data
are reverse-degree maps h with d h d = d, zero outside the reversed shape.
Isomorphisms and zero-preserving functors transport these data.

In a preadditive category the reflexive normalization r = h d h and the
subsequent normalization n = (1 − d r) r give splittings with n d n = n
and n² = 0. For integer-indexed chain complexes, splitting is equivalently
a family s_n : K_n → K_{n+1} with d_{n+1,n} s_n d_{n+1,n} = d_{n+1,n}.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace HomologicalComplex

universe u v w uD vD

variable {C : Type u} [Category.{v} C]
  {ι : Type w} {c : ComplexShape ι}

section ZeroMorphisms

variable [HasZeroMorphisms C]

/--
Let K be a complex of shape c on an index type ι in a category C with zero morphisms. A
splitting consists of maps hᵢⱼ : Kᵢ → Kⱼ, zero when c.Rel j i fails, such that dᵢⱼ ≫ hⱼᵢ ≫ dᵢⱼ
= dᵢⱼ for every i,j. Thus each allowed differential has a generalized inverse in the opposite
direction; composition is written from left to right with ≫.
This is the generalized-inverse condition for a split complex in Weibel, Definition 1.4.1.
-/
structure Splitting (K : HomologicalComplex C c) where
  /--
  Let K be a complex of shape c on an index type ι in a category C with zero morphisms. The
  components of a splitting are maps hᵢⱼ : Kᵢ → Kⱼ in the direction opposite to the
  differential relation c.Rel j i.
  -/
  hom : ∀ i j : ι, K.X i ⟶ K.X j
  /--
  Let K be a complex of shape c on an index type ι in a category C with zero morphisms. For a
  splitting s, its component s.hom i j vanishes whenever the reverse differential relation
  c.Rel j i does not hold.
  -/
  zero : ∀ i j : ι, ¬c.Rel j i → hom i j = 0
  /--
  Let K be a complex of shape c on an index type ι in a category C with zero morphisms. For a
  splitting s, every differential dᵢⱼ : Kᵢ → Kⱼ satisfies dᵢⱼ ≫ s.hom j i ≫ dᵢⱼ = dᵢⱼ. No
  additive structure is required.
  -/
  d_h_d : ∀ i j : ι, K.d i j ≫ hom j i ≫ K.d i j = K.d i j

/--
Let K be a complex of shape c on an index type ι in a category C with zero morphisms. The
complex is split precisely when there exists a family of reverse-degree maps hᵢⱼ, zero off
c.Rel j i, with dᵢⱼ ≫ hⱼᵢ ≫ dᵢⱼ = dᵢⱼ for all i,j.
-/
def IsSplit (K : HomologicalComplex C c) : Prop :=
  Nonempty (Splitting K)

namespace Splitting

variable {K L M : HomologicalComplex C c}

/--
Let K be a complex of shape c on an index type ι in a category C with zero morphisms. Two
splittings s and t are equal if s.hom i j = t.hom i j for every pair of indices i,j. The
generalized-inverse and support laws are part of both splitting data.
-/
@[ext]
lemma ext {s t : Splitting K} (h : ∀ i j, s.hom i j = t.hom i j) : s = t := by
  cases s
  cases t
  congr
  funext i j
  exact h i j

/--
Let K be a complex of shape c on an index type ι in a category C with zero morphisms. If every
differential K.d i j is zero, the family hᵢⱼ = 0 defines a splitting of K: its reverse support
and d h d = d laws hold at every pair of indices.
-/
def ofZero (h : ∀ i j, K.d i j = 0) : Splitting K where
  hom _ _ := 0
  zero _ _ _ := rfl
  d_h_d i j := by simp only [h i j, comp_zero]

/--
Let K be a complex of shape c on an index type ι in a category C with zero morphisms. Assume
K.d i j = 0 for every i,j. The splitting obtained from this hypothesis has (Splitting.ofZero
h).hom i j = 0 at every pair of indices.
-/
@[simp]
lemma ofZero_hom (h : ∀ i j, K.d i j = 0) (i j : ι) :
    (ofZero h).hom i j = 0 := rfl

/--
Let K be a complex of shape c on an index type ι in a category C with zero morphisms. Let s be
a splitting, with maps hᵢⱼ = s.hom i j : Kᵢ → Kⱼ supported on c.Rel j i and satisfying dᵢⱼ ≫
hⱼᵢ ≫ dᵢⱼ = dᵢⱼ. For all i,j the endomorphism dᵢⱼ ≫ hⱼᵢ of Kᵢ is idempotent: its composite
with itself equals dᵢⱼ ≫ hⱼᵢ.
-/
lemma d_hom_idempotent (s : Splitting K) (i j : ι) :
    (K.d i j ≫ s.hom j i) ≫ (K.d i j ≫ s.hom j i) =
      K.d i j ≫ s.hom j i := by
  calc
    _ = (K.d i j ≫ s.hom j i ≫ K.d i j) ≫ s.hom j i := by
      simp only [Category.assoc]
    _ = K.d i j ≫ s.hom j i := by rw [s.d_h_d i j]

/--
Let K be a complex of shape c on an index type ι in a category C with zero morphisms. Let s be
a splitting, with maps hᵢⱼ = s.hom i j : Kᵢ → Kⱼ supported on c.Rel j i and satisfying dᵢⱼ ≫
hⱼᵢ ≫ dᵢⱼ = dᵢⱼ. For all i,j the endomorphism hᵢⱼ ≫ dⱼᵢ of Kᵢ is idempotent: (hᵢⱼ ≫ dⱼᵢ) ≫
(hᵢⱼ ≫ dⱼᵢ) = hᵢⱼ ≫ dⱼᵢ.
-/
lemma hom_d_idempotent (s : Splitting K) (i j : ι) :
    (s.hom i j ≫ K.d j i) ≫ (s.hom i j ≫ K.d j i) =
      s.hom i j ≫ K.d j i := by
  calc
    _ = s.hom i j ≫ (K.d j i ≫ s.hom i j ≫ K.d j i) := by
      simp only [Category.assoc]
    _ = s.hom i j ≫ K.d j i := by rw [s.d_h_d j i]

/--
Let K be a complex of shape c on an index type ι in a category C with zero morphisms. Let s be
a splitting, with maps hᵢⱼ = s.hom i j : Kᵢ → Kⱼ supported on c.Rel j i and satisfying dᵢⱼ ≫
hⱼᵢ ≫ dᵢⱼ = dᵢⱼ. Replacing each hᵢⱼ by hᵢⱼ ≫ dⱼᵢ ≫ hᵢⱼ gives another splitting, called the
reflexive normalization. Its components remain zero off the reverse relation c.Rel j i and
also satisfy rᵢⱼ ≫ dⱼᵢ ≫ rᵢⱼ = rᵢⱼ.
-/
def reflexive (s : Splitting K) : Splitting K where
  hom i j := s.hom i j ≫ K.d j i ≫ s.hom i j
  zero i j hij := by simp only [s.zero i j hij, comp_zero]
  d_h_d i j := by
    calc
      _ = (K.d i j ≫ s.hom j i ≫ K.d i j) ≫ s.hom j i ≫ K.d i j := by
        simp only [Category.assoc]
      _ = K.d i j ≫ s.hom j i ≫ K.d i j :=
        congrArg (fun a : K.X i ⟶ K.X j => a ≫ s.hom j i ≫ K.d i j) (s.d_h_d i j)
      _ = K.d i j := s.d_h_d i j

/--
Let K be a complex of shape c on an index type ι in a category C with zero morphisms. Let s be
a splitting, with maps hᵢⱼ = s.hom i j : Kᵢ → Kⱼ supported on c.Rel j i and satisfying dᵢⱼ ≫
hⱼᵢ ≫ dᵢⱼ = dᵢⱼ. The component of the reflexive normalization from Kᵢ to Kⱼ is exactly
s.reflexive.hom i j = hᵢⱼ ≫ dⱼᵢ ≫ hᵢⱼ.
-/
lemma reflexive_hom (s : Splitting K) (i j : ι) :
    s.reflexive.hom i j = s.hom i j ≫ K.d j i ≫ s.hom i j := rfl

/--
Let K be a complex of shape c on an index type ι in a category C with zero morphisms. Let s be
a splitting, with maps hᵢⱼ = s.hom i j : Kᵢ → Kⱼ supported on c.Rel j i and satisfying dᵢⱼ ≫
hⱼᵢ ≫ dᵢⱼ = dᵢⱼ. The reflexively normalized component rᵢⱼ = s.reflexive.hom i j satisfies rᵢⱼ
≫ dⱼᵢ ≫ rᵢⱼ = rᵢⱼ for every i,j.
-/
lemma reflexive_h_d_h (s : Splitting K) (i j : ι) :
    s.reflexive.hom i j ≫ K.d j i ≫ s.reflexive.hom i j = s.reflexive.hom i j := by
  dsimp only [reflexive]
  calc
    _ = s.hom i j ≫ (K.d j i ≫ s.hom i j ≫ K.d j i) ≫
        s.hom i j ≫ K.d j i ≫ s.hom i j := by simp only [Category.assoc]
    _ = s.hom i j ≫ K.d j i ≫ s.hom i j ≫ K.d j i ≫ s.hom i j := by
      rw [s.d_h_d j i]
    _ = s.hom i j ≫ (K.d j i ≫ s.hom i j ≫ K.d j i) ≫ s.hom i j := by
      simp only [Category.assoc]
    _ = s.hom i j ≫ K.d j i ≫ s.hom i j := by rw [s.d_h_d j i]

/--
Let K be a complex of shape c on an index type ι in a category C with zero morphisms. Let s be
a splitting, with maps hᵢⱼ = s.hom i j : Kᵢ → Kⱼ supported on c.Rel j i and satisfying dᵢⱼ ≫
hⱼᵢ ≫ dᵢⱼ = dᵢⱼ. Reflexive normalization preserves the differential-first endomorphism: dᵢⱼ ≫
s.reflexive.hom j i = dᵢⱼ ≫ hⱼᵢ for all i,j.
-/
lemma d_reflexive_hom (s : Splitting K) (i j : ι) :
    K.d i j ≫ s.reflexive.hom j i = K.d i j ≫ s.hom j i := by
  change K.d i j ≫ (s.hom j i ≫ K.d i j ≫ s.hom j i) = _
  calc
    _ = (K.d i j ≫ s.hom j i ≫ K.d i j) ≫ s.hom j i := by
      simp only [Category.assoc]
    _ = K.d i j ≫ s.hom j i := by rw [s.d_h_d i j]

/--
Let K be a complex of shape c on an index type ι in a category C with zero morphisms. Let s be
a splitting, with maps hᵢⱼ = s.hom i j : Kᵢ → Kⱼ supported on c.Rel j i and satisfying dᵢⱼ ≫
hⱼᵢ ≫ dᵢⱼ = dᵢⱼ. Reflexive normalization preserves the inverse-first endomorphism:
s.reflexive.hom i j ≫ dⱼᵢ = hᵢⱼ ≫ dⱼᵢ for all i,j.
-/
lemma reflexive_hom_d (s : Splitting K) (i j : ι) :
    s.reflexive.hom i j ≫ K.d j i = s.hom i j ≫ K.d j i := by
  change (s.hom i j ≫ K.d j i ≫ s.hom i j) ≫ K.d j i = _
  calc
    _ = s.hom i j ≫ (K.d j i ≫ s.hom i j ≫ K.d j i) := by
      simp only [Category.assoc]
    _ = s.hom i j ≫ K.d j i := by rw [s.d_h_d j i]

/--
Let K be a complex of shape c on an index type ι in a category C with zero morphisms. Let s be
a splitting, with maps hᵢⱼ = s.hom i j : Kᵢ → Kⱼ supported on c.Rel j i and satisfying dᵢⱼ ≫
hⱼᵢ ≫ dᵢⱼ = dᵢⱼ. For an isomorphism of complexes e : K ≅ L of the same shape, the transported
splitting of L has components e.inv.f i ≫ hᵢⱼ ≫ e.hom.f j. Conjugation preserves both reverse
support and the generalized-inverse law.
-/
def ofIso (s : Splitting K) (e : K ≅ L) : Splitting L where
  hom i j := e.inv.f i ≫ s.hom i j ≫ e.hom.f j
  zero i j hij := by simp only [s.zero i j hij, comp_zero, zero_comp]
  d_h_d i j := by
    have hId : e.inv.f j ≫ e.hom.f j = 𝟙 (L.X j) := by
      have h := congrArg (fun f : L ⟶ L => f.f j) e.inv_hom_id
      simpa only [HomologicalComplex.comp_f, HomologicalComplex.id_f] using h
    calc
      _ = e.inv.f i ≫ (K.d i j ≫ s.hom j i ≫ K.d i j) ≫ e.hom.f j := by
        simp only [Category.assoc]
        rw [← e.inv.comm_assoc i j, e.hom.comm i j]
      _ = e.inv.f i ≫ K.d i j ≫ e.hom.f j := by rw [s.d_h_d i j]
      _ = L.d i j ≫ e.inv.f j ≫ e.hom.f j := by rw [e.inv.comm_assoc i j]
      _ = L.d i j := by rw [hId, Category.comp_id]

/--
Let K be a complex of shape c on an index type ι in a category C with zero morphisms. Let s be
a splitting, with maps hᵢⱼ = s.hom i j : Kᵢ → Kⱼ supported on c.Rel j i and satisfying dᵢⱼ ≫
hⱼᵢ ≫ dᵢⱼ = dᵢⱼ. For a complex isomorphism e : K ≅ L, the transported component is (s.ofIso
e).hom i j = e.inv.f i ≫ hᵢⱼ ≫ e.hom.f j : Lᵢ → Lⱼ.
-/
lemma ofIso_hom (s : Splitting K) (e : K ≅ L) (i j : ι) :
    (s.ofIso e).hom i j = e.inv.f i ≫ s.hom i j ≫ e.hom.f j := rfl

/--
Let K be a complex of shape c on an index type ι in a category C with zero morphisms. Let s be
a splitting, with maps hᵢⱼ = s.hom i j : Kᵢ → Kⱼ supported on c.Rel j i and satisfying dᵢⱼ ≫
hⱼᵢ ≫ dᵢⱼ = dᵢⱼ. Transporting s along the identity isomorphism of K leaves the splitting
unchanged: s.ofIso (Iso.refl K) = s.
-/
@[simp]
lemma ofIso_refl (s : Splitting K) : s.ofIso (Iso.refl K) = s := by
  ext i j
  simp only [ofIso, Iso.refl_inv, Iso.refl_hom, HomologicalComplex.id_f,
    Category.id_comp, Category.comp_id]

/--
Let K be a complex of shape c on an index type ι in a category C with zero morphisms. Let s be
a splitting, with maps hᵢⱼ = s.hom i j : Kᵢ → Kⱼ supported on c.Rel j i and satisfying dᵢⱼ ≫
hⱼᵢ ≫ dᵢⱼ = dᵢⱼ. For complex isomorphisms e : K ≅ L and f : L ≅ M, successive transport agrees
with transport along their composite: (s.ofIso e).ofIso f = s.ofIso (e ≪≫ f).
-/
lemma ofIso_trans (s : Splitting K) (e : K ≅ L) (f : L ≅ M) :
    (s.ofIso e).ofIso f = s.ofIso (e ≪≫ f) := by
  ext i j
  simp only [ofIso, Iso.trans_inv, Iso.trans_hom, HomologicalComplex.comp_f, Category.assoc]

variable {D : Type uD} [Category.{vD} D] [HasZeroMorphisms D]

/--
Let K be a complex of shape c on an index type ι in a category C with zero morphisms. Let s be
a splitting, with maps hᵢⱼ = s.hom i j : Kᵢ → Kⱼ supported on c.Rel j i and satisfying dᵢⱼ ≫
hⱼᵢ ≫ dᵢⱼ = dᵢⱼ. Let D also have zero morphisms and let F : C ⥤ D preserve them. Applying F to
every hᵢⱼ produces a splitting of the complex with terms F(Kᵢ) and differentials F(dᵢⱼ); no
additivity assumption on F is needed.
-/
def map (s : Splitting K) (F : C ⥤ D) [F.PreservesZeroMorphisms] :
    Splitting ((F.mapHomologicalComplex c).obj K) where
  hom i j := F.map (s.hom i j)
  zero i j hij := by rw [s.zero i j hij, F.map_zero]
  d_h_d i j := by
    change F.map (K.d i j) ≫ F.map (s.hom j i) ≫ F.map (K.d i j) = F.map (K.d i j)
    rw [← F.map_comp, ← F.map_comp, s.d_h_d i j]

/--
Let K be a complex of shape c on an index type ι in a category C with zero morphisms. Let s be
a splitting, with maps hᵢⱼ = s.hom i j : Kᵢ → Kⱼ supported on c.Rel j i and satisfying dᵢⱼ ≫
hⱼᵢ ≫ dᵢⱼ = dᵢⱼ. For a zero-morphism-preserving functor F : C ⥤ D into another category with
zero morphisms, the induced splitting of F(K) has component (s.map F).hom i j = F.map (hᵢⱼ).
-/
lemma map_hom (s : Splitting K) (F : C ⥤ D) [F.PreservesZeroMorphisms] (i j : ι) :
    (s.map F).hom i j = F.map (s.hom i j) := rfl

end Splitting

/--
Let K be a complex of shape c on an index type ι in a category C with zero morphisms. If K.d i
j = 0 for all i,j, then K is split, as witnessed by the zero family of reverse-degree maps.
-/
lemma isSplit_of_d_eq_zero {K : HomologicalComplex C c} (h : ∀ i j, K.d i j = 0) :
    IsSplit K :=
  ⟨Splitting.ofZero h⟩

/--
Let K be a complex of shape c on an index type ι in a category C with zero morphisms. For an
isomorphism e : K ≅ L of complexes of shape c, K admits a generalized-inverse splitting if and
only if L does. Transport uses conjugation by the components of e.
-/
lemma isSplit_iff_of_iso {K L : HomologicalComplex C c} (e : K ≅ L) :
    IsSplit K ↔ IsSplit L := by
  constructor
  · rintro ⟨s⟩
    exact ⟨s.ofIso e⟩
  · rintro ⟨s⟩
    exact ⟨s.ofIso e.symm⟩

/--
Let K be a complex of shape c on an index type ι in a category C with zero morphisms. Assume K
admits a splitting and let F : C ⥤ D preserve zero morphisms, where D is another category with
zero morphisms. The complex with terms F(Kᵢ) and differentials F(dᵢⱼ) also admits a splitting.
-/
lemma IsSplit.map {K : HomologicalComplex C c} (h : IsSplit K)
    {D : Type uD} [Category.{vD} D] [HasZeroMorphisms D]
    (F : C ⥤ D) [F.PreservesZeroMorphisms] :
    IsSplit ((F.mapHomologicalComplex c).obj K) := by
  obtain ⟨s⟩ := h
  exact ⟨s.map F⟩

end ZeroMorphisms

section Preadditive

variable [Preadditive C]

namespace Splitting

variable {K : HomologicalComplex C c}

/--
Let K be a complex of shape c in a preadditive category C, and let s be a splitting with
components hᵢⱼ : Kᵢ → Kⱼ in the reversed degrees. Write rᵢⱼ = hᵢⱼ ≫ dⱼᵢ ≫ hᵢⱼ for the
reflexive normalization. The normalized splitting has nᵢⱼ = (1_{Kᵢ} − dᵢ,next(i) ≫
r_next(i),i) ≫ rᵢⱼ. It satisfies d n d = d, n d n = n, and every composite nᵢⱼ ≫ nⱼₖ is zero.
-/
noncomputable def normalize (s : Splitting K) : Splitting K where
  hom i j :=
    (𝟙 (K.X i) - K.d i (c.next i) ≫ s.reflexive.hom (c.next i) i) ≫
      s.reflexive.hom i j
  zero i j hij := by
    rw [s.reflexive.zero i j hij, comp_zero]
  d_h_d i j := by
    have h : K.d i j ≫
        (𝟙 (K.X j) - K.d j (c.next j) ≫ s.reflexive.hom (c.next j) j) = K.d i j := by
      simp only [Preadditive.comp_sub, Category.comp_id, ← Category.assoc,
        K.d_comp_d, zero_comp, sub_zero]
    calc
      _ = (K.d i j ≫
          (𝟙 (K.X j) - K.d j (c.next j) ≫ s.reflexive.hom (c.next j) j)) ≫
            s.reflexive.hom j i ≫ K.d i j := by simp only [Category.assoc]
      _ = K.d i j ≫ s.reflexive.hom j i ≫ K.d i j := by rw [h]
      _ = K.d i j := s.reflexive.d_h_d i j

/--
Let K be a complex of shape c in a preadditive category C, and let s be a splitting with
components hᵢⱼ : Kᵢ → Kⱼ in the reversed degrees. Write rᵢⱼ = hᵢⱼ ≫ dⱼᵢ ≫ hᵢⱼ for the
reflexive normalization. For all i,j the normalized component is s.normalize.hom i j = (1_{Kᵢ}
− dᵢ,next(i) ≫ r_next(i),i) ≫ rᵢⱼ. Here next(i) is the successor selected by the complex
shape.
-/
lemma normalize_hom (s : Splitting K) (i j : ι) :
    s.normalize.hom i j =
      (𝟙 (K.X i) - K.d i (c.next i) ≫ s.reflexive.hom (c.next i) i) ≫
        s.reflexive.hom i j := rfl

/--
Let K be a complex of shape c in a preadditive category C, and let s be a splitting with
components hᵢⱼ : Kᵢ → Kⱼ in the reversed degrees. Write rᵢⱼ = hᵢⱼ ≫ dⱼᵢ ≫ hᵢⱼ for the
reflexive normalization. For nᵢⱼ = s.normalize.hom i j, the normalized splitting satisfies nᵢⱼ
≫ dⱼᵢ ≫ nᵢⱼ = nᵢⱼ at every pair of indices.
-/
lemma normalize_h_d_h (s : Splitting K) (i j : ι) :
    s.normalize.hom i j ≫ K.d j i ≫ s.normalize.hom i j = s.normalize.hom i j := by
  let a : K.X i ⟶ K.X i :=
    𝟙 (K.X i) - K.d i (c.next i) ≫ s.reflexive.hom (c.next i) i
  have hd : K.d j i ≫ a = K.d j i := by
    dsimp only [a]
    simp only [Preadditive.comp_sub, Category.comp_id, ← Category.assoc,
      K.d_comp_d, zero_comp, sub_zero]
  change (a ≫ s.reflexive.hom i j) ≫ K.d j i ≫
      (a ≫ s.reflexive.hom i j) = a ≫ s.reflexive.hom i j
  calc
    _ = a ≫ s.reflexive.hom i j ≫ (K.d j i ≫ a) ≫ s.reflexive.hom i j := by
      simp only [Category.assoc]
    _ = a ≫ s.reflexive.hom i j ≫ K.d j i ≫ s.reflexive.hom i j := by rw [hd]
    _ = a ≫ (s.reflexive.hom i j ≫ K.d j i ≫ s.reflexive.hom i j) := rfl
    _ = a ≫ s.reflexive.hom i j := by rw [s.reflexive_h_d_h i j]

/--
Let K be a complex of shape c in a preadditive category C, and let s be a splitting with
components hᵢⱼ : Kᵢ → Kⱼ in the reversed degrees. Write rᵢⱼ = hᵢⱼ ≫ dⱼᵢ ≫ hᵢⱼ for the
reflexive normalization. Every consecutive pair of normalized reverse-degree maps has zero
composite: s.normalize.hom i j ≫ s.normalize.hom j k = 0 for all i,j,k. The statement also
includes components outside the reverse shape, which are zero.
-/
lemma normalize_hom_comp_hom (s : Splitting K) (i j k : ι) :
    s.normalize.hom i j ≫ s.normalize.hom j k = 0 := by
  by_cases hij : c.Rel j i
  · have hnext : c.next j = i := c.next_eq' hij
    have hzero : s.reflexive.hom i j ≫
        (𝟙 (K.X j) - K.d j i ≫ s.reflexive.hom i j) = 0 := by
      rw [Preadditive.comp_sub, Category.comp_id]
      rw [s.reflexive_h_d_h i j, sub_self]
    change
      ((𝟙 (K.X i) - K.d i (c.next i) ≫ s.reflexive.hom (c.next i) i) ≫
        s.reflexive.hom i j) ≫
      ((𝟙 (K.X j) - K.d j (c.next j) ≫ s.reflexive.hom (c.next j) j) ≫
        s.reflexive.hom j k) = 0
    rw [hnext]
    calc
      _ = (𝟙 (K.X i) - K.d i (c.next i) ≫
          s.reflexive.hom (c.next i) i) ≫
            (s.reflexive.hom i j ≫
              (𝟙 (K.X j) - K.d j i ≫ s.reflexive.hom i j)) ≫
                s.reflexive.hom j k := by simp only [Category.assoc]
      _ = 0 := by
        rw [hzero]
        simp only [zero_comp, comp_zero]
  · rw [s.normalize.zero i j hij, zero_comp]

end Splitting

end Preadditive

end HomologicalComplex


namespace ChainComplex

section IntegerSplittingFamily

universe uChain vChain

variable {C : Type uChain} [Category.{vChain} C] [HasZeroMorphisms C]

/--
Let K be an integer-indexed chain complex in a category C with zero morphisms, with
differential d_{n+1,n} : K_{n+1} → K_n. A family s_n : K_n → K_{n+1} satisfying d_{n+1,n} =
d_{n+1,n} ≫ s_n ≫ d_{n+1,n} for every integer n determines a splitting. Its component n→n+1 is
s_n and all other reverse-degree components are zero.
-/
def splittingOfDegreeOneHom (K : ChainComplex C ℤ)
    (s : ∀ n : ℤ, K.X n ⟶ K.X (n + 1))
    (hs : ∀ n : ℤ, K.d (n + 1) n = K.d (n + 1) n ≫ s n ≫ K.d (n + 1) n) :
    HomologicalComplex.Splitting K where
  hom i j := if h : i + 1 = j then s i ≫ eqToHom (congrArg K.X h) else 0
  zero i j hij := by
    change ¬ i + 1 = j at hij
    exact dite_eq_right hij
  d_h_d i j := by
    by_cases h : j + 1 = i
    · subst i
      simp only [dite_eq_left rfl, eqToHom_refl, Category.comp_id]
      exact (hs j).symm
    · have hd : K.d i j = 0 := K.shape i j h
      simp only [hd, comp_zero]

/--
Let K be an integer-indexed chain complex in a category C with zero morphisms, with
differential d_{n+1,n} : K_{n+1} → K_n. For a family s_n : K_n → K_{n+1} with d_{n+1,n} =
d_{n+1,n} ≫ s_n ≫ d_{n+1,n} at every integer n, the constructed splitting has component
(splittingOfDegreeOneHom K s hs).hom n (n+1) = s_n.
-/
lemma splittingOfDegreeOneHom_hom_succ (K : ChainComplex C ℤ)
    (s : ∀ n : ℤ, K.X n ⟶ K.X (n + 1))
    (hs : ∀ n : ℤ, K.d (n + 1) n = K.d (n + 1) n ≫ s n ≫ K.d (n + 1) n)
    (n : ℤ) :
    (splittingOfDegreeOneHom K s hs).hom n (n + 1) = s n := by
  change (if h : n + 1 = n + 1 then s n ≫ eqToHom (congrArg K.X h) else 0) = s n
  simp only [dite_eq_left rfl, eqToHom_refl, Category.comp_id]

/--
Let K be an integer-indexed chain complex in a category C with zero morphisms, with
differential d_{n+1,n} : K_{n+1} → K_n. The complex is split if and only if there exists a
family s_n : K_n → K_{n+1} with d_{n+1,n} = d_{n+1,n} ≫ s_n ≫ d_{n+1,n} for all n ∈ ℤ.
-/
theorem isSplit_iff_exists_degreeOneHom (K : ChainComplex C ℤ) :
    HomologicalComplex.IsSplit K ↔
      ∃ s : ∀ n : ℤ, K.X n ⟶ K.X (n + 1),
        ∀ n : ℤ, K.d (n + 1) n = K.d (n + 1) n ≫ s n ≫ K.d (n + 1) n := by
  constructor
  · rintro ⟨s⟩
    exact ⟨fun n => s.hom n (n + 1), fun n => (s.d_h_d (n + 1) n).symm⟩
  · rintro ⟨s, hs⟩
    exact ⟨splittingOfDegreeOneHom K s hs⟩

end IntegerSplittingFamily

end ChainComplex

namespace HomologicalComplex

universe uEdge vEdge wEdge

variable {C : Type uEdge} [Category.{vEdge} C] [HasZeroMorphisms C]
  {ι : Type wEdge} {c : ComplexShape ι} {K : HomologicalComplex C c}

/--
Let K be a complex of shape c on an index type ι in a category C with zero morphisms. Assume
that for every allowed differential dᵢⱼ there exists gⱼᵢ : Kⱼ → Kᵢ with dᵢⱼ ≫ gⱼᵢ ≫ dᵢⱼ = dᵢⱼ.
Selecting one such inverse on each edge and setting all other components to zero defines a
splitting of K.
-/
noncomputable def Splitting.ofEdgewise
    (h : ∀ i j, c.Rel i j → ∃ s : K.X j ⟶ K.X i,
      K.d i j ≫ s ≫ K.d i j = K.d i j) : Splitting K := by
  classical
  exact {
    hom := fun i j => if hij : c.Rel j i then Classical.choose (h j i hij) else 0
    zero := fun i j hij => by simp only [dite_eq_right hij]
    d_h_d := fun i j => by
      by_cases hij : c.Rel i j
      · simp only [dite_eq_left hij]
        exact Classical.choose_spec (h i j hij)
      · simp only [K.shape i j hij, comp_zero] }

/--
Let K be a complex of shape c on an index type ι in a category C with zero morphisms. Assume
each allowed differential has a generalized inverse, and form the splitting by selecting one
inverse for each edge. If c.Rel j i, its component from Kᵢ to Kⱼ is the inverse selected from
the hypothesis for dⱼᵢ.
-/
theorem Splitting.ofEdgewise_hom_of_rel
    (h : ∀ i j, c.Rel i j → ∃ s : K.X j ⟶ K.X i,
      K.d i j ≫ s ≫ K.d i j = K.d i j)
    (i j : ι) (hij : c.Rel j i) :
    (Splitting.ofEdgewise h).hom i j = Classical.choose (h j i hij) := by
  classical
  change (if hji : c.Rel j i then Classical.choose (h j i hji) else 0) = _
  rw [dite_eq_left hij]

/--
Let K be a complex of shape c on an index type ι in a category C with zero morphisms. The
complex is split if and only if, for every pair i,j with c.Rel i j, there exists g : Kⱼ → Kᵢ
such that dᵢⱼ ≫ g ≫ dᵢⱼ = dᵢⱼ. No condition on disallowed differentials is needed beyond the
complex-shape law.
-/
theorem isSplit_iff_edgewise (K : HomologicalComplex C c) :
    IsSplit K ↔ ∀ i j, c.Rel i j → ∃ s : K.X j ⟶ K.X i,
      K.d i j ≫ s ≫ K.d i j = K.d i j := by
  constructor
  · rintro ⟨s⟩ i j hij
    exact ⟨s.hom j i, s.d_h_d i j⟩
  · intro h
    exact ⟨Splitting.ofEdgewise h⟩

end HomologicalComplex
