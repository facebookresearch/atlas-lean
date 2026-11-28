/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Authors: @toskua, Codex
-/

module

public import Mathlib.Algebra.Homology.HomologicalComplex
public import Mathlib.CategoryTheory.Limits.Shapes.BinaryBiproducts

/-!
# Cofree complexes with endpoint terms

Let C have zero morphisms, a zero object and binary biproducts. Let c be a
complex shape on an arbitrary index type ι,
and I : ι → C a family of objects. Put Eᵢ = I(c.next i) when c has an outgoing
edge at i, and Eᵢ = 0 otherwise. The cofree complex D(I) has terms
D(I)ᵢ = Iᵢ ⊕ Eᵢ. Along an edge i → j, its differential projects onto Eᵢ,
identifies that object with Iⱼ and includes it as the first summand of D(I)ⱼ.
Successive differentials compose to zero.

For any c-shaped complex K, morphisms K → D(I) correspond bijectively to
arbitrary families aᵢ : Kᵢ → Iᵢ. The first component is aᵢ, and the second
component along i → j is dᵏᵢⱼ followed by aⱼ. At an index without an outgoing
edge the second component is zero.

Each term uses only a binary biproduct. The coefficient-family equivalence
and its naturality laws hold at endpoints and along outgoing edges alike.
The index and both category universes are independent.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped Classical ZeroObject

universe u v w

namespace HomologicalComplex

variable {C : Type u} [Category.{v} C]
  [HasZeroMorphisms C] [HasZeroObject C] [HasBinaryBiproducts C]
variable {ι : Type w} {c : ComplexShape ι}

/-- For C with a zero object, a complex shape c and a family I : ι → C,
the second coefficient at i is I(c.next i) if c has an outgoing edge at i,
and the zero object otherwise. -/
def endpointCofreeNextTerm (c : ComplexShape ι) (I : ι → C) (i : ι) : C :=
  if c.Rel i (c.next i) then I (c.next i) else 0

/-- For C with a zero object, a coefficient family I and an edge
c.Rel i j of a complex shape, the optional second coefficient at i is
canonically isomorphic to Iⱼ, using c.next i = j. -/
def endpointCofreeNextTermIso (I : ι → C) {i j : ι} (hij : c.Rel i j) :
    endpointCofreeNextTerm c I i ≅ I j :=
  eqToIso (by
    have hi : c.Rel i (c.next i) := by
      simpa only [c.next_eq' hij] using hij
    rw [endpointCofreeNextTerm, ite_eq_left hi]
    exact congrArg I (c.next_eq' hij))

omit [HasZeroMorphisms C] [HasBinaryBiproducts C] in
/-- For a family I in a category C with a zero object and an index i of a complex
shape c with no outgoing edge, the optional second cofree coefficient
at i equals the zero object. -/
theorem endpointCofreeNextTerm_of_no_next (I : ι → C) (i : ι)
    (hi : ¬ c.Rel i (c.next i)) :
    endpointCofreeNextTerm c I i = (0 : C) :=
  ite_eq_right hi

omit [HasZeroMorphisms C] [HasBinaryBiproducts C] in
/-- For a family I in a category C with a zero object and an index i of a complex
shape c satisfying ¬ c.Rel i (c.next i), the optional second coefficient
of the cofree term is a zero object. -/
theorem endpointCofreeNextTerm_isZero (I : ι → C) (i : ι)
    (hi : ¬ c.Rel i (c.next i)) :
    IsZero (endpointCofreeNextTerm c I i) := by
  rw [endpointCofreeNextTerm_of_no_next I i hi]
  exact CategoryTheory.Limits.isZero_zero C

/-- For a family I in C and any complex shape c, form
the complex with term Iᵢ ⊕ Eᵢ, where Eᵢ is I(c.next i) on an outgoing
edge and zero otherwise. Its differential along i → j is the second
projection, the identification Eᵢ ≅ Iⱼ, and the first inclusion at j. -/
def endpointCofree (c : ComplexShape ι) (I : ι → C) : HomologicalComplex C c where
  X i := I i ⊞ endpointCofreeNextTerm c I i
  d i j := if hij : c.Rel i j then
    (biprod.snd : I i ⊞ endpointCofreeNextTerm c I i ⟶
      endpointCofreeNextTerm c I i) ≫
        (endpointCofreeNextTermIso I hij).hom ≫
          (biprod.inl : I j ⟶ I j ⊞ endpointCofreeNextTerm c I j)
    else 0
  shape i j hij := by simp only [dite_eq_right hij]
  d_comp_d' i j k hij hjk := by
    simp only [dite_eq_left hij, dite_eq_left hjk, Category.assoc,
      biprod.inl_snd_assoc, comp_zero, zero_comp]

/-- For a family I in C and a complex shape c, the
projection D(I)ᵢ = Iᵢ ⊕ Eᵢ → Iᵢ is the first biproduct projection. -/
def endpointCofreeProjection (c : ComplexShape ι) (I : ι → C) (i : ι) :
    (endpointCofree c I).X i ⟶ I i :=
  biprod.fst

/-- For a family I in C and a complex shape c, the
projection D(I)ᵢ = Iᵢ ⊕ Eᵢ → Eᵢ is the second biproduct projection.
The target is zero when i has no outgoing edge. -/
def endpointCofreeSecondProjection (c : ComplexShape ι) (I : ι → C) (i : ι) :
    (endpointCofree c I).X i ⟶ endpointCofreeNextTerm c I i :=
  biprod.snd

/-- For a family I in C and a complex shape c, the map
Iᵢ → D(I)ᵢ = Iᵢ ⊕ Eᵢ is the first biproduct inclusion. -/
def endpointCofreeInclusion (c : ComplexShape ι) (I : ι → C) (i : ι) :
    I i ⟶ (endpointCofree c I).X i :=
  biprod.inl

/-- For a family I in C and a complex shape c, the
first inclusion Iᵢ → D(I)ᵢ followed by the first projection to Iᵢ is
the identity of Iᵢ. -/
@[reassoc (attr := simp)]
theorem endpointCofreeInclusion_projection (c : ComplexShape ι) (I : ι → C) (i : ι) :
    endpointCofreeInclusion c I i ≫ endpointCofreeProjection c I i = 𝟙 (I i) :=
  biprod.inl_fst

/-- For a family I in C and a complex shape c, the
first inclusion Iᵢ → D(I)ᵢ followed by the optional second projection
to Eᵢ is zero. -/
@[reassoc (attr := simp)]
theorem endpointCofreeInclusion_secondProjection (c : ComplexShape ι) (I : ι → C) (i : ι) :
    endpointCofreeInclusion c I i ≫ endpointCofreeSecondProjection c I i = 0 :=
  biprod.inl_snd

/-- For a family I in C and an edge c.Rel i j, the
differential D(I)ᵢ → D(I)ⱼ equals the optional second projection at i,
followed by Eᵢ ≅ Iⱼ and the first inclusion at j. -/
theorem endpointCofree_d (I : ι → C) {i j : ι} (hij : c.Rel i j) :
    (endpointCofree c I).d i j =
      endpointCofreeSecondProjection c I i ≫
        (endpointCofreeNextTermIso I hij).hom ≫ endpointCofreeInclusion c I j :=
  dite_eq_left hij

/-- For a family I in C and an index i of a complex
shape c with no outgoing edge, the cofree term D(I)ᵢ = Iᵢ ⊕ 0 is
canonically isomorphic to Iᵢ. -/
def endpointCofreeXIsoOfNoNext (I : ι → C) (i : ι)
    (hi : ¬ c.Rel i (c.next i)) : (endpointCofree c I).X i ≅ I i :=
  (isoBiprodZero (endpointCofreeNextTerm_isZero I i hi)).symm

/-- For a family I in C and an index i without an
outgoing edge in the complex shape c, the forward map of D(I)ᵢ ≅ Iᵢ
is the first cofree projection. -/
@[simp]
theorem endpointCofreeXIsoOfNoNext_hom (I : ι → C) (i : ι)
    (hi : ¬ c.Rel i (c.next i)) :
    (endpointCofreeXIsoOfNoNext I i hi).hom = endpointCofreeProjection c I i :=
  rfl

/-- For a complex K in C and a family aᵢ : Kᵢ → Iᵢ,
the second coefficient of its map into D(I) is dᵏᵢ,c.next i followed
by a at c.next i, transported to Eᵢ. At an index without an outgoing
edge it is zero. -/
def endpointCofreeSecondCoefficient (K : HomologicalComplex C c) (I : ι → C)
    (a : ∀ i, K.X i ⟶ I i) (i : ι) :
    K.X i ⟶ endpointCofreeNextTerm c I i :=
  if hi : c.Rel i (c.next i) then
    K.d i (c.next i) ≫ a (c.next i) ≫ (endpointCofreeNextTermIso I hi).inv
  else 0

/-- For a c-shaped complex K in C and arbitrary maps
aᵢ : Kᵢ → Iᵢ, there is a complex morphism K → D(I). Its component
at i has first coefficient aᵢ and second coefficient determined by
the outgoing differential of K; at an endpoint the latter is zero. -/
def endpointCofreeHom (K : HomologicalComplex C c) (I : ι → C)
    (a : ∀ i, K.X i ⟶ I i) : K ⟶ endpointCofree c I where
  f i := biprod.lift (a i) (endpointCofreeSecondCoefficient K I a i)
  comm' i j hij := by
    obtain rfl := c.next_eq' hij
    rw [endpointCofree_d I hij]
    change biprod.lift (a i) (endpointCofreeSecondCoefficient K I a i) ≫
        (biprod.snd ≫ (endpointCofreeNextTermIso I hij).hom ≫ biprod.inl) =
      K.d i (c.next i) ≫ biprod.lift (a (c.next i))
        (endpointCofreeSecondCoefficient K I a (c.next i))
    apply biprod.hom_ext
    · simp only [Category.assoc, biprod.inl_fst, Category.comp_id,
        biprod.lift_snd_assoc, biprod.lift_fst,
        endpointCofreeSecondCoefficient, dite_eq_left hij, Iso.inv_hom_id]
    · simp only [Category.assoc, biprod.inl_snd, comp_zero, biprod.lift_snd]
      by_cases hj : c.Rel (c.next i) (c.next (c.next i))
      · simp only [endpointCofreeSecondCoefficient, dite_eq_left hj,
          ← Category.assoc, K.d_comp_d, zero_comp]
      · simp only [endpointCofreeSecondCoefficient, dite_eq_right hj, comp_zero]

/-- For a complex K in C and maps aᵢ : Kᵢ → Iᵢ, the
component of the cofree morphism K → D(I), followed by
the first projection at i, equals aᵢ. -/
@[reassoc (attr := simp)]
theorem endpointCofreeHom_fst (K : HomologicalComplex C c) (I : ι → C)
    (a : ∀ i, K.X i ⟶ I i) (i : ι) :
    (endpointCofreeHom K I a).f i ≫ endpointCofreeProjection c I i = a i :=
  biprod.lift_fst _ _

/-- For a complex K in C and maps aᵢ : Kᵢ → Iᵢ, the
component of K → D(I), followed by the optional second projection
at i, is its coefficient determined by the source differential. -/
@[reassoc]
theorem endpointCofreeHom_snd (K : HomologicalComplex C c) (I : ι → C)
    (a : ∀ i, K.X i ⟶ I i) (i : ι) :
    (endpointCofreeHom K I a).f i ≫ endpointCofreeSecondProjection c I i =
      endpointCofreeSecondCoefficient K I a i :=
  biprod.lift_snd _ _

/-- For a complex K in C, maps aᵢ : Kᵢ → Iᵢ and an
edge c.Rel i j, the second coefficient of the cofree map K → D(I),
identified with a map to Iⱼ, equals aⱼ ∘ dᵏᵢⱼ. -/
@[reassoc]
theorem endpointCofreeHom_snd_of_rel (K : HomologicalComplex C c) (I : ι → C)
    (a : ∀ i, K.X i ⟶ I i) {i j : ι} (hij : c.Rel i j) :
    ((endpointCofreeHom K I a).f i ≫ endpointCofreeSecondProjection c I i) ≫
        (endpointCofreeNextTermIso I hij).hom = K.d i j ≫ a j := by
  obtain rfl := c.next_eq' hij
  rw [endpointCofreeHom_snd]
  simp only [endpointCofreeSecondCoefficient, dite_eq_left hij, Category.assoc,
    Iso.inv_hom_id, Category.comp_id]

/-- For a morphism g : K → D(I) in C and an outgoing
edge at i, its second coefficient at i is dᵏᵢ,c.next i followed by
the first coefficient of g at c.next i, transported to Eᵢ. Thus
commutation with the differential determines this coefficient. -/
@[reassoc]
theorem endpointCofree_snd (K : HomologicalComplex C c) (I : ι → C)
    (g : K ⟶ endpointCofree c I) (i : ι)
    (hi : c.Rel i (c.next i)) :
    g.f i ≫ endpointCofreeSecondProjection c I i =
      K.d i (c.next i) ≫ g.f (c.next i) ≫
        endpointCofreeProjection c I (c.next i) ≫ (endpointCofreeNextTermIso I hi).inv := by
  have h := congrArg
    (fun f : K.X i ⟶ (endpointCofree c I).X (c.next i) =>
      f ≫ endpointCofreeProjection c I (c.next i)) (g.comm i (c.next i))
  rw [endpointCofree_d I hi] at h
  simp only [Category.assoc, endpointCofreeInclusion_projection, Category.comp_id] at h
  have ht := congrArg
    (fun f : K.X i ⟶ I (c.next i) => f ≫ (endpointCofreeNextTermIso I hi).inv) h
  simpa only [Category.assoc, Iso.hom_inv_id, Category.comp_id] using ht

/-- For complexes in C and any shape c, two morphisms
K → D(I) are equal whenever their first coefficients Kᵢ → Iᵢ agree
at every index. This includes indices without an outgoing edge. -/
theorem endpointCofree_hom_ext (I : ι → C)
    {K : HomologicalComplex C c} {f g : K ⟶ endpointCofree c I}
    (h : ∀ i, f.f i ≫ endpointCofreeProjection c I i =
      g.f i ≫ endpointCofreeProjection c I i) : f = g := by
  apply HomologicalComplex.hom_ext
  intro i
  apply biprod.hom_ext
  · exact h i
  · change f.f i ≫ endpointCofreeSecondProjection c I i =
      g.f i ≫ endpointCofreeSecondProjection c I i
    by_cases hi : c.Rel i (c.next i)
    · rw [endpointCofree_snd K I f i hi, endpointCofree_snd K I g i hi]
      simpa only [Category.assoc] using congrArg
        (fun z : K.X (c.next i) ⟶ I (c.next i) =>
          K.d i (c.next i) ≫ z ≫ (endpointCofreeNextTermIso I hi).inv) (h (c.next i))
    · exact (endpointCofreeNextTerm_isZero I i hi).eq_of_tgt _ _

/-- For a c-shaped complex K and a family I in C,
morphisms K → D(I) are in bijection with arbitrary families Kᵢ → Iᵢ.
The forward direction takes first projections, and the inverse
constructs the morphism whose second coefficients are determined by dᵏ. -/
def endpointCofreeHomEquiv (K : HomologicalComplex C c) (I : ι → C) :
    (K ⟶ endpointCofree c I) ≃ (∀ i, K.X i ⟶ I i) where
  toFun g i := g.f i ≫ endpointCofreeProjection c I i
  invFun a := endpointCofreeHom K I a
  left_inv g := by
    apply endpointCofree_hom_ext I
    intro i
    exact endpointCofreeHom_fst K I _ i
  right_inv a := funext fun i => endpointCofreeHom_fst K I a i

/-- For a morphism g : K → L of c-shaped complexes in C
and maps aᵢ : Lᵢ → Iᵢ, the composite K → L → D(I) is the cofree
morphism with first coefficients aᵢ ∘ gᵢ. -/
@[reassoc]
theorem endpointCofreeHom_precomp {K L : HomologicalComplex C c} (g : K ⟶ L)
    (I : ι → C) (a : ∀ i, L.X i ⟶ I i) :
    g ≫ endpointCofreeHom L I a =
      endpointCofreeHom K I (fun i => g.f i ≫ a i) := by
  apply endpointCofree_hom_ext I
  intro i
  simp only [HomologicalComplex.comp_f, Category.assoc, endpointCofreeHom_fst]

/-- For coefficient families I,J in C and maps
aᵢ : Iᵢ → Jᵢ, the induced morphism D(I) → D(J) has first component
given by the first projection of D(I) followed by aᵢ. The second
components are determined by the cofree differentials. -/
def endpointCofreeMap (c : ComplexShape ι) {I J : ι → C} (a : ∀ i, I i ⟶ J i) :
    endpointCofree c I ⟶ endpointCofree c J :=
  endpointCofreeHom (endpointCofree c I) J
    (fun i => endpointCofreeProjection c I i ≫ a i)

/-- For maps aᵢ : Iᵢ → Jᵢ in C, the induced cofree
morphism D(I) → D(J), followed by the first projection at i, equals
the first projection from D(I)ᵢ followed by aᵢ. -/
@[reassoc (attr := simp)]
theorem endpointCofreeMap_fst (c : ComplexShape ι) {I J : ι → C} (a : ∀ i, I i ⟶ J i) (i : ι) :
    (endpointCofreeMap c a).f i ≫ endpointCofreeProjection c J i =
      endpointCofreeProjection c I i ≫ a i :=
  endpointCofreeHom_fst _ _ _ _

/-- For a complex K in C and maps aᵢ : Kᵢ → Iᵢ and
bᵢ : Iᵢ → Jᵢ, the prescribed morphism K → D(I) followed by the
cofree map D(I) → D(J) is the cofree morphism with coefficients
bᵢ ∘ aᵢ. -/
@[reassoc]
theorem endpointCofreeHom_naturality (K : HomologicalComplex C c) {I J : ι → C}
    (a : ∀ i, K.X i ⟶ I i) (b : ∀ i, I i ⟶ J i) :
    endpointCofreeHom K I a ≫ endpointCofreeMap c b =
      endpointCofreeHom K J (fun i => a i ≫ b i) := by
  apply endpointCofree_hom_ext J
  intro i
  simp only [HomologicalComplex.comp_f, Category.assoc, endpointCofreeMap_fst]
  rw [← Category.assoc, endpointCofreeHom_fst]
  rw [endpointCofreeHom_fst]

/-- For a family I in C and any complex shape c,
the cofree morphism induced by the identity on every Iᵢ is the
identity of D(I). -/
@[simp]
theorem endpointCofreeMap_id (c : ComplexShape ι) (I : ι → C) :
    endpointCofreeMap c (fun i => 𝟙 (I i)) = 𝟙 (endpointCofree c I) := by
  apply endpointCofree_hom_ext I
  intro i
  simp only [endpointCofreeMap_fst, Category.comp_id, HomologicalComplex.id_f, Category.id_comp]

/-- For coefficient families I,J,L in C and maps
aᵢ : Iᵢ → Jᵢ and bᵢ : Jᵢ → Lᵢ, the composite of their induced
cofree morphisms equals the cofree morphism induced by bᵢ ∘ aᵢ. -/
theorem endpointCofreeMap_comp (c : ComplexShape ι) {I J L : ι → C} (a : ∀ i, I i ⟶ J i)
    (b : ∀ i, J i ⟶ L i) :
    endpointCofreeMap c a ≫ endpointCofreeMap c b =
      endpointCofreeMap c (fun i => a i ≫ b i) := by
  apply endpointCofree_hom_ext L
  intro i
  simp only [HomologicalComplex.comp_f, Category.assoc,
    endpointCofreeMap_fst, endpointCofreeMap_fst_assoc]

end HomologicalComplex
