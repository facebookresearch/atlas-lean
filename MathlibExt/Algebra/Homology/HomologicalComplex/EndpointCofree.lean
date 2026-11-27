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

public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.CategoryTheory.Preadditive.Injective.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.BinaryBiproducts

/-!
# Cofree complexes with endpoint terms

Let C be an abelian category, c a complex shape on an arbitrary index type ι,
and I : ι → C a family of objects. Put Eᵢ = I(c.next i) when c has an outgoing
edge at i, and Eᵢ = 0 otherwise. The cofree complex D(I) has terms
D(I)ᵢ = Iᵢ ⊕ Eᵢ. Along an edge i → j, its differential projects onto Eᵢ,
identifies that object with Iⱼ and includes it as the first summand of D(I)ⱼ.
Successive differentials compose to zero.

For any c-shaped complex K, morphisms K → D(I) correspond bijectively to
arbitrary families aᵢ : Kᵢ → Iᵢ. The first component is aᵢ, and the second
component along i → j is dᵏᵢⱼ followed by aⱼ. At an index without an outgoing
edge the second component is zero.

Injective objects Iᵢ give an injective complex D(I), and monic first
components give a monic complex morphism. Thus enough injectives in C imply
enough injectives in the category of c-shaped complexes. Each term uses only
a binary biproduct; the index and both category universes are independent.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped Classical ZeroObject

universe u v w

namespace HomologicalComplex

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {ι : Type w} {c : ComplexShape ι}

/-- For an abelian category C, a complex shape c and a family I : ι → C,
the second coefficient at i is I(c.next i) if c has an outgoing edge at i,
and the zero object otherwise. -/
def endpointCofreeNextTerm (I : ι → C) (i : ι) : C :=
  if c.Rel i (c.next i) then I (c.next i) else 0

/-- For an abelian category C, a coefficient family I and an edge
c.Rel i j of a complex shape, the optional second coefficient at i is
canonically isomorphic to Iⱼ, using c.next i = j. -/
def endpointCofreeNextTermIso (I : ι → C) {i j : ι} (hij : c.Rel i j) :
    endpointCofreeNextTerm (c := c) I i ≅ I j :=
  eqToIso (by
    have hi : c.Rel i (c.next i) := by
      simpa only [c.next_eq' hij] using hij
    rw [endpointCofreeNextTerm, if_pos hi]
    exact congrArg I (c.next_eq' hij))

/-- For a family I in an abelian category and an index i of a complex
shape c with no outgoing edge, the optional second cofree coefficient
at i equals the zero object. -/
theorem endpointCofreeNextTerm_of_no_next (I : ι → C) (i : ι)
    (hi : ¬ c.Rel i (c.next i)) :
    endpointCofreeNextTerm (c := c) I i = (0 : C) :=
  if_neg hi

/-- For a family I in an abelian category and an index i of a complex
shape c satisfying ¬ c.Rel i (c.next i), the optional second coefficient
of the cofree term is a zero object. -/
theorem endpointCofreeNextTerm_isZero (I : ι → C) (i : ι)
    (hi : ¬ c.Rel i (c.next i)) :
    IsZero (endpointCofreeNextTerm (c := c) I i) := by
  rw [endpointCofreeNextTerm_of_no_next I i hi]
  exact isZero_zero C

/-- For a family I in an abelian category and any complex shape c, form
the complex with term Iᵢ ⊕ Eᵢ, where Eᵢ is I(c.next i) on an outgoing
edge and zero otherwise. Its differential along i → j is the second
projection, the identification Eᵢ ≅ Iⱼ, and the first inclusion at j. -/
def endpointCofree (I : ι → C) : HomologicalComplex C c where
  X i := I i ⊞ endpointCofreeNextTerm (c := c) I i
  d i j := if hij : c.Rel i j then
    (biprod.snd : I i ⊞ endpointCofreeNextTerm (c := c) I i ⟶
      endpointCofreeNextTerm (c := c) I i) ≫
        (endpointCofreeNextTermIso I hij).hom ≫
          (biprod.inl : I j ⟶ I j ⊞ endpointCofreeNextTerm (c := c) I j)
    else 0
  shape i j hij := by simp only [dif_neg hij]
  d_comp_d' i j k hij hjk := by
    simp only [dif_pos hij, dif_pos hjk, Category.assoc,
      biprod.inl_snd_assoc, comp_zero, zero_comp]

/-- For a family I in an abelian category and a complex shape c, the
projection D(I)ᵢ = Iᵢ ⊕ Eᵢ → Iᵢ is the first biproduct projection. -/
def endpointCofreeProjection (I : ι → C) (i : ι) :
    (endpointCofree (c := c) I).X i ⟶ I i :=
  biprod.fst

/-- For a family I in an abelian category and a complex shape c, the
projection D(I)ᵢ = Iᵢ ⊕ Eᵢ → Eᵢ is the second biproduct projection.
The target is zero when i has no outgoing edge. -/
def endpointCofreeSecondProjection (I : ι → C) (i : ι) :
    (endpointCofree (c := c) I).X i ⟶ endpointCofreeNextTerm (c := c) I i :=
  biprod.snd

/-- For a family I in an abelian category and a complex shape c, the map
Iᵢ → D(I)ᵢ = Iᵢ ⊕ Eᵢ is the first biproduct inclusion. -/
def endpointCofreeInclusion (I : ι → C) (i : ι) :
    I i ⟶ (endpointCofree (c := c) I).X i :=
  biprod.inl

/-- For a family I in an abelian category and a complex shape c, the
first inclusion Iᵢ → D(I)ᵢ followed by the first projection to Iᵢ is
the identity of Iᵢ. -/
@[reassoc (attr := simp)]
theorem endpointCofreeInclusion_projection (I : ι → C) (i : ι) :
    endpointCofreeInclusion (c := c) I i ≫ endpointCofreeProjection (c := c) I i = 𝟙 (I i) :=
  biprod.inl_fst

/-- For a family I in an abelian category and a complex shape c, the
first inclusion Iᵢ → D(I)ᵢ followed by the optional second projection
to Eᵢ is zero. -/
@[reassoc (attr := simp)]
theorem endpointCofreeInclusion_secondProjection (I : ι → C) (i : ι) :
    endpointCofreeInclusion (c := c) I i ≫ endpointCofreeSecondProjection (c := c) I i = 0 :=
  biprod.inl_snd

/-- For a family I in an abelian category and an edge c.Rel i j, the
differential D(I)ᵢ → D(I)ⱼ equals the optional second projection at i,
followed by Eᵢ ≅ Iⱼ and the first inclusion at j. -/
theorem endpointCofree_d (I : ι → C) {i j : ι} (hij : c.Rel i j) :
    (endpointCofree (c := c) I).d i j =
      endpointCofreeSecondProjection (c := c) I i ≫
        (endpointCofreeNextTermIso I hij).hom ≫ endpointCofreeInclusion (c := c) I j :=
  dif_pos hij

/-- For a family I in an abelian category and an index i of a complex
shape c with no outgoing edge, the cofree term D(I)ᵢ = Iᵢ ⊕ 0 is
canonically isomorphic to Iᵢ. -/
def endpointCofreeXIsoOfNoNext (I : ι → C) (i : ι)
    (hi : ¬ c.Rel i (c.next i)) : (endpointCofree (c := c) I).X i ≅ I i :=
  (isoBiprodZero (endpointCofreeNextTerm_isZero I i hi)).symm

/-- For a family I in an abelian category and an index i without an
outgoing edge in the complex shape c, the forward map of D(I)ᵢ ≅ Iᵢ
is the first cofree projection. -/
@[simp]
theorem endpointCofreeXIsoOfNoNext_hom (I : ι → C) (i : ι)
    (hi : ¬ c.Rel i (c.next i)) :
    (endpointCofreeXIsoOfNoNext I i hi).hom = endpointCofreeProjection (c := c) I i :=
  rfl

/-- For a complex K in an abelian category and a family aᵢ : Kᵢ → Iᵢ,
the second coefficient of its map into D(I) is dᵏᵢ,c.next i followed
by a at c.next i, transported to Eᵢ. At an index without an outgoing
edge it is zero. -/
def endpointCofreeSecondCoefficient (K : HomologicalComplex C c) (I : ι → C)
    (a : ∀ i, K.X i ⟶ I i) (i : ι) :
    K.X i ⟶ endpointCofreeNextTerm (c := c) I i :=
  if hi : c.Rel i (c.next i) then
    K.d i (c.next i) ≫ a (c.next i) ≫ (endpointCofreeNextTermIso I hi).inv
  else 0

/-- For a c-shaped complex K in an abelian category and arbitrary maps
aᵢ : Kᵢ → Iᵢ, there is a complex morphism K → D(I). Its component
at i has first coefficient aᵢ and second coefficient determined by
the outgoing differential of K; at an endpoint the latter is zero. -/
def endpointCofreeHom (K : HomologicalComplex C c) (I : ι → C)
    (a : ∀ i, K.X i ⟶ I i) : K ⟶ endpointCofree (c := c) I where
  f i := biprod.lift (a i) (endpointCofreeSecondCoefficient K I a i)
  comm' i j hij := by
    obtain rfl := c.next_eq' hij
    rw [endpointCofree_d I hij]
    apply biprod.hom_ext
    · simp only [Category.assoc, endpointCofreeInclusion, endpointCofreeSecondProjection,
        biprod.inl_fst, Category.comp_id, biprod.lift_snd, biprod.lift_snd_assoc,
        biprod.lift_fst,
        endpointCofreeSecondCoefficient, dif_pos hij, Iso.inv_hom_id]
    · simp only [Category.assoc, endpointCofreeInclusion, endpointCofreeSecondProjection,
        biprod.inl_snd, comp_zero, biprod.lift_snd]
      by_cases hj : c.Rel (c.next i) (c.next (c.next i))
      · simp only [endpointCofreeSecondCoefficient, dif_pos hj,
          ← Category.assoc, K.d_comp_d, zero_comp]
      · simp only [endpointCofreeSecondCoefficient, dif_neg hj, comp_zero]

/-- For a complex K in an abelian category and maps aᵢ : Kᵢ → Iᵢ, the
component of the prescribed cofree morphism K → D(I), followed by
the first projection at i, equals aᵢ. -/
@[reassoc (attr := simp)]
theorem endpointCofreeHom_fst (K : HomologicalComplex C c) (I : ι → C)
    (a : ∀ i, K.X i ⟶ I i) (i : ι) :
    (endpointCofreeHom K I a).f i ≫ endpointCofreeProjection (c := c) I i = a i :=
  biprod.lift_fst _ _

/-- For a complex K in an abelian category and maps aᵢ : Kᵢ → Iᵢ, the
component of K → D(I), followed by the optional second projection
at i, is its coefficient determined by the source differential. -/
@[reassoc]
theorem endpointCofreeHom_snd (K : HomologicalComplex C c) (I : ι → C)
    (a : ∀ i, K.X i ⟶ I i) (i : ι) :
    (endpointCofreeHom K I a).f i ≫ endpointCofreeSecondProjection (c := c) I i =
      endpointCofreeSecondCoefficient K I a i :=
  biprod.lift_snd _ _

/-- For a complex K in an abelian category, maps aᵢ : Kᵢ → Iᵢ and an
edge c.Rel i j, the second coefficient of the prescribed map K → D(I),
identified with a map to Iⱼ, equals aⱼ ∘ dᵏᵢⱼ. -/
@[reassoc]
theorem endpointCofreeHom_snd_of_rel (K : HomologicalComplex C c) (I : ι → C)
    (a : ∀ i, K.X i ⟶ I i) {i j : ι} (hij : c.Rel i j) :
    ((endpointCofreeHom K I a).f i ≫ endpointCofreeSecondProjection (c := c) I i) ≫
        (endpointCofreeNextTermIso I hij).hom = K.d i j ≫ a j := by
  obtain rfl := c.next_eq' hij
  rw [endpointCofreeHom_snd]
  simp only [endpointCofreeSecondCoefficient, dif_pos hij, Category.assoc,
    Iso.inv_hom_id, Category.comp_id]

/-- For a morphism g : K → D(I) in an abelian category and an outgoing
edge at i, its second coefficient at i is dᵏᵢ,c.next i followed by
the first coefficient of g at c.next i, transported to Eᵢ. Thus
commutation with the differential determines this coefficient. -/
@[reassoc]
theorem endpointCofree_snd (K : HomologicalComplex C c) (I : ι → C)
    (g : K ⟶ endpointCofree (c := c) I) (i : ι)
    (hi : c.Rel i (c.next i)) :
    g.f i ≫ endpointCofreeSecondProjection (c := c) I i =
      K.d i (c.next i) ≫ g.f (c.next i) ≫
        endpointCofreeProjection (c := c) I (c.next i) ≫ (endpointCofreeNextTermIso I hi).inv := by
  have h := congrArg
    (fun f : K.X i ⟶ (endpointCofree (c := c) I).X (c.next i) =>
      f ≫ endpointCofreeProjection (c := c) I (c.next i)) (g.comm i (c.next i))
  rw [endpointCofree_d I hi] at h
  simp only [Category.assoc, endpointCofreeInclusion_projection, Category.comp_id] at h
  have ht := congrArg
    (fun f : K.X i ⟶ I (c.next i) => f ≫ (endpointCofreeNextTermIso I hi).inv) h
  simpa only [Category.assoc, Iso.hom_inv_id, Category.comp_id] using ht

/-- For complexes in an abelian category and any shape c, two morphisms
K → D(I) are equal whenever their first coefficients Kᵢ → Iᵢ agree
at every index. This includes indices without an outgoing edge. -/
theorem endpointCofree_hom_ext (I : ι → C)
    {K : HomologicalComplex C c} {f g : K ⟶ endpointCofree (c := c) I}
    (h : ∀ i, f.f i ≫ endpointCofreeProjection (c := c) I i =
      g.f i ≫ endpointCofreeProjection (c := c) I i) : f = g := by
  apply HomologicalComplex.hom_ext
  intro i
  apply biprod.hom_ext
  · exact h i
  · by_cases hi : c.Rel i (c.next i)
    · rw [endpointCofree_snd K I f i hi, endpointCofree_snd K I g i hi, h (c.next i)]
    · exact (endpointCofreeNextTerm_isZero I i hi).eq_of_tgt _ _

/-- For a c-shaped complex K and a family I in an abelian category,
morphisms K → D(I) are in bijection with arbitrary families Kᵢ → Iᵢ.
The forward direction takes first projections, and the inverse
constructs the morphism whose second coefficients are determined by dᵏ. -/
def endpointCofreeHomEquiv (K : HomologicalComplex C c) (I : ι → C) :
    (K ⟶ endpointCofree (c := c) I) ≃ (∀ i, K.X i ⟶ I i) where
  toFun g i := g.f i ≫ endpointCofreeProjection (c := c) I i
  invFun a := endpointCofreeHom K I a
  left_inv g := by
    apply endpointCofree_hom_ext I
    intro i
    exact endpointCofreeHom_fst K I _ i
  right_inv a := funext fun i => endpointCofreeHom_fst K I a i

/-- For a morphism g : K → L of c-shaped complexes in an abelian category
and maps aᵢ : Lᵢ → Iᵢ, the composite K → L → D(I) is the prescribed
cofree morphism with first coefficients aᵢ ∘ gᵢ. -/
@[reassoc]
theorem endpointCofreeHom_precomp {K L : HomologicalComplex C c} (g : K ⟶ L)
    (I : ι → C) (a : ∀ i, L.X i ⟶ I i) :
    g ≫ endpointCofreeHom L I a =
      endpointCofreeHom K I (fun i => g.f i ≫ a i) := by
  apply endpointCofree_hom_ext I
  intro i
  simp only [HomologicalComplex.comp_f, Category.assoc, endpointCofreeHom_fst]

/-- For coefficient families I,J in an abelian category and maps
aᵢ : Iᵢ → Jᵢ, the induced morphism D(I) → D(J) has first component
given by the first projection of D(I) followed by aᵢ. The second
components are determined by the cofree differentials. -/
def endpointCofreeMap {I J : ι → C} (a : ∀ i, I i ⟶ J i) :
    endpointCofree (c := c) I ⟶ endpointCofree (c := c) J :=
  endpointCofreeHom (endpointCofree (c := c) I) J
    (fun i => endpointCofreeProjection (c := c) I i ≫ a i)

/-- For maps aᵢ : Iᵢ → Jᵢ in an abelian category, the induced cofree
morphism D(I) → D(J), followed by the first projection at i, equals
the first projection from D(I)ᵢ followed by aᵢ. -/
@[reassoc (attr := simp)]
theorem endpointCofreeMap_fst {I J : ι → C} (a : ∀ i, I i ⟶ J i) (i : ι) :
    (endpointCofreeMap (c := c) a).f i ≫ endpointCofreeProjection (c := c) J i =
      endpointCofreeProjection (c := c) I i ≫ a i :=
  endpointCofreeHom_fst _ _ _ _

/-- For a complex K in an abelian category and maps aᵢ : Kᵢ → Iᵢ and
bᵢ : Iᵢ → Jᵢ, the prescribed morphism K → D(I) followed by the
cofree map D(I) → D(J) is the prescribed morphism with coefficients
bᵢ ∘ aᵢ. -/
@[reassoc]
theorem endpointCofreeHom_naturality (K : HomologicalComplex C c) {I J : ι → C}
    (a : ∀ i, K.X i ⟶ I i) (b : ∀ i, I i ⟶ J i) :
    endpointCofreeHom K I a ≫ endpointCofreeMap b =
      endpointCofreeHom K J (fun i => a i ≫ b i) := by
  apply endpointCofree_hom_ext J
  intro i
  simp only [HomologicalComplex.comp_f, Category.assoc, endpointCofreeMap_fst]
  rw [← Category.assoc, endpointCofreeHom_fst]

/-- For a family I in an abelian category and any complex shape c,
the cofree morphism induced by the identity on every Iᵢ is the
identity of D(I). -/
@[simp]
theorem endpointCofreeMap_id (I : ι → C) :
    endpointCofreeMap (c := c) (fun i => 𝟙 (I i)) = 𝟙 (endpointCofree (c := c) I) := by
  apply endpointCofree_hom_ext I
  intro i
  simp only [endpointCofreeMap_fst, Category.comp_id, HomologicalComplex.id_f, Category.id_comp]

/-- For coefficient families I,J,L in an abelian category and maps
aᵢ : Iᵢ → Jᵢ and bᵢ : Jᵢ → Lᵢ, the composite of their induced
cofree morphisms equals the cofree morphism induced by bᵢ ∘ aᵢ. -/
theorem endpointCofreeMap_comp {I J L : ι → C} (a : ∀ i, I i ⟶ J i)
    (b : ∀ i, J i ⟶ L i) :
    endpointCofreeMap (c := c) a ≫ endpointCofreeMap b =
      endpointCofreeMap (fun i => a i ≫ b i) := by
  apply endpointCofree_hom_ext L
  intro i
  simp only [HomologicalComplex.comp_f, Category.assoc,
    endpointCofreeMap_fst, endpointCofreeMap_fst_assoc]

/-- For an abelian category C, any complex shape c and a family of
injective objects Iᵢ, the complex D(I) is injective in the category
of c-shaped complexes. Its term at an endpoint has zero second summand. -/
theorem endpointCofree_injective (I : ι → C) [∀ i, Injective (I i)] :
    Injective (endpointCofree (c := c) I) where
  factors {X Y} g m hm := by
    letI : Mono m := hm
    let a : ∀ i, Y.X i ⟶ I i := fun i =>
      Injective.factorThru (g.f i ≫ endpointCofreeProjection (c := c) I i) (m.f i)
    refine ⟨endpointCofreeHom Y I a, ?_⟩
    apply endpointCofree_hom_ext I
    intro i
    change (m.f i ≫ (endpointCofreeHom Y I a).f i) ≫
      endpointCofreeProjection (c := c) I i = g.f i ≫ endpointCofreeProjection (c := c) I i
    rw [Category.assoc, endpointCofreeHom_fst]
    exact Injective.comp_factorThru _ _

/-- For a complex K in an abelian category and a family of monomorphisms
aᵢ : Kᵢ → Iᵢ, the prescribed cofree morphism K → D(I) is a
monomorphism of complexes of the same shape. -/
theorem endpointCofreeHom_mono (K : HomologicalComplex C c) (I : ι → C)
    (a : ∀ i, K.X i ⟶ I i) [∀ i, Mono (a i)] :
    Mono (endpointCofreeHom K I a) := by
  apply HomologicalComplex.mono_of_mono_f
  intro i
  exact mono_of_mono_fac (endpointCofreeHom_fst K I a i)

/-- If an abelian category C has enough injectives, a complex K of any
shape has a cofree morphism into D(I), where Iᵢ is the chosen injective
object containing Kᵢ and the first coefficient is the chosen
monomorphism Kᵢ → Iᵢ. -/
def endpointCofreeCover (K : HomologicalComplex C c) [EnoughInjectives C] :
    K ⟶ endpointCofree (c := c) (fun i => Injective.under (K.X i)) :=
  endpointCofreeHom K _ (fun i => Injective.ι (K.X i))

/-- For a complex K in an abelian category with enough injectives,
the cofree cover followed by the first projection in degree i is
the chosen inclusion of Kᵢ into its injective object. -/
@[reassoc (attr := simp)]
theorem endpointCofreeCover_fst (K : HomologicalComplex C c) [EnoughInjectives C] (i : ι) :
    (endpointCofreeCover K).f i ≫
        endpointCofreeProjection (c := c) (fun j => Injective.under (K.X j)) i =
      Injective.ι (K.X i) :=
  endpointCofreeHom_fst _ _ _ _

/-- If C is an abelian category with enough injectives, then the category
of complexes in C of any shape c has enough injectives. Each complex
embeds in the cofree complex formed from its degreewise injective
objects, including at indices with no outgoing edge. -/
theorem enoughInjectives_of_endpointCofree [EnoughInjectives C] :
    EnoughInjectives (HomologicalComplex C c) where
  presentation K := by
    let I : ι → C := fun i => Injective.under (K.X i)
    let a : ∀ i, K.X i ⟶ I i := fun i => Injective.ι (K.X i)
    letI : ∀ i, Injective (I i) := fun i => by dsimp only [I]; infer_instance
    letI : ∀ i, Mono (a i) := fun i => by dsimp only [a, I]; infer_instance
    letI : Injective (endpointCofree (c := c) I) := endpointCofree_injective I
    letI : Mono (endpointCofreeHom K I a) := endpointCofreeHom_mono K I a
    exact ⟨{ J := endpointCofree (c := c) I, f := endpointCofreeHom K I a }⟩

/-- For an abelian category C with enough injectives and any complex
shape c, cofree covers provide the enough-injectives structure on
the category of c-shaped complexes. The index, object and morphism
universes are independent. -/
instance instEnoughInjectivesEndpointCofree [EnoughInjectives C] :
    EnoughInjectives (HomologicalComplex C c) :=
  enoughInjectives_of_endpointCofree

end HomologicalComplex
