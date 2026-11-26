/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.Algebra.Homology.CochainComplex.BoundedIsoWaldhausen
public import MathlibExt.Algebra.Homology.CochainComplex.BoundedAmbientCofiberExactness
public import MathlibExt.CategoryTheory.Waldhausen.Fibration.AcyclicSubcategory
public import Mathlib.CategoryTheory.ObjectProperty.ContainsZero
public import Mathlib.CategoryTheory.ObjectProperty.Equivalence
public import Mathlib.CategoryTheory.Adjunction.Limits

/-!
# The bounded ambient-acyclic full subcategory

For additive F:E → A, with E preadditive and A abelian, consider the full
subcategory A_F of bounded complexes K with F(K) acyclic.
When E is Quillen exact with a zero object and binary biproducts, this
object condition equals acyclicity for the bounded ambient Waldhausen
weak class.

If F is exact, admissible pushouts remain ambient acyclic.
The subcategory therefore has degreewise admissible cofibrations and
isomorphisms as weak equivalences. Its inclusion is exact into both
the bounded isomorphism model and the bounded ambient model, and it
preserves and reflects their cofiber sequences.
The two equivalent acyclic presentations retain the same complexes,
morphisms and canonical zero comparisons.

Full faithfulness, reflection and essential-image kernel closure additionally
identify ambient-acyclic membership with all-degree admissible cycle data.
The category object and morphism universes are independent.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

universe uE vE uA vA

open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject

namespace CochainComplex.Bounded

variable {E : Type uE} [Category.{vE} E] [Preadditive E]
variable {A : Type uA} [Category.{vA} A] [Abelian A]
variable (F : E ⥤ A) [F.Additive]

/-- Let E be preadditive, A abelian and F:E → A additive.
Let A_F be the full subcategory of bounded integer E-complexes K
whose ambient complex F(K) is acyclic, and J:A_F → Bounded(E)
its inclusion.

The object property on Bounded(E) is acyclicity of the termwise mapped complex F(K). -/
def ambientAcyclicObjects : ObjectProperty (Bounded E) :=
  fun K => ((F.mapHomologicalComplex (.up ℤ)).obj K.obj).Acyclic

/-- Let E be preadditive, A abelian and F:E → A additive.
Let A_F be the full subcategory of bounded integer E-complexes K
whose ambient complex F(K) is acyclic, and J:A_F → Bounded(E)
its inclusion.

The full subcategory A_F consists of bounded E-complexes whose F-images are acyclic. -/
abbrev AmbientAcyclic := (ambientAcyclicObjects F).FullSubcategory

/-- Let E be preadditive, A abelian and F:E → A additive.
Let A_F be the full subcategory of bounded integer E-complexes K
whose ambient complex F(K) is acyclic, and J:A_F → Bounded(E)
its inclusion.

The inclusion J retains the bounded complex and all its ambient bounded morphisms. -/
abbrev ambientAcyclicι : AmbientAcyclic F ⥤ Bounded E := (ambientAcyclicObjects F).ι

/-- Let E be preadditive, A abelian and F:E → A additive.
Let A_F be the full subcategory of bounded integer E-complexes K
whose ambient complex F(K) is acyclic, and J:A_F → Bounded(E)
its inclusion.

For K in A_F, the inclusion has value the same underlying bounded complex K. -/
theorem ambientAcyclicι_obj (K : AmbientAcyclic F) : (ambientAcyclicι F).obj K = K.obj := rfl

/-- Let E be preadditive, A abelian and F:E → A additive.
Let A_F be the full subcategory of bounded integer E-complexes K
whose ambient complex F(K) is acyclic, and J:A_F → Bounded(E)
its inclusion.

For a map in A_F, J returns its underlying bounded cochain map. -/
theorem ambientAcyclicι_map {K L : AmbientAcyclic F} (f : K ⟶ L) :
    (ambientAcyclicι F).map f = f.hom := rfl

instance ambientAcyclicObjects_isClosedUnderIsomorphisms :
    (ambientAcyclicObjects F).IsClosedUnderIsomorphisms where
  of_iso e hK := by
    let J := F.mapHomologicalComplex (.up ℤ)
    let _ : QuasiIso (J.map e.hom.hom) := inferInstance
    intro j
    exact (exactAt_iff_of_quasiIsoAt (J.map e.hom.hom) j).mp (hK j)

variable [HasZeroObject E]

instance ambientAcyclicObjects_containsZero : (ambientAcyclicObjects F).ContainsZero where
  exists_zero := by
    let J := ι E ⋙ F.mapHomologicalComplex (.up ℤ)
    exact ⟨0, isZero_zero (Bounded E),
      (J.obj (0 : Bounded E)).acyclic_of_isZero (J.map_isZero (isZero_zero (Bounded E)))⟩

/-- Let E be preadditive, A abelian and F:E → A additive.
Let A_F be the full subcategory of bounded integer E-complexes K
whose ambient complex F(K) is acyclic, and J:A_F → Bounded(E)
its inclusion. Assume E has a zero object.

The canonical zero comparison δ:J(0_{A_F}) ≅ 0_{Bounded(E)} identifies the included selected zero with the bounded zero. -/
def ambientAcyclicZeroIso : (ambientAcyclicι F).obj (0 : AmbientAcyclic F) ≅ (0 : Bounded E) :=
  ((ambientAcyclicι F).map_isZero (isZero_zero (AmbientAcyclic F))).isoZero

/-- Let E be preadditive, A abelian and F:E → A additive.
Let A_F be the full subcategory of bounded integer E-complexes K
whose ambient complex F(K) is acyclic, and J:A_F → Bounded(E)
its inclusion. Assume E has a zero object and let δ:J(0_{A_F}) ≅ 0_{Bounded(E)} be the canonical comparison.

The forward map followed by its inverse is the identity of J(0_{A_F}). -/
theorem ambientAcyclicZeroIso_hom_inv :
    (ambientAcyclicZeroIso F).hom ≫ (ambientAcyclicZeroIso F).inv =
      𝟙 ((ambientAcyclicι F).obj (0 : AmbientAcyclic F)) := (ambientAcyclicZeroIso F).hom_inv_id

variable [HasBinaryBiproducts E] [ExactCategory E]

/-- Let E be preadditive, A abelian and F:E → A additive.
Let A_F be the full subcategory of bounded integer E-complexes K
whose ambient complex F(K) is acyclic, and J:A_F → Bounded(E)
its inclusion. Assume E is Quillen exact with a zero object and binary biproducts.
On Bounded(E), let V have degreewise admissible cofibrations and
isomorphism weak maps, and W the same cofibrations with F-detected
quasi-isomorphisms. Let C_W be the canonical full subcategory of
objects receiving a W-weak map from zero.

For any z:0 → K in Bounded(E), F(K) is acyclic if and only if z is W-weak. -/
theorem ambientAcyclicObjects_iff_zeroWeak (K : Bounded E) (z : (0 : Bounded E) ⟶ K) :
    letI := ambientWaldhausenCategory F
    ambientAcyclicObjects F K ↔ IsWeakEquivalence z := by
  let _ := ambientWaldhausenCategory F
  let J := ι E ⋙ F.mapHomologicalComplex (.up ℤ)
  have hZero := (J.obj (0 : Bounded E)).acyclic_of_isZero
    (J.map_isZero (isZero_zero (Bounded E)))
  rw [ambient_isWeakEquivalence_iff F z]
  constructor
  · intro hK
    apply (quasiIso_iff (J.map z)).mpr
    intro j
    exact (quasiIsoAt_iff_exactAt (J.map z) j (hZero j)).mpr (hK j)
  · intro hz
    let _ : QuasiIso (J.map z) := hz
    intro j
    exact (quasiIsoAt_iff_exactAt (J.map z) j (hZero j)).mp inferInstance

/-- Let E be preadditive, A abelian and F:E → A additive.
Let A_F be the full subcategory of bounded integer E-complexes K
whose ambient complex F(K) is acyclic, and J:A_F → Bounded(E)
its inclusion. Assume E is Quillen exact with a zero object and binary biproducts.
On Bounded(E), let V have degreewise admissible cofibrations and
isomorphism weak maps, and W the same cofibrations with F-detected
quasi-isomorphisms. Let C_W be the canonical full subcategory of
objects receiving a W-weak map from zero.

The F-acyclic object property equals the canonical W-acyclic property 0 → K weak. -/
theorem ambientAcyclicCanonical_iff (K : Bounded E) :
    ambientAcyclicObjects F K ↔
      @WaldhausenCategoryWithoutGluing.acyclicObjects (Bounded E) _ _ (ambientWaldhausenCategory F) K := by
  let _ := ambientWaldhausenCategory F
  exact (ambientAcyclicObjects_iff_zeroWeak F K ((isZero_zero (Bounded E)).to_ K)).trans
    (WaldhausenCategoryWithoutGluing.acyclicObjects_iff_zero_to K ((isZero_zero (Bounded E)).to_ K)).symm

/-- Let E be preadditive, A abelian and F:E → A additive.
Let A_F be the full subcategory of bounded integer E-complexes K
whose ambient complex F(K) is acyclic, and J:A_F → Bounded(E)
its inclusion. Assume E is Quillen exact with a zero object and binary biproducts.
On Bounded(E), let V have degreewise admissible cofibrations and
isomorphism weak maps, and W the same cofibrations with F-detected
quasi-isomorphisms. Let C_W be the canonical full subcategory of
objects receiving a W-weak map from zero.

The canonical acyclic category C_W is the full subcategory of Bounded(E) with 0 → K W-weak. -/
abbrev CanonicalAmbientAcyclic := Waldhausen.AcyclicSubcategory (ambientWaldhausenCategory F)

/-- Let E be preadditive, A abelian and F:E → A additive.
Let A_F be the full subcategory of bounded integer E-complexes K
whose ambient complex F(K) is acyclic, and J:A_F → Bounded(E)
its inclusion. Assume E is Quillen exact with a zero object and binary biproducts.
On Bounded(E), let V have degreewise admissible cofibrations and
isomorphism weak maps, and W the same cofibrations with F-detected
quasi-isomorphisms. Let C_W be the canonical full subcategory of
objects receiving a W-weak map from zero.

The comparison functor A_F → C_W identifies the full subcategories by their equivalent acyclicity conditions. -/
def ambientAcyclicToCanonical : AmbientAcyclic F ⥤ CanonicalAmbientAcyclic F :=
  ObjectProperty.ιOfLE (fun K hK => (ambientAcyclicCanonical_iff F K).mp hK)

/-- Let E be preadditive, A abelian and F:E → A additive.
Let A_F be the full subcategory of bounded integer E-complexes K
whose ambient complex F(K) is acyclic, and J:A_F → Bounded(E)
its inclusion. Assume E is Quillen exact with a zero object and binary biproducts.
On Bounded(E), let V have degreewise admissible cofibrations and
isomorphism weak maps, and W the same cofibrations with F-detected
quasi-isomorphisms. Let C_W be the canonical full subcategory of
objects receiving a W-weak map from zero.

The inverse comparison C_W → A_F uses the equivalent ambient-acyclic condition on the same bounded objects. -/
def ambientAcyclicFromCanonical : CanonicalAmbientAcyclic F ⥤ AmbientAcyclic F :=
  ObjectProperty.ιOfLE (fun K hK => (ambientAcyclicCanonical_iff F K).mpr hK)

/-- Let E be preadditive, A abelian and F:E → A additive.
Let A_F be the full subcategory of bounded integer E-complexes K
whose ambient complex F(K) is acyclic, and J:A_F → Bounded(E)
its inclusion. Assume E is Quillen exact with a zero object and binary biproducts.
On Bounded(E), let V have degreewise admissible cofibrations and
isomorphism weak maps, and W the same cofibrations with F-detected
quasi-isomorphisms. Let C_W be the canonical full subcategory of
objects receiving a W-weak map from zero.

The two acyclic presentations are canonically equivalent, with unchanged underlying bounded objects and morphisms. -/
def ambientAcyclicCanonicalEquivalence : AmbientAcyclic F ≌ CanonicalAmbientAcyclic F where
  functor := ambientAcyclicToCanonical F
  inverse := ambientAcyclicFromCanonical F
  unitIso := Iso.refl _
  counitIso := Iso.refl _
  functor_unitIso_comp X := by
    change (𝟙 ((ambientAcyclicToCanonical F).obj X)) ≫ 𝟙 _ = 𝟙 _
    exact Category.id_comp _

instance ambientAcyclicToCanonical_isEquivalence : (ambientAcyclicToCanonical F).IsEquivalence :=
  (ambientAcyclicCanonicalEquivalence F).isEquivalence_functor

instance ambientAcyclicFromCanonical_isEquivalence : (ambientAcyclicFromCanonical F).IsEquivalence :=
  (ambientAcyclicCanonicalEquivalence F).symm.isEquivalence_functor

/-- Let E be preadditive, A abelian and F:E → A additive.
Let A_F be the full subcategory of bounded integer E-complexes K
whose ambient complex F(K) is acyclic, and J:A_F → Bounded(E)
its inclusion. Assume E is Quillen exact with a zero object and binary biproducts.
On Bounded(E), let V have degreewise admissible cofibrations and
isomorphism weak maps, and W the same cofibrations with F-detected
quasi-isomorphisms. Let C_W be the canonical full subcategory of
objects receiving a W-weak map from zero.

The forward comparison A_F → C_W retains the underlying bounded complex. -/
theorem ambientAcyclicToCanonical_obj (X : AmbientAcyclic F) :
    ((ambientAcyclicToCanonical F).obj X).obj = X.obj := rfl

/-- Let E be preadditive, A abelian and F:E → A additive.
Let A_F be the full subcategory of bounded integer E-complexes K
whose ambient complex F(K) is acyclic, and J:A_F → Bounded(E)
its inclusion. Assume E is Quillen exact with a zero object and binary biproducts.
On Bounded(E), let V have degreewise admissible cofibrations and
isomorphism weak maps, and W the same cofibrations with F-detected
quasi-isomorphisms. Let C_W be the canonical full subcategory of
objects receiving a W-weak map from zero.

The forward comparison retains the underlying bounded cochain morphism. -/
theorem ambientAcyclicToCanonical_map {X Y : AmbientAcyclic F} (f : X ⟶ Y) :
    ((ambientAcyclicToCanonical F).map f).hom = f.hom := rfl

/-- Let E be preadditive, A abelian and F:E → A additive.
Let A_F be the full subcategory of bounded integer E-complexes K
whose ambient complex F(K) is acyclic, and J:A_F → Bounded(E)
its inclusion. Assume E is Quillen exact with a zero object and binary biproducts.
On Bounded(E), let V have degreewise admissible cofibrations and
isomorphism weak maps, and W the same cofibrations with F-detected
quasi-isomorphisms. Let C_W be the canonical full subcategory of
objects receiving a W-weak map from zero.

The inverse comparison C_W → A_F retains the underlying bounded complex. -/
theorem ambientAcyclicFromCanonical_obj (X : CanonicalAmbientAcyclic F) :
    ((ambientAcyclicFromCanonical F).obj X).obj = X.obj := rfl

/-- Let E be preadditive, A abelian and F:E → A additive.
Let A_F be the full subcategory of bounded integer E-complexes K
whose ambient complex F(K) is acyclic, and J:A_F → Bounded(E)
its inclusion. Assume E is Quillen exact with a zero object and binary biproducts.
On Bounded(E), let V have degreewise admissible cofibrations and
isomorphism weak maps, and W the same cofibrations with F-detected
quasi-isomorphisms. Let C_W be the canonical full subcategory of
objects receiving a W-weak map from zero.

The inverse comparison retains the underlying bounded cochain morphism. -/
theorem ambientAcyclicFromCanonical_map {X Y : CanonicalAmbientAcyclic F} (f : X ⟶ Y) :
    ((ambientAcyclicFromCanonical F).map f).hom = f.hom := rfl

/-- Let E be preadditive, A abelian and F:E → A additive.
Let A_F be the full subcategory of bounded integer E-complexes K
whose ambient complex F(K) is acyclic, and J:A_F → Bounded(E)
its inclusion. Assume E is Quillen exact with a zero object and binary biproducts.
On Bounded(E), let V have degreewise admissible cofibrations and
isomorphism weak maps, and W the same cofibrations with F-detected
quasi-isomorphisms. Let C_W be the canonical full subcategory of
objects receiving a W-weak map from zero.

The forward comparison followed by the canonical inclusion C_W → Bounded(E) equals J. -/
theorem ambientAcyclicToCanonical_comp_ι :
    ambientAcyclicToCanonical F ⋙ Waldhausen.acyclicι (ambientWaldhausenCategory F) =
      ambientAcyclicι F := rfl

/-- Let E be preadditive, A abelian and F:E → A additive.
Let A_F be the full subcategory of bounded integer E-complexes K
whose ambient complex F(K) is acyclic, and J:A_F → Bounded(E)
its inclusion. Assume E is Quillen exact with a zero object and binary biproducts.
On Bounded(E), let V have degreewise admissible cofibrations and
isomorphism weak maps, and W the same cofibrations with F-detected
quasi-isomorphisms. Let C_W be the canonical full subcategory of
objects receiving a W-weak map from zero.

The inverse comparison followed by J equals the canonical inclusion C_W → Bounded(E). -/
theorem ambientAcyclicFromCanonical_comp_ι :
    ambientAcyclicFromCanonical F ⋙ ambientAcyclicι F =
      Waldhausen.acyclicι (ambientWaldhausenCategory F) := rfl

/-- Let E be preadditive, A abelian and F:E → A additive.
Let A_F be the full subcategory of bounded integer E-complexes K
whose ambient complex F(K) is acyclic, and J:A_F → Bounded(E)
its inclusion. Assume E is Quillen exact with a zero object and binary biproducts.
On Bounded(E), let V have degreewise admissible cofibrations and
isomorphism weak maps, and W the same cofibrations with F-detected
quasi-isomorphisms. Let C_W be the canonical full subcategory of
objects receiving a W-weak map from zero.

For the forward comparison T:A_F → C_W, the canonical isomorphism T(0_{A_F}) ≅ 0_{C_W} compares the two selected acyclic zeros. -/
def ambientAcyclicCanonicalZeroIso :
    letI := Waldhausen.acyclicHasZeroObject (ambientWaldhausenCategory F)
    (ambientAcyclicToCanonical F).obj (0 : AmbientAcyclic F) ≅ (0 : CanonicalAmbientAcyclic F) := by
  let _ := Waldhausen.acyclicHasZeroObject (ambientWaldhausenCategory F)
  exact ((Waldhausen.acyclic_isZero_iff (ambientWaldhausenCategory F) _).mpr
    ((ambientAcyclicι F).map_isZero (isZero_zero (AmbientAcyclic F)))).isoZero

/-- Let E be preadditive, A abelian and F:E → A additive.
Let A_F be the full subcategory of bounded integer E-complexes K
whose ambient complex F(K) is acyclic, and J:A_F → Bounded(E)
its inclusion. Assume E is Quillen exact with a zero object and binary biproducts.
On Bounded(E), let V have degreewise admissible cofibrations and
isomorphism weak maps, and W the same cofibrations with F-detected
quasi-isomorphisms. Let C_W be the canonical full subcategory of
objects receiving a W-weak map from zero.

After inclusion in Bounded(E), the forward comparison T(0_{A_F}) → 0_{C_W} followed by the canonical included-zero map equals J(0_{A_F}) → 0_{Bounded(E)}. -/
theorem ambientAcyclicCanonicalZeroIso_hom :
    letI := Waldhausen.acyclicHasZeroObject (ambientWaldhausenCategory F)
    (Waldhausen.acyclicι (ambientWaldhausenCategory F)).map (ambientAcyclicCanonicalZeroIso F).hom ≫
        (Waldhausen.acyclicιZeroIso (ambientWaldhausenCategory F)).hom =
      (ambientAcyclicZeroIso F).hom := by
  let _ := Waldhausen.acyclicHasZeroObject (ambientWaldhausenCategory F)
  exact (isZero_zero (Bounded E)).eq_of_tgt _ _

/-- Let E be preadditive, A abelian and F:E → A additive.
Let A_F be the full subcategory of bounded integer E-complexes K
whose ambient complex F(K) is acyclic, and J:A_F → Bounded(E)
its inclusion. Assume E is Quillen exact with a zero object and binary biproducts.
On Bounded(E), let V have degreewise admissible cofibrations and
isomorphism weak maps, and W the same cofibrations with F-detected
quasi-isomorphisms. Let C_W be the canonical full subcategory of
objects receiving a W-weak map from zero.

After inclusion in Bounded(E), the inverse comparison 0_{C_W} → T(0_{A_F}) preceded by the canonical inverse included-zero map equals 0_{Bounded(E)} → J(0_{A_F}). -/
theorem ambientAcyclicCanonicalZeroIso_inv :
    letI := Waldhausen.acyclicHasZeroObject (ambientWaldhausenCategory F)
    (Waldhausen.acyclicιZeroIso (ambientWaldhausenCategory F)).inv ≫
        (Waldhausen.acyclicι (ambientWaldhausenCategory F)).map (ambientAcyclicCanonicalZeroIso F).inv =
      (ambientAcyclicZeroIso F).inv := by
  let _ := Waldhausen.acyclicHasZeroObject (ambientWaldhausenCategory F)
  exact (isZero_zero (Bounded E)).eq_of_src _ _

/-- Let E be preadditive, A abelian and F:E → A additive.
Let A_F be the full subcategory of bounded integer E-complexes K
whose ambient complex F(K) is acyclic, and J:A_F → Bounded(E)
its inclusion. Assume E is Quillen exact with a zero object and binary biproducts.
On Bounded(E), let V have degreewise admissible cofibrations and
isomorphism weak maps, and W the same cofibrations with F-detected
quasi-isomorphisms. Let C_W be the canonical full subcategory of
objects receiving a W-weak map from zero.

The cofibration classes of V and W are equal: both consist of degreewise admissible monomorphisms. -/
theorem ambientIsoCofibrations_eq :
    (isoWaldhausenCategory E).cofibrations = (ambientWaldhausenCategory F).cofibrations := by
  funext X Y f
  exact propext ((iso_isCofibration_iff E f).trans (ambient_isCofibration_iff F f).symm)

/-- Let E be preadditive, A abelian and F:E → A additive.
Let A_F be the full subcategory of bounded integer E-complexes K
whose ambient complex F(K) is acyclic, and J:A_F → Bounded(E)
its inclusion. Assume E is Quillen exact with a zero object and binary biproducts.
On Bounded(E), let V have degreewise admissible cofibrations and
isomorphism weak maps, and W the same cofibrations with F-detected
quasi-isomorphisms. Let C_W be the canonical full subcategory of
objects receiving a W-weak map from zero.

Every V-weak map is W-weak, since an isomorphism becomes an F-quasi-isomorphism. -/
theorem ambientIsoWeakEquivalences_le :
    (isoWaldhausenCategory E).weakEquivalences ≤ (ambientWaldhausenCategory F).weakEquivalences := by
  intro X Y f hf
  let _ : IsIso f := (iso_isWeakEquivalence_iff E f).mp hf
  apply (ambient_isWeakEquivalence_iff F f).mpr
  infer_instance

variable [F.IsExact]

/-- Let E be preadditive, A abelian and F:E → A additive.
Let A_F be the full subcategory of bounded integer E-complexes K
whose ambient complex F(K) is acyclic, and J:A_F → Bounded(E)
its inclusion. Assume E is Quillen exact with a zero object and binary biproducts.
On Bounded(E), let V have degreewise admissible cofibrations and
isomorphism weak maps, and W the same cofibrations with F-detected
quasi-isomorphisms. Let C_W be the canonical full subcategory of
objects receiving a W-weak map from zero. Assume F is exact.

A pushout of X → Y and X → Z along a degreewise admissible map, with X,Y,Z in A_F, also has its apex in A_F. -/
theorem ambientAcyclicObjects_pushout {X Y Z P : Bounded E}
    {i : X ⟶ Y} {f : X ⟶ Z} {inY : Y ⟶ P} {inZ : Z ⟶ P}
    (hi : degreewiseAdmissibleMonomorphisms E i) (hP : IsPushout i f inY inZ)
    (hX : ambientAcyclicObjects F X) (hY : ambientAcyclicObjects F Y)
    (hZ : ambientAcyclicObjects F Z) : ambientAcyclicObjects F P := by
  let _ := ambientWaldhausenCategory F
  exact (ambientAcyclicCanonical_iff F P).mpr
    ((ambientWaldhausen_gluing F).acyclicObjects_of_pushout i f inY inZ
      ((ambient_isCofibration_iff F i).mpr hi) hP
      ((ambientAcyclicCanonical_iff F X).mp hX)
      ((ambientAcyclicCanonical_iff F Y).mp hY)
      ((ambientAcyclicCanonical_iff F Z).mp hZ))

/-- Let E be preadditive, A abelian and F:E → A additive.
Let A_F be the full subcategory of bounded integer E-complexes K
whose ambient complex F(K) is acyclic, and J:A_F → Bounded(E)
its inclusion. Assume E is Quillen exact with a zero object and binary biproducts.
On Bounded(E), let V have degreewise admissible cofibrations and
isomorphism weak maps, and W the same cofibrations with F-detected
quasi-isomorphisms. Let C_W be the canonical full subcategory of
objects receiving a W-weak map from zero. Assume F is exact.

The canonical acyclic category C_W carries the restriction of V, with degreewise admissible cofibrations and isomorphism weak maps. -/
@[instance_reducible]
def ambientAcyclicCanonicalWaldhausenCategory :
    letI := Waldhausen.acyclicHasZeroObject (ambientWaldhausenCategory F)
    WaldhausenCategoryWithoutGluing (CanonicalAmbientAcyclic F) :=
  Waldhausen.acyclicWaldhausenCategory (isoWaldhausenCategory E) (ambientWaldhausenCategory F)
    (ambientIsoCofibrations_eq F) (ambientWaldhausen_gluing F)

omit [F.IsExact] in
/-- Let E be preadditive, A abelian and F:E → A additive.
Let A_F be the full subcategory of bounded integer E-complexes K
whose ambient complex F(K) is acyclic, and J:A_F → Bounded(E)
its inclusion. Assume E is Quillen exact with a zero object and binary biproducts.
On Bounded(E), let V have degreewise admissible cofibrations and
isomorphism weak maps, and W the same cofibrations with F-detected
quasi-isomorphisms. Let C_W be the canonical full subcategory of
objects receiving a W-weak map from zero.

The cofibration property on A_F consists of maps whose bounded components are admissible monomorphisms in every degree. -/
def ambientAcyclicCofibrations : MorphismProperty (AmbientAcyclic F) :=
  (degreewiseAdmissibleMonomorphisms E).inverseImage (ambientAcyclicι F)

/-- Let E be preadditive, A abelian and F:E → A additive.
Let A_F be the full subcategory of bounded integer E-complexes K
whose ambient complex F(K) is acyclic, and J:A_F → Bounded(E)
its inclusion. Assume E is Quillen exact with a zero object and binary biproducts.
On Bounded(E), let V have degreewise admissible cofibrations and
isomorphism weak maps, and W the same cofibrations with F-detected
quasi-isomorphisms. Let C_W be the canonical full subcategory of
objects receiving a W-weak map from zero. Assume F is exact.

An admissible span in A_F has a pushout in A_F, Bounded(E), and E in every degree. The cobase-change leg is degreewise admissible and the underlying raw complex is the original cochain pushout. -/
theorem exists_ambientAcyclicAdmissiblePushout {X Y Z : AmbientAcyclic F}
    (i : X ⟶ Y) (f : X ⟶ Z) (hi : ambientAcyclicCofibrations F i) :
    letI := hasPushout_hom_of_degreewiseAdmissibleMonomorphisms E i.hom f.hom hi
    ∃ (P : AmbientAcyclic F) (inY : Y ⟶ P) (inZ : Z ⟶ P),
      IsPushout i f inY inZ ∧ IsPushout i.hom f.hom inY.hom inZ.hom ∧
      (∀ j : ℤ, IsPushout (i.hom.hom.f j) (f.hom.hom.f j)
        (inY.hom.hom.f j) (inZ.hom.hom.f j)) ∧ ambientAcyclicCofibrations F inZ ∧
      P.obj.obj = pushout i.hom.hom f.hom.hom := by
  let _ := hasPushout_hom_of_degreewiseAdmissibleMonomorphisms E i.hom f.hom hi
  obtain ⟨P, inY, inZ, hP, _, hTerms, hadm, hRaw⟩ :=
    exists_boundedAdmissiblePushout E i.hom f.hom hi
  let Q : AmbientAcyclic F :=
    ⟨P, ambientAcyclicObjects_pushout F hi hP X.property Y.property Z.property⟩
  let inY' : Y ⟶ Q := ObjectProperty.homMk inY
  let inZ' : Z ⟶ Q := ObjectProperty.homMk inZ
  have hQ : IsPushout i f inY' inZ' := IsPushout.of_map_of_faithful (ambientAcyclicι F) hP
  exact ⟨Q, inY', inZ', hQ, hP, hTerms, hadm, hRaw⟩

/-- Let E be preadditive, A abelian and F:E → A additive.
Let A_F be the full subcategory of bounded integer E-complexes K
whose ambient complex F(K) is acyclic, and J:A_F → Bounded(E)
its inclusion. Assume E is Quillen exact with a zero object and binary biproducts.
On Bounded(E), let V have degreewise admissible cofibrations and
isomorphism weak maps, and W the same cofibrations with F-detected
quasi-isomorphisms. Let C_W be the canonical full subcategory of
objects receiving a W-weak map from zero. Assume F is exact.

Any admissible pushout square in A_F remains a pushout square after applying J to Bounded(E). -/
theorem ambientAcyclicPushout_ι {X Y Z P : AmbientAcyclic F}
    {i : X ⟶ Y} {f : X ⟶ Z} {inY : Y ⟶ P} {inZ : Z ⟶ P}
    (hi : ambientAcyclicCofibrations F i) (hP : IsPushout i f inY inZ) :
    IsPushout i.hom f.hom inY.hom inZ.hom := by
  let J := ambientAcyclicToCanonical F
  have hi₀ : (isoWaldhausenCategory E).cofibrations ((J.map i).hom) :=
    (iso_isCofibration_iff E i.hom).mpr hi
  have hCanon : IsPushout (J.map f) (J.map i) (J.map inZ) (J.map inY) := hP.flip.map J
  exact (Waldhausen.acyclicι_map_isPushout (isoWaldhausenCategory E)
    (ambientWaldhausenCategory F) (ambientIsoCofibrations_eq F) (ambientWaldhausen_gluing F)
    (J.map i) (J.map f) (J.map inZ) (J.map inY) hi₀ hCanon).flip

/-- Let E be preadditive, A abelian and F:E → A additive.
Let A_F be the full subcategory of bounded integer E-complexes K
whose ambient complex F(K) is acyclic, and J:A_F → Bounded(E)
its inclusion. Assume E is Quillen exact with a zero object and binary biproducts.
On Bounded(E), let V have degreewise admissible cofibrations and
isomorphism weak maps, and W the same cofibrations with F-detected
quasi-isomorphisms. Let C_W be the canonical full subcategory of
objects receiving a W-weak map from zero. Assume F is exact.

The Waldhausen data on A_F have degreewise admissible cofibrations, isomorphism weak equivalences and the inherited admissible pushouts. -/
@[instance_reducible, no_expose]
def ambientAcyclicWaldhausenCategory : WaldhausenCategoryWithoutGluing (AmbientAcyclic F) where
  cofibrations := ambientAcyclicCofibrations F
  weakEquivalences := MorphismProperty.isomorphisms (AmbientAcyclic F)
  cofibrations_isMultiplicative := by
    dsimp only [ambientAcyclicCofibrations]
    infer_instance
  cofibrations_respectsIso := by
    dsimp only [ambientAcyclicCofibrations]
    infer_instance
  weakEquivalences_isMultiplicative := inferInstance
  weakEquivalences_respectsIso := inferInstance
  zero_isCofibration K f := by
    change degreewiseAdmissibleMonomorphisms E f.hom
    let _ := Waldhausen.acyclicHasZeroObject (ambientWaldhausenCategory F)
    let _ := ambientAcyclicCanonicalWaldhausenCategory F
    let J := ambientAcyclicToCanonical F
    have hZero : IsZero (J.obj (0 : AmbientAcyclic F)) :=
      (Waldhausen.acyclic_isZero_iff (ambientWaldhausenCategory F) _).mpr
        ((ambientAcyclicι F).map_isZero (isZero_zero (AmbientAcyclic F)))
    let e := hZero.isoZero
    have h : IsCofibration (e.inv ≫ J.map f) := WaldhausenCategoryWithoutGluing.zero_isCofibration _ _
    have hcomp : IsCofibration (e.hom ≫ (e.inv ≫ J.map f)) :=
      WaldhausenCategoryWithoutGluing.cofibrations.comp_mem _ _
        (WaldhausenCategoryWithoutGluing.cofibrations.of_isIso e.hom) h
    have hf : IsCofibration (J.map f) := by simpa only [Iso.hom_inv_id_assoc] using hcomp
    exact (iso_isCofibration_iff E f.hom).mp
      ((Waldhausen.isCofibration_acyclicWaldhausenCategory_iff (isoWaldhausenCategory E)
        (ambientWaldhausenCategory F) (ambientIsoCofibrations_eq F) (ambientWaldhausen_gluing F)
        (J.map f)).mp hf)
  cofibration_pushout i hi Z f := by
    let J := ambientAcyclicToCanonical F
    have hi₀ : (isoWaldhausenCategory E).cofibrations ((J.map i).hom) :=
      (iso_isCofibration_iff E i.hom).mpr hi
    obtain ⟨P, inZ, inY, _, hP, hadm⟩ :=
      Waldhausen.acyclic_cofibration_pushout (isoWaldhausenCategory E)
        (ambientWaldhausenCategory F) (ambientIsoCofibrations_eq F) (ambientWaldhausen_gluing F)
        (J.map i) hi₀ (J.obj Z) (J.map f)
    let Q := (ambientAcyclicFromCanonical F).obj P
    let inZ' : Z ⟶ Q := ObjectProperty.homMk inZ.hom
    let inY' : _ ⟶ Q := ObjectProperty.homMk inY.hom
    refine ⟨Q, inZ', inY', IsPushout.of_map_of_faithful (ambientAcyclicι F) hP, ?_⟩
    exact (iso_isCofibration_iff E inZ.hom).mp hadm

/-- Let E be preadditive, A abelian and F:E → A additive.
Let A_F be the full subcategory of bounded integer E-complexes K
whose ambient complex F(K) is acyclic, and J:A_F → Bounded(E)
its inclusion. Assume E is Quillen exact with a zero object and binary biproducts.
On Bounded(E), let V have degreewise admissible cofibrations and
isomorphism weak maps, and W the same cofibrations with F-detected
quasi-isomorphisms. Let C_W be the canonical full subcategory of
objects receiving a W-weak map from zero. Assume F is exact.

A map in the inherited structure on A_F is a cofibration if and only if every underlying degree component is an admissible monomorphism. -/
theorem ambientAcyclic_isCofibration_iff {X Y : AmbientAcyclic F} (f : X ⟶ Y) :
    letI := ambientAcyclicWaldhausenCategory F
    IsCofibration f ↔ ∀ j : ℤ, ExactCategory.IsAdmissibleMono (f.hom.hom.f j) := Iff.rfl

/-- Let E be preadditive, A abelian and F:E → A additive.
Let A_F be the full subcategory of bounded integer E-complexes K
whose ambient complex F(K) is acyclic, and J:A_F → Bounded(E)
its inclusion. Assume E is Quillen exact with a zero object and binary biproducts.
On Bounded(E), let V have degreewise admissible cofibrations and
isomorphism weak maps, and W the same cofibrations with F-detected
quasi-isomorphisms. Let C_W be the canonical full subcategory of
objects receiving a W-weak map from zero. Assume F is exact.

A map in the inherited structure on A_F is weak if and only if it is an isomorphism in A_F. -/
theorem ambientAcyclic_isWeakEquivalence_iff {X Y : AmbientAcyclic F} (f : X ⟶ Y) :
    letI := ambientAcyclicWaldhausenCategory F
    IsWeakEquivalence f ↔ IsIso f := Iff.rfl

/-- Let E be preadditive, A abelian and F:E → A additive.
Let A_F be the full subcategory of bounded integer E-complexes K
whose ambient complex F(K) is acyclic, and J:A_F → Bounded(E)
its inclusion. Assume E is Quillen exact with a zero object and binary biproducts.
On Bounded(E), let V have degreewise admissible cofibrations and
isomorphism weak maps, and W the same cofibrations with F-detected
quasi-isomorphisms. Let C_W be the canonical full subcategory of
objects receiving a W-weak map from zero. Assume F is exact.

The forward comparison A_F → C_W is Waldhausen exact for the inherited V structures. -/
theorem ambientAcyclicToCanonical_isWaldhausenExact :
    letI := Waldhausen.acyclicHasZeroObject (ambientWaldhausenCategory F)
    @Functor.IsWaldhausenExact (AmbientAcyclic F) _ _ (ambientAcyclicWaldhausenCategory F)
      (CanonicalAmbientAcyclic F) _ _ (ambientAcyclicCanonicalWaldhausenCategory F)
      (ambientAcyclicToCanonical F) := by
  let _ := Waldhausen.acyclicHasZeroObject (ambientWaldhausenCategory F)
  refine @Functor.IsWaldhausenExact.mk (AmbientAcyclic F) _ _ (ambientAcyclicWaldhausenCategory F)
    (CanonicalAmbientAcyclic F) _ _ (ambientAcyclicCanonicalWaldhausenCategory F)
    (ambientAcyclicToCanonical F) ?_ ?_ ?_ ?_
  · intro X hX
    exact (Waldhausen.acyclic_isZero_iff (ambientWaldhausenCategory F) _).mpr
      ((ambientAcyclicι F).map_isZero hX)
  · intro X Y f hf
    exact (Waldhausen.isCofibration_acyclicWaldhausenCategory_iff (isoWaldhausenCategory E)
      (ambientWaldhausenCategory F) (ambientIsoCofibrations_eq F) (ambientWaldhausen_gluing F)
      ((ambientAcyclicToCanonical F).map f)).mpr
      ((iso_isCofibration_iff E f.hom).mpr ((ambientAcyclic_isCofibration_iff F f).mp hf))
  · intro X Y f hf
    let _ : IsIso f := (ambientAcyclic_isWeakEquivalence_iff F f).mp hf
    exact (Waldhausen.isWeakEquivalence_acyclicWaldhausenCategory_iff (isoWaldhausenCategory E)
      (ambientWaldhausenCategory F) (ambientIsoCofibrations_eq F) (ambientWaldhausen_gluing F)
      ((ambientAcyclicToCanonical F).map f)).mpr
      ((iso_isWeakEquivalence_iff E _).mpr inferInstance)
  · intro X Y Z P i f inl inr hi hP
    exact hP.map (ambientAcyclicToCanonical F)

/-- Let E be preadditive, A abelian and F:E → A additive.
Let A_F be the full subcategory of bounded integer E-complexes K
whose ambient complex F(K) is acyclic, and J:A_F → Bounded(E)
its inclusion. Assume E is Quillen exact with a zero object and binary biproducts.
On Bounded(E), let V have degreewise admissible cofibrations and
isomorphism weak maps, and W the same cofibrations with F-detected
quasi-isomorphisms. Let C_W be the canonical full subcategory of
objects receiving a W-weak map from zero. Assume F is exact.

The inverse comparison C_W → A_F is Waldhausen exact for the inherited V structures. -/
theorem ambientAcyclicFromCanonical_isWaldhausenExact :
    letI := Waldhausen.acyclicHasZeroObject (ambientWaldhausenCategory F)
    @Functor.IsWaldhausenExact (CanonicalAmbientAcyclic F) _ _
      (ambientAcyclicCanonicalWaldhausenCategory F) (AmbientAcyclic F) _ _
      (ambientAcyclicWaldhausenCategory F) (ambientAcyclicFromCanonical F) := by
  let _ := Waldhausen.acyclicHasZeroObject (ambientWaldhausenCategory F)
  refine @Functor.IsWaldhausenExact.mk (CanonicalAmbientAcyclic F) _ _
    (ambientAcyclicCanonicalWaldhausenCategory F) (AmbientAcyclic F) _ _
    (ambientAcyclicWaldhausenCategory F) (ambientAcyclicFromCanonical F) ?_ ?_ ?_ ?_
  · intro X hX
    exact IsZero.of_full_of_faithful_of_isZero (ambientAcyclicι F)
      ((ambientAcyclicFromCanonical F).obj X)
      ((Waldhausen.acyclic_isZero_iff (ambientWaldhausenCategory F) X).mp hX)
  · intro X Y f hf
    exact (ambientAcyclic_isCofibration_iff F _).mpr
      ((iso_isCofibration_iff E f.hom).mp
        ((Waldhausen.isCofibration_acyclicWaldhausenCategory_iff (isoWaldhausenCategory E)
          (ambientWaldhausenCategory F) (ambientIsoCofibrations_eq F) (ambientWaldhausen_gluing F)
          f).mp hf))
  · intro X Y f hf
    have hIso : IsIso f.hom := (iso_isWeakEquivalence_iff E f.hom).mp
      ((Waldhausen.isWeakEquivalence_acyclicWaldhausenCategory_iff (isoWaldhausenCategory E)
        (ambientWaldhausenCategory F) (ambientIsoCofibrations_eq F) (ambientWaldhausen_gluing F)
        f).mp hf)
    let _ : IsIso f := (ObjectProperty.isIso_hom_iff f).mp hIso
    exact (ambientAcyclic_isWeakEquivalence_iff F _).mpr inferInstance
  · intro X Y Z P i f inl inr hi hP
    exact hP.map (ambientAcyclicFromCanonical F)

/-- Let E be preadditive, A abelian and F:E → A additive.
Let A_F be the full subcategory of bounded integer E-complexes K
whose ambient complex F(K) is acyclic, and J:A_F → Bounded(E)
its inclusion. Assume E is Quillen exact with a zero object and binary biproducts.
On Bounded(E), let V have degreewise admissible cofibrations and
isomorphism weak maps, and W the same cofibrations with F-detected
quasi-isomorphisms. Let C_W be the canonical full subcategory of
objects receiving a W-weak map from zero. Assume F is exact.

The inclusion J is Waldhausen exact into Bounded(E) with its isomorphism weak structure V. -/
theorem ambientAcyclicι_iso_isWaldhausenExact :
    @Functor.IsWaldhausenExact (AmbientAcyclic F) _ _ (ambientAcyclicWaldhausenCategory F)
      (Bounded E) _ _ (isoWaldhausenCategory E) (ambientAcyclicι F) := by
  let _ := Waldhausen.acyclicHasZeroObject (ambientWaldhausenCategory F)
  exact @Functor.IsWaldhausenExact.comp (AmbientAcyclic F) _ _ (ambientAcyclicWaldhausenCategory F)
    (CanonicalAmbientAcyclic F) _ _ (ambientAcyclicCanonicalWaldhausenCategory F)
    (Bounded E) _ _ (isoWaldhausenCategory E) (ambientAcyclicToCanonical F)
    (Waldhausen.acyclicι (ambientWaldhausenCategory F))
    (ambientAcyclicToCanonical_isWaldhausenExact F)
    (Waldhausen.acyclicι_isWaldhausenExact (isoWaldhausenCategory E)
      (ambientWaldhausenCategory F) (ambientIsoCofibrations_eq F) (ambientWaldhausen_gluing F))

/-- Let E be preadditive, A abelian and F:E → A additive.
Let A_F be the full subcategory of bounded integer E-complexes K
whose ambient complex F(K) is acyclic, and J:A_F → Bounded(E)
its inclusion. Assume E is Quillen exact with a zero object and binary biproducts.
On Bounded(E), let V have degreewise admissible cofibrations and
isomorphism weak maps, and W the same cofibrations with F-detected
quasi-isomorphisms. Let C_W be the canonical full subcategory of
objects receiving a W-weak map from zero. Assume F is exact.

The inclusion J is Waldhausen exact into Bounded(E) with its ambient weak structure W. -/
theorem ambientAcyclicι_ambient_isWaldhausenExact :
    @Functor.IsWaldhausenExact (AmbientAcyclic F) _ _ (ambientAcyclicWaldhausenCategory F)
      (Bounded E) _ _ (ambientWaldhausenCategory F) (ambientAcyclicι F) := by
  let _ := Waldhausen.acyclicHasZeroObject (ambientWaldhausenCategory F)
  exact @Functor.IsWaldhausenExact.comp (AmbientAcyclic F) _ _ (ambientAcyclicWaldhausenCategory F)
    (CanonicalAmbientAcyclic F) _ _ (ambientAcyclicCanonicalWaldhausenCategory F)
    (Bounded E) _ _ (ambientWaldhausenCategory F) (ambientAcyclicToCanonical F)
    (Waldhausen.acyclicι (ambientWaldhausenCategory F))
    (ambientAcyclicToCanonical_isWaldhausenExact F)
    (Waldhausen.acyclicι_toLarger_isWaldhausenExact (isoWaldhausenCategory E)
      (ambientWaldhausenCategory F) (ambientIsoCofibrations_eq F) (ambientIsoWeakEquivalences_le F)
      (ambientWaldhausen_gluing F))

/-- Let E be preadditive, A abelian and F:E → A additive.
Let A_F be the full subcategory of bounded integer E-complexes K
whose ambient complex F(K) is acyclic, and J:A_F → Bounded(E)
its inclusion. Assume E is Quillen exact with a zero object and binary biproducts.
On Bounded(E), let V have degreewise admissible cofibrations and
isomorphism weak maps, and W the same cofibrations with F-detected
quasi-isomorphisms. Let C_W be the canonical full subcategory of
objects receiving a W-weak map from zero. Assume F is exact.

For a bounded cofiber sequence X —i→ Y → Z, the quotient Z lies in A_F if and only if i is W-weak. -/
theorem ambientCofiber_quotient_mem_iff {X Y Z : Bounded E} (i : X ⟶ Y) (p : Y ⟶ Z)
    (hSeq : letI := ambientWaldhausenCategory F; IsCofiberSequence i p) :
    letI := ambientWaldhausenCategory F
    ambientAcyclicObjects F Z ↔ IsWeakEquivalence i :=
  (ambientCofiber_isWeakEquivalence_iff_quotient_acyclic F i p hSeq).symm

omit [F.IsExact] in
/-- Let E be preadditive, A abelian and F:E → A additive.
Let A_F be the full subcategory of bounded integer E-complexes K
whose ambient complex F(K) is acyclic, and J:A_F → Bounded(E)
its inclusion. Assume E is Quillen exact with a zero object and binary biproducts.
On Bounded(E), let V have degreewise admissible cofibrations and
isomorphism weak maps, and W the same cofibrations with F-detected
quasi-isomorphisms. Let C_W be the canonical full subcategory of
objects receiving a W-weak map from zero.

The bounded structures V and W have the same cofiber sequences, since they have the same cofibrations and chosen zero pushouts. -/
theorem iso_isCofiberSequence_iff_ambient {X Y Z : Bounded E} (i : X ⟶ Y) (p : Y ⟶ Z) :
    @IsCofiberSequence (Bounded E) _ _ (isoWaldhausenCategory E) X Y Z i p ↔
      @IsCofiberSequence (Bounded E) _ _ (ambientWaldhausenCategory F) X Y Z i p :=
  and_congr ((iso_isCofibration_iff E i).trans (ambient_isCofibration_iff F i).symm) Iff.rfl

/-- Let E be preadditive, A abelian and F:E → A additive.
Let A_F be the full subcategory of bounded integer E-complexes K
whose ambient complex F(K) is acyclic, and J:A_F → Bounded(E)
its inclusion. Assume E is Quillen exact with a zero object and binary biproducts.
On Bounded(E), let V have degreewise admissible cofibrations and
isomorphism weak maps, and W the same cofibrations with F-detected
quasi-isomorphisms. Let C_W be the canonical full subcategory of
objects receiving a W-weak map from zero. Assume F is exact.

A row in A_F is a cofiber sequence in its inherited V structure exactly when its underlying bounded row is a cofiber sequence for V. -/
theorem ambientAcyclic_isCofiberSequence_iff {X Y Z : AmbientAcyclic F}
    (i : X ⟶ Y) (p : Y ⟶ Z) :
    @IsCofiberSequence (AmbientAcyclic F) _ _ (ambientAcyclicWaldhausenCategory F) X Y Z i p ↔
      @IsCofiberSequence (Bounded E) _ _ (isoWaldhausenCategory E)
        X.obj Y.obj Z.obj i.hom p.hom := by
  let _ := ambientAcyclicWaldhausenCategory F
  let _ := isoWaldhausenCategory E
  let _ := Waldhausen.acyclicHasZeroObject (ambientWaldhausenCategory F)
  let _ := ambientAcyclicCanonicalWaldhausenCategory F
  let J := ambientAcyclicToCanonical F
  have hCanon := Waldhausen.acyclic_isCofiberSequence_iff (isoWaldhausenCategory E)
    (ambientWaldhausenCategory F) (ambientIsoCofibrations_eq F) (ambientWaldhausen_gluing F)
    (J.map i) (J.map p)
  constructor
  · intro hS
    exact hCanon.mp ((ambientAcyclicToCanonical_isWaldhausenExact F).map_cofibrationSequence hS)
  · intro hS
    exact (ambientAcyclicFromCanonical_isWaldhausenExact F).map_cofibrationSequence (hCanon.mpr hS)

/-- Let E be preadditive, A abelian and F:E → A additive.
Let A_F be the full subcategory of bounded integer E-complexes K
whose ambient complex F(K) is acyclic, and J:A_F → Bounded(E)
its inclusion. Assume E is Quillen exact with a zero object and binary biproducts.
On Bounded(E), let V have degreewise admissible cofibrations and
isomorphism weak maps, and W the same cofibrations with F-detected
quasi-isomorphisms. Let C_W be the canonical full subcategory of
objects receiving a W-weak map from zero. Assume F is exact.

The inherited isomorphism weak structure on A_F satisfies the gluing axiom. -/
theorem ambientAcyclic_gluing :
    letI := ambientAcyclicWaldhausenCategory F
    WaldhausenGluingAxiom (C := AmbientAcyclic F) := by
  let _ := ambientAcyclicWaldhausenCategory F
  let _ := isoWaldhausenCategory E
  let _ := Waldhausen.acyclicHasZeroObject (ambientWaldhausenCategory F)
  let _ := ambientAcyclicCanonicalWaldhausenCategory F
  let J := ambientAcyclicToCanonical F
  let hJ := ambientAcyclicToCanonical_isWaldhausenExact F
  have hG := Waldhausen.acyclicGluingAxiom (isoWaldhausenCategory E)
    (ambientWaldhausenCategory F) (ambientIsoCofibrations_eq F) (ambientWaldhausen_gluing F)
    (isoWaldhausen_gluing E)
  constructor
  intro X Y Z P X' Y' Z' P' i f inY inZ i' f' inY' inZ'
    hP hP' x y z p hi hi' wi wf wY wZ hx hy hz
  have hp : IsWeakEquivalence (J.map p) := hG.gluing (hP.map J) (hP'.map J)
    (J.map x) (J.map y) (J.map z) (J.map p) (hJ.map_cofibration i hi) (hJ.map_cofibration i' hi')
    (by simpa only [← J.map_comp] using congrArg J.map wi)
    (by simpa only [← J.map_comp] using congrArg J.map wf)
    (by simpa only [← J.map_comp] using congrArg J.map wY)
    (by simpa only [← J.map_comp] using congrArg J.map wZ)
    (hJ.map_weakEquivalence x hx) (hJ.map_weakEquivalence y hy) (hJ.map_weakEquivalence z hz)
  exact (ambientAcyclicFromCanonical_isWaldhausenExact F).map_weakEquivalence (J.map p) hp

variable [F.Full] [F.Faithful] [F.ReflectsAdmissibleExact]

/-- Let E be preadditive, A abelian and F:E → A additive.
Let A_F be the full subcategory of bounded integer E-complexes K
whose ambient complex F(K) is acyclic, and J:A_F → Bounded(E)
its inclusion. Assume E is Quillen exact with a zero object and binary biproducts.
On Bounded(E), let V have degreewise admissible cofibrations and
isomorphism weak maps, and W the same cofibrations with F-detected
quasi-isomorphisms. Let C_W be the canonical full subcategory of
objects receiving a W-weak map from zero. Assume F is exact. Assume F is fully faithful, reflects admissible exactness, and has essential image closed under kernels of epimorphisms between image objects.

For bounded K, membership in A_F is equivalent to existence of all-degree source cycle conflations and differential factorizations. -/
theorem ambientAcyclicObjects_iff_admissibleData (K : Bounded E)
    (hKernelClosure : ∀ {U V : A} (f : U ⟶ V) [Epi f],
      F.essImage U → F.essImage V → F.essImage (kernel f)) :
    ambientAcyclicObjects F K ↔ Nonempty (AmbientCycles.AdmissibleAcyclicData K) :=
  AmbientCycles.ambient_acyclic_iff_admissibleData F K hKernelClosure

end CochainComplex.Bounded

end
