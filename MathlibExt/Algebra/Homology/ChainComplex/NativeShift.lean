/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import Mathlib.Algebra.Homology.CochainComplexOpposite
public import Mathlib.Algebra.Homology.HomotopyCategory.Shift

/-!
# Signed shifts of integer chain complexes

For a preadditive category C and a ∈ ℤ, the signed shift S_a of an integer chain complex K has
degree-i term K_{i−a} and differential (−1)^a d_K. It is obtained by reversing indices to
cochains, applying their signed shift, and reversing indices back. A chain map shifts without an
additional sign. Canonical isomorphisms S₀ ≅ id and S_{a+b} ≅ S_b ∘ S_a satisfy the unit and
associativity laws.

With the translation convention having terms K_{i+p}, the shift parameter is a = −p. The sign
convention follows Weibel, An Introduction to Homological Algebra (1994), §1.2.8.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Functor HomologicalComplex

namespace ChainComplex

universe u v

variable (C : Type u) [Category.{v} C] [Preadditive C]

/-- Let C be a preadditive category, and let a ∈ ℤ. The functor nativeShift C a sends an integer
chain complex K to the signed shift S_a K, whose degree-i term is K_{i−a} and whose differential
is (−1)^a times the corresponding differential of K. It transports the cochain shift through
reversal of integer indices. -/
noncomputable def nativeShift (a : ℤ) : ChainComplex C ℤ ⥤ ChainComplex C ℤ :=
  (cochainComplexEquivalence C).functor ⋙
    CategoryTheory.shiftFunctor (CochainComplex C ℤ) a ⋙
      (cochainComplexEquivalence C).inverse

/-- Let C be a preadditive category, and let a ∈ ℤ. The signed shift S_a on integer chain complexes
is additive: it sends zero chain maps to zero and satisfies S_a(f+g) = S_a(f)+S_a(g). -/
instance nativeShift_additive (a : ℤ) : (nativeShift C a).Additive := by
  dsimp only [nativeShift, cochainComplexEquivalence]
  infer_instance

variable {C}

/-- Let C be a preadditive category, K an integer chain complex, and a,i ∈ ℤ. The degree-i term of
S_a K equals K_{−(−i+a)}, canonically the same degree as K_{i−a}. -/
@[simp]
lemma nativeShift_obj_X (K : ChainComplex C ℤ) (a i : ℤ) :
    ((nativeShift C a).obj K).X i = K.X (-(-i + a)) := rfl

/-- Let C be a preadditive category, K an integer chain complex, and a,i,j ∈ ℤ. The shifted
differential is d_{S_a K,i,j} = (−1)^a d_{K,−(−i+a),−(−j+a)}. The sign acts through the integer
scalar action on morphisms of C. -/
@[simp]
lemma nativeShift_obj_d (K : ChainComplex C ℤ) (a i j : ℤ) :
    ((nativeShift C a).obj K).d i j =
      a.negOnePow • K.d (-(-i + a)) (-(-j + a)) := rfl

/-- Let C be a preadditive category, f : K → L a map of integer chain complexes, and a,i ∈ ℤ. The
degree-i component of S_a(f) equals f_{−(−i+a)}; shifting the map introduces no extra sign. -/
@[simp]
lemma nativeShift_map_f {K L : ChainComplex C ℤ} (f : K ⟶ L) (a i : ℤ) :
    ((nativeShift C a).map f).f i = f.f (-(-i + a)) := rfl

/-- Let C be a preadditive category, K an integer chain complex, and a,i ∈ ℤ. The canonical
reindexing isomorphism nativeShiftObjXIso identifies (S_a K)_i with K_{i−a}. -/
noncomputable def nativeShiftObjXIso (K : ChainComplex C ℤ) (a i : ℤ) :
    ((nativeShift C a).obj K).X i ≅ K.X (i - a) :=
  K.XIsoOfEq (show -(-i + a) = i - a by omega)

/-- Let C be a preadditive category, K an integer chain complex, and a,i,j ∈ ℤ with i−a = j. The
specified-coordinate isomorphism identifies (S_a K)_i with K_j. -/
noncomputable def nativeShiftObjXIso' (K : ChainComplex C ℤ) (a i j : ℤ)
    (h : i - a = j) : ((nativeShift C a).obj K).X i ≅ K.X j :=
  nativeShiftObjXIso K a i ≪≫ K.XIsoOfEq h

/-- Let C be a preadditive category, K an integer chain complex, and a,i,j ∈ ℤ. Write e_i : (S_a
K)_i ≅ K_{i−a} and e_j : (S_a K)_j ≅ K_{j−a} for the canonical term isomorphisms. Then d_{S_a
K,i,j} = e_i.hom ≫ ((−1)^a d_{K,i−a,j−a}) ≫ e_j.inv. -/
lemma nativeShiftObjXIso_d (K : ChainComplex C ℤ) (a i j : ℤ) :
    ((nativeShift C a).obj K).d i j =
      (nativeShiftObjXIso K a i).hom ≫
        (a.negOnePow • K.d (i - a) (j - a)) ≫
          (nativeShiftObjXIso K a j).inv := by
  have hi : -(-i + a) = i - a := by omega
  have hj : -(-j + a) = j - a := by omega
  change a.negOnePow • K.d (-(-i + a)) (-(-j + a)) =
    (K.XIsoOfEq hi).hom ≫ (a.negOnePow • K.d (i - a) (j - a)) ≫ (K.XIsoOfEq hj).inv
  have h := (K.XIsoOfEq_hom_comp_d_assoc hi (j - a) (K.XIsoOfEq hj).inv).trans
    (K.d_comp_XIsoOfEq_inv hj (-(-i + a)))
  simpa only [Linear.comp_units_smul, Linear.units_smul_comp] using
    congrArg (fun f : K.X (-(-i + a)) ⟶ K.X (-(-j + a)) => a.negOnePow • f) h.symm

/-- Let C be a preadditive category, K an integer chain complex, and a,i,j,i′,j′ ∈ ℤ with i−a = i′
and j−a = j′. For the coordinate isomorphisms e_i : (S_a K)_i ≅ K_i′ and e_j : (S_a K)_j ≅ K_j′,
the shifted differential is e_i.hom ≫ ((−1)^a d_K,i′,j′) ≫ e_j.inv. -/
lemma nativeShiftObjXIso'_d (K : ChainComplex C ℤ) (a i j i' j' : ℤ)
    (hi : i - a = i') (hj : j - a = j') :
    ((nativeShift C a).obj K).d i j =
      (nativeShiftObjXIso' K a i i' hi).hom ≫
        (a.negOnePow • K.d i' j') ≫ (nativeShiftObjXIso' K a j j' hj).inv := by
  subst i'
  subst j'
  simpa only [nativeShiftObjXIso', XIsoOfEq_rfl, Iso.trans_refl] using
    nativeShiftObjXIso_d K a i j

/-- Let C be a preadditive category, K an integer chain complex, and a,i,j,i′,j′ ∈ ℤ with i−a = i′
and j−a = j′. For the specified term isomorphisms e_i and e_j, one has e_i.inv ≫ d_{S_a K,i,j} ≫
e_j.hom = (−1)^a d_K,i′,j′. -/
lemma nativeShiftObjXIso'_inv_d_hom (K : ChainComplex C ℤ) (a i j i' j' : ℤ)
    (hi : i - a = i') (hj : j - a = j') :
    (nativeShiftObjXIso' K a i i' hi).inv ≫
        ((nativeShift C a).obj K).d i j ≫ (nativeShiftObjXIso' K a j j' hj).hom =
      a.negOnePow • K.d i' j' := by
  rw [nativeShiftObjXIso'_d K a i j i' j' hi hj]
  simp only [Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id]

/-- Let C be a preadditive category, f : K → L a map of integer chain complexes, and a,i ∈ ℤ. If
e_K,i and e_L,i identify the shifted terms with degree i−a, then S_a(f)_i ≫ e_L,i.hom =
e_K,i.hom ≫ f_{i−a}. -/
@[reassoc]
lemma nativeShiftObjXIso_naturality {K L : ChainComplex C ℤ}
    (f : K ⟶ L) (a i : ℤ) :
    ((nativeShift C a).map f).f i ≫ (nativeShiftObjXIso L a i).hom =
      (nativeShiftObjXIso K a i).hom ≫ f.f (i - a) := by
  change f.f (-(-i + a)) ≫
      (L.XIsoOfEq (show -(-i + a) = i - a by omega)).hom =
    (K.XIsoOfEq (show -(-i + a) = i - a by omega)).hom ≫ f.f (i - a)
  exact XIsoOfEq_hom_naturality f (show -(-i + a) = i - a by omega)

/-- Let C be a preadditive category, f : K → L a map of integer chain complexes, and a,i,j ∈ ℤ with
i−a = j. The specified term isomorphisms satisfy S_a(f)_i ≫ e_L,i.hom = e_K,i.hom ≫ f_j. -/
@[reassoc]
lemma nativeShiftObjXIso'_naturality {K L : ChainComplex C ℤ}
    (f : K ⟶ L) (a i j : ℤ) (h : i - a = j) :
    ((nativeShift C a).map f).f i ≫ (nativeShiftObjXIso' L a i j h).hom =
      (nativeShiftObjXIso' K a i j h).hom ≫ f.f j := by
  subst j
  simpa only [nativeShiftObjXIso', XIsoOfEq_rfl, Iso.trans_refl] using
    nativeShiftObjXIso_naturality f a i

/-- Let C be a preadditive category, f : K → L a map of integer chain complexes, and a,i,j ∈ ℤ with
i−a = j. The specified coordinates satisfy e_K,i.inv ≫ S_a(f)_i ≫ e_L,i.hom = f_j. -/
lemma nativeShiftObjXIso'_inv_map_f_hom {K L : ChainComplex C ℤ}
    (f : K ⟶ L) (a i j : ℤ) (h : i - a = j) :
    (nativeShiftObjXIso' K a i j h).inv ≫
        ((nativeShift C a).map f).f i ≫ (nativeShiftObjXIso' L a i j h).hom = f.f j := by
  rw [nativeShiftObjXIso'_naturality]
  exact (nativeShiftObjXIso' K a i j h).inv_hom_id_assoc _

variable (C)

/-- Let C be a preadditive category, The signed shift by zero has a canonical natural isomorphism η
: S₀ ≅ id on integer chain complexes. Its components are the reindexing maps identifying
K_{−(−i)} with K_i. -/
noncomputable def nativeShiftZero : nativeShift C 0 ≅ 𝟭 (ChainComplex C ℤ) :=
  let E := cochainComplexEquivalence C
  isoWhiskerRight
      (isoWhiskerLeft E.functor
        (CategoryTheory.shiftFunctorZero (CochainComplex C ℤ) ℤ)) E.inverse ≪≫
    isoWhiskerRight (Functor.rightUnitor E.functor) E.inverse ≪≫ E.unitIso.symm

/-- Let C be a preadditive category, and let a,b,s ∈ ℤ with a+b = s. There is a canonical natural
isomorphism α_{a,b} : S_s ≅ S_b ∘ S_a, identifying a single shift by s with first shifting by a
and then by b. -/
noncomputable def nativeShiftAdd' (a b ab : ℤ) (h : a + b = ab) :
    nativeShift C ab ≅ nativeShift C a ⋙ nativeShift C b :=
  let E := cochainComplexEquivalence C
  let Sa := CategoryTheory.shiftFunctor (CochainComplex C ℤ) a
  let Sb := CategoryTheory.shiftFunctor (CochainComplex C ℤ) b
  isoWhiskerRight
      (isoWhiskerLeft E.functor
        (CategoryTheory.shiftFunctorAdd' (CochainComplex C ℤ) a b ab h)) E.inverse ≪≫
    isoWhiskerRight
      ((Functor.rightUnitor (E.functor ⋙ Sa)).symm ≪≫
        isoWhiskerLeft (E.functor ⋙ Sa) E.counitIso.symm) (Sb ⋙ E.inverse)

/-- Let C be a preadditive category, and let a,b ∈ ℤ. The canonical natural isomorphism α_{a,b} :
S_{a+b} ≅ S_b ∘ S_a compares a shift by the sum with the two successive signed shifts. -/
noncomputable def nativeShiftAdd (a b : ℤ) :
    nativeShift C (a + b) ≅ nativeShift C a ⋙ nativeShift C b :=
  nativeShiftAdd' C a b (a + b) rfl

variable {C}

/-- Let C be a preadditive category, K an integer chain complex, and i ∈ ℤ. The degree-i component
of η_K : S₀ K → K is the canonical equality isomorphism K_{−(−i+0)} → K_i. -/
lemma nativeShiftZero_hom_app_f (K : ChainComplex C ℤ) (i : ℤ) :
    ((nativeShiftZero C).hom.app K).f i =
      (K.XIsoOfEq (show -(-i + 0) = i by omega)).hom := by
  have h₁ : -(-i + 0) = -(-i) := by omega
  have h₂ : -(-i) = i := by omega
  change (K.XIsoOfEq h₁).hom ≫ 𝟙 (K.X (-(-i))) ≫ (K.XIsoOfEq h₂).hom = _
  simp only [Category.id_comp, XIsoOfEq, eqToIso, eqToHom_trans]

/-- Let C be a preadditive category, K an integer chain complex, and i ∈ ℤ. The degree-i component
of η_K⁻¹ : K → S₀ K is the canonical equality map K_i → K_{−(−i+0)}. -/
lemma nativeShiftZero_inv_app_f (K : ChainComplex C ℤ) (i : ℤ) :
    ((nativeShiftZero C).inv.app K).f i =
      (K.XIsoOfEq (show i = -(-i + 0) by omega)).hom := by
  have h₁ : i = -(-i) := by omega
  have h₂ : -(-i) = -(-i + 0) := by omega
  change ((K.XIsoOfEq h₁).hom ≫ 𝟙 (K.X (-(-i)))) ≫ (K.XIsoOfEq h₂).hom = _
  simp only [Category.comp_id, XIsoOfEq, eqToIso, eqToHom_trans]

/-- Let C be a preadditive category, K an integer chain complex, and a,b,s,i ∈ ℤ with a+b = s. The
degree-i component of α_{a,b,K} is the canonical equality map from K_{−(−i+s)} to
K_{−(−(−(−i+b))+a)}. Both indices equal i−a−b, and no scalar sign is added to this map. -/
lemma nativeShiftAdd'_hom_app_f (K : ChainComplex C ℤ)
    (a b ab : ℤ) (h : a + b = ab) (i : ℤ) :
    ((nativeShiftAdd' C a b ab h).hom.app K).f i =
      (K.XIsoOfEq (show -(-i + ab) = -(-(-(-i + b)) + a) by omega)).hom := by
  unfold nativeShiftAdd'
  rw [CochainComplex.shiftFunctorAdd'_eq]
  have h₁ : -(-i + ab) = -((-i + b) + a) := by omega
  have h₂ : -((-i + b) + a) = -(-(-(-i + b)) + a) := by omega
  change (K.XIsoOfEq h₁).hom ≫ 𝟙 (K.X (-((-i + b) + a))) ≫ (K.XIsoOfEq h₂).hom = _
  simp only [Category.id_comp, XIsoOfEq, eqToIso, eqToHom_trans]

/-- Let C be a preadditive category, K an integer chain complex, and a,b,s,i ∈ ℤ with a+b = s. The
degree-i component of α_{a,b,K}⁻¹ is the equality map from K_{−(−(−(−i+b))+a)} to K_{−(−i+s)},
both in degree i−a−b. -/
lemma nativeShiftAdd'_inv_app_f (K : ChainComplex C ℤ)
    (a b ab : ℤ) (h : a + b = ab) (i : ℤ) :
    ((nativeShiftAdd' C a b ab h).inv.app K).f i =
      (K.XIsoOfEq (show -(-(-(-i + b)) + a) = -(-i + ab) by omega)).hom := by
  unfold nativeShiftAdd'
  rw [CochainComplex.shiftFunctorAdd'_eq]
  have h₁ : -(-(-(-i + b)) + a) = -((-i + b) + a) := by omega
  have h₂ : -((-i + b) + a) = -(-i + ab) := by omega
  change ((K.XIsoOfEq h₁).hom ≫ 𝟙 (K.X (-((-i + b) + a)))) ≫ (K.XIsoOfEq h₂).hom = _
  simp only [Category.comp_id, XIsoOfEq, eqToIso, eqToHom_trans]

/-- Let C be a preadditive category, K an integer chain complex, and a,b,i ∈ ℤ. The degree-i
component of S_{a+b}K → S_b(S_a K) is the canonical equality map K_{−(−i+(a+b))} →
K_{−(−(−(−i+b))+a)}. -/
lemma nativeShiftAdd_hom_app_f (K : ChainComplex C ℤ) (a b i : ℤ) :
    ((nativeShiftAdd C a b).hom.app K).f i =
      (K.XIsoOfEq (show -(-i + (a + b)) = -(-(-(-i + b)) + a) by omega)).hom :=
  nativeShiftAdd'_hom_app_f K a b (a + b) rfl i

/-- Let C be a preadditive category, K an integer chain complex, and a,b,i ∈ ℤ. The inverse
comparison S_b(S_a K) → S_{a+b}K has degree-i component the canonical equality map
K_{−(−(−(−i+b))+a)} → K_{−(−i+(a+b))}. -/
lemma nativeShiftAdd_inv_app_f (K : ChainComplex C ℤ) (a b i : ℤ) :
    ((nativeShiftAdd C a b).inv.app K).f i =
      (K.XIsoOfEq (show -(-(-(-i + b)) + a) = -(-i + (a + b)) by omega)).hom :=
  nativeShiftAdd'_inv_app_f K a b (a + b) rfl i

variable (C)

/-- Let C be a preadditive category, and a ∈ ℤ. The comparison α_{0,a} : S_a ≅ S_a ∘ S₀ agrees with
the inverse left unitor followed by the inverse zero-shift isomorphism whiskered on the right by
S_a. Thus inserting a zero shift before S_a gives the canonical unit comparison. -/
lemma nativeShiftAdd'_zero_add (a : ℤ) :
    nativeShiftAdd' C 0 a a (zero_add a) =
      (Functor.leftUnitor (nativeShift C a)).symm ≪≫
        isoWhiskerRight (nativeShiftZero C).symm (nativeShift C a) := by
  ext K i
  change ((nativeShiftAdd' C 0 a a (zero_add a)).hom.app K).f i =
    (HomologicalComplex.id ((nativeShift C a).obj K)).f i ≫
      ((nativeShift C a).map ((nativeShiftZero C).inv.app K)).f i
  dsimp only [HomologicalComplex.id]
  rw [Category.id_comp, nativeShiftAdd'_hom_app_f,
    nativeShift_map_f, nativeShiftZero_inv_app_f]

/-- Let C be a preadditive category, and a ∈ ℤ. The comparison α_{a,0} : S_a ≅ S₀ ∘ S_a agrees with
the inverse right unitor followed by the inverse zero-shift isomorphism whiskered on the left by
S_a. Thus inserting a zero shift after S_a gives the canonical unit comparison. -/
lemma nativeShiftAdd'_add_zero (a : ℤ) :
    nativeShiftAdd' C a 0 a (add_zero a) =
      (Functor.rightUnitor (nativeShift C a)).symm ≪≫
        isoWhiskerLeft (nativeShift C a) (nativeShiftZero C).symm := by
  ext K i
  change ((nativeShiftAdd' C a 0 a (add_zero a)).hom.app K).f i =
    (HomologicalComplex.id ((nativeShift C a).obj K)).f i ≫ ((nativeShiftZero C).inv.app ((nativeShift C a).obj K)).f i
  dsimp only [HomologicalComplex.id]
  rw [Category.id_comp, nativeShiftAdd'_hom_app_f,
    nativeShiftZero_inv_app_f]
  rfl

/-- Let C be a preadditive category, and a,b,c ∈ ℤ. The two natural isomorphisms S_{a+b+c} ≅ S_c ∘
S_b ∘ S_a agree: first apply α_{a+b,c} and then α_{a,b}, or first apply α_{a,b+c} and then
α_{b,c}, using the functor associator to identify the parenthesizations. -/
lemma nativeShiftAdd_assoc (a b c : ℤ) :
    nativeShiftAdd C (a + b) c ≪≫
        isoWhiskerRight (nativeShiftAdd C a b) (nativeShift C c) ≪≫
          Functor.associator (nativeShift C a) (nativeShift C b) (nativeShift C c) =
      nativeShiftAdd' C a (b + c) ((a + b) + c) (add_assoc a b c).symm ≪≫
        isoWhiskerLeft (nativeShift C a) (nativeShiftAdd C b c) := by
  ext K i
  change ((nativeShiftAdd C (a + b) c).hom.app K).f i ≫
      ((nativeShift C c).map ((nativeShiftAdd C a b).hom.app K)).f i ≫
        (HomologicalComplex.id (((nativeShift C a ⋙ nativeShift C b) ⋙ nativeShift C c).obj K)).f i =
    ((nativeShiftAdd' C a (b + c) ((a + b) + c) (add_assoc a b c).symm).hom.app K).f i ≫
      ((nativeShiftAdd C b c).hom.app ((nativeShift C a).obj K)).f i
  dsimp only [HomologicalComplex.id]
  have hid := congrArg
    (fun f => ((nativeShiftAdd C (a + b) c).hom.app K).f i ≫ f)
    (Category.comp_id (((nativeShift C c).map ((nativeShiftAdd C a b).hom.app K)).f i))
  refine hid.trans ?_
  rw [nativeShiftAdd_hom_app_f,
    nativeShift_map_f, nativeShiftAdd_hom_app_f, nativeShiftAdd'_hom_app_f,
    nativeShiftAdd_hom_app_f]
  simp only [XIsoOfEq, eqToIso]
  exact (eqToHom_trans _ _).trans (eqToHom_trans _ _).symm

end ChainComplex
