/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.Algebra.Homology.HomologicalComplex.Splitting
public import MathlibExt.Algebra.Homology.ChainComplex.NativeShift

/-!
# Signed shifts of generalized-inverse splittings

For integer cochains, shift by a places K^{i+a} in degree i and gives
both the differential and inverse component the factor (−1)^a.
For integer chains the corresponding term is K_{i−a}, with the same sign.

Reflexive and square-zero normalization commute with these shifts.
Canonical zero/addition isomorphisms, complex isomorphisms and additive
functors give the associated coherence laws.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits HomologicalComplex

namespace HomologicalComplex.Splitting

universe u v w

section EqualityComponents

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C]
  {ι : Type w} {c : ComplexShape ι} {K : HomologicalComplex C c}

private lemma hom_congr (s : Splitting K) {i i' j j' : ι}
    (hi : i = i') (hj : j = j') :
    s.hom i j = (K.XIsoOfEq hi).hom ≫ s.hom i' j' ≫ (K.XIsoOfEq hj).inv := by
  subst i' j'
  simp only [XIsoOfEq_rfl, Iso.refl_hom, Iso.refl_inv,
    Category.id_comp, Category.comp_id]

end EqualityComponents

section Cochain

variable {C : Type u} [Category.{v} C] [Preadditive C]
  {K L : CochainComplex C ℤ}

/--
Let K be an integer cochain complex in a preadditive category C, s a splitting and a∈ℤ. The
shift convention is (K⟦a⟧)ⁱ=Kⁱ⁺ᵃ with differential sign (−1)ᵃ. The shifted splitting has
h'ᵢⱼ=(−1)ᵃ•s.hom(i+a)(j+a), using the same sign as the shifted differential so d' h' d'=d'.
-/
noncomputable def cochainShift (s : Splitting K) (a : ℤ) : Splitting (K⟦a⟧) where
  hom i j := a.negOnePow • s.hom (i + a) (j + a)
  zero i j hij := by
    rw [s.zero _ _ (by
      change ¬ j + 1 = i at hij
      change ¬ (j + a) + 1 = i + a
      omega), smul_zero]
  d_h_d i j := by
    change (a.negOnePow • K.d (i + a) (j + a)) ≫
        (a.negOnePow • s.hom (j + a) (i + a)) ≫
          (a.negOnePow • K.d (i + a) (j + a)) =
      a.negOnePow • K.d (i + a) (j + a)
    simpa only [Linear.units_smul_comp, Linear.comp_units_smul,
      smul_smul, Int.units_mul_self, one_smul, mul_one, one_mul] using
      congrArg (fun f : K.X (i + a) ⟶ K.X (j + a) => a.negOnePow • f)
        (s.d_h_d (i + a) (j + a))

/--
Let K be an integer cochain complex in a preadditive category C, s a splitting and a∈ℤ. The
shift convention is (K⟦a⟧)ⁱ=Kⁱ⁺ᵃ with differential sign (−1)ᵃ. The component from (K⟦a⟧)ⁱ to
(K⟦a⟧)ʲ is exactly (−1)ᵃ•s.hom(i+a)(j+a), for all integers i,j and shifts a.
-/
@[simp]
lemma cochainShift_hom (s : Splitting K) (a i j : ℤ) :
    (s.cochainShift a).hom i j = a.negOnePow • s.hom (i + a) (j + a) := rfl

/--
Let K be an integer cochain complex in a preadditive category C, s a splitting and a∈ℤ. The
shift convention is (K⟦a⟧)ⁱ=Kⁱ⁺ᵃ with differential sign (−1)ᵃ. Reflexive normalization
commutes with shifting: (s.cochainShift a).reflexive=s.reflexive.cochainShift a.
-/
lemma cochainShift_reflexive (s : Splitting K) (a : ℤ) :
    (s.cochainShift a).reflexive = s.reflexive.cochainShift a := by
  ext i j
  simp only [reflexive_hom, cochainShift_hom,
    CochainComplex.shiftFunctor_obj_d', Linear.units_smul_comp,
    Linear.comp_units_smul, smul_smul, Int.units_mul_self,
    one_smul, mul_one, one_mul]

/--
Let K be an integer cochain complex in a preadditive category C, s a splitting and a∈ℤ. The
shift convention is (K⟦a⟧)ⁱ=Kⁱ⁺ᵃ with differential sign (−1)ᵃ. Square-zero normalization
commutes with shifting: (s.cochainShift a).normalize=s.normalize.cochainShift a.
-/
lemma cochainShift_normalize (s : Splitting K) (a : ℤ) :
    (s.cochainShift a).normalize = s.normalize.cochainShift a := by
  have hnext (p : ℤ) : (ComplexShape.up ℤ).next p = p + 1 :=
    (ComplexShape.up ℤ).next_eq' (by rfl)
  have htranslate (p : ℤ) :
      (ComplexShape.up ℤ).next p + a = (ComplexShape.up ℤ).next (p + a) := by
    rw [hnext, hnext]
    omega
  ext i j
  simp only [normalize_hom, cochainShift_reflexive, cochainShift_hom,
    CochainComplex.shiftFunctor_obj_d', htranslate,
    Linear.units_smul_comp, Linear.comp_units_smul, smul_smul,
    Int.units_mul_self, one_smul, mul_one, one_mul]
  simp only [CochainComplex.shiftFunctor_obj_X', hnext, add_assoc, add_left_comm, add_comm]
  rw [htranslate i]

/--
Let K be an integer cochain complex in a preadditive category C, s a splitting and a∈ℤ. The
shift convention is (K⟦a⟧)ⁱ=Kⁱ⁺ᵃ with differential sign (−1)ᵃ. For an isomorphism e:K≅L,
shifting the transported splitting agrees with transporting the shifted splitting along e⟦a⟧.
-/
lemma cochainShift_ofIso (s : Splitting K) (e : K ≅ L) (a : ℤ) :
    (s.ofIso e).cochainShift a =
      (s.cochainShift a).ofIso
        ((CategoryTheory.shiftFunctor (CochainComplex C ℤ) a).mapIso e) := by
  ext i j
  simp only [ofIso_hom, cochainShift_hom, Functor.mapIso_hom, Functor.mapIso_inv, Iso.app_hom,
    Iso.app_inv,
    CochainComplex.shiftFunctor_map_f', Linear.units_smul_comp,
    Linear.comp_units_smul]

/--
Let K be an integer cochain complex in a preadditive category C, s a splitting and a∈ℤ. The
shift convention is (K⟦a⟧)ⁱ=Kⁱ⁺ᵃ with differential sign (−1)ᵃ. At a=0, transport along the
canonical isomorphism K⟦0⟧≅K restores the original splitting s.
-/
@[simp]
lemma cochainShift_zero (s : Splitting K) :
    (s.cochainShift 0).ofIso
      ((CategoryTheory.shiftFunctorZero (CochainComplex C ℤ) ℤ).app K) = s := by
  ext i j
  simp only [ofIso_hom, cochainShift_hom, Iso.app_hom, Iso.app_inv,
    Int.negOnePow_zero, one_smul, CochainComplex.shiftFunctorZero_hom_app_f,
    CochainComplex.shiftFunctorZero_inv_app_f]
  have hi : i = i + 0 := by omega
  have hj : j = j + 0 := by omega
  simpa only [XIsoOfEq, eqToIso] using (hom_congr s hi hj).symm

/--
Let K be an integer cochain complex in a preadditive category C, s a splitting and a∈ℤ. The
shift convention is (K⟦a⟧)ⁱ=Kⁱ⁺ᵃ with differential sign (−1)ᵃ. For b∈ℤ, transporting the
splitting shifted by a+b along K⟦a+b⟧≅(K⟦a⟧)⟦b⟧ gives (s.cochainShift a).cochainShift b.
-/
lemma cochainShift_add (s : Splitting K) (a b : ℤ) :
    (s.cochainShift (a + b)).ofIso
        ((CategoryTheory.shiftFunctorAdd (CochainComplex C ℤ) a b).app K) =
      (s.cochainShift a).cochainShift b := by
  ext i j
  simp only [ofIso_hom, cochainShift_hom,
    CochainComplex.shiftFunctorAdd_inv_app_f,
    CochainComplex.shiftFunctorAdd_hom_app_f]
  have hi : i + b + a = i + (a + b) := by omega
  have hj : j + b + a = j + (a + b) := by omega
  change (K.XIsoOfEq hi).hom ≫
        ((a + b).negOnePow • s.hom (i + (a + b)) (j + (a + b))) ≫
          (K.XIsoOfEq hj).inv =
      b.negOnePow • (a.negOnePow • s.hom (i + b + a) (j + b + a))
  have hh := congrArg (fun f : K.X (i + b + a) ⟶ K.X (j + b + a) => (a + b).negOnePow • f)
    (hom_congr s hi hj)
  simpa only [Linear.comp_units_smul, Linear.units_smul_comp, smul_smul,
    Int.negOnePow_add, mul_comm] using hh.symm

universe uD vD

variable {D : Type uD} [Category.{vD} D] [Preadditive D]

/--
Let K be an integer cochain complex in a preadditive category C, s a splitting and a∈ℤ. The
shift convention is (K⟦a⟧)ⁱ=Kⁱ⁺ᵃ with differential sign (−1)ᵃ. For an additive functor F:C⥤D
between preadditive categories, mapping the shifted splitting and transporting along
F(K⟦a⟧)≅F(K)⟦a⟧ gives (s.map F).cochainShift a.
-/
lemma cochainShift_map (s : Splitting K) (F : C ⥤ D) [F.Additive] (a : ℤ) :
    ((s.cochainShift a).map F).ofIso ((F.mapCochainComplexShiftIso a).app K) =
      (s.map F).cochainShift a := by
  ext i j
  simp [ofIso_hom, map_hom, cochainShift_hom,
    Functor.mapCochainComplexShiftIso, Functor.map_units_smul]

end Cochain

section Chain

variable {C : Type u} [Category.{v} C] [Preadditive C]
  {K L : ChainComplex C ℤ}

/--
Let K be an integer chain complex in a preadditive category C, s a splitting and a∈ℤ. Write
K⟨a⟩ for the chain shift with degree-i term K_{i−a} and differential sign (−1)ᵃ. The shifted
splitting has component (−1)ᵃ•s.hom(i−a)(j−a), represented on the chain-shift terms by their
canonical degree identifications.
-/
noncomputable def chainShift (s : Splitting K) (a : ℤ) :
    Splitting ((ChainComplex.nativeShift C a).obj K) where
  hom i j := a.negOnePow • s.hom (-(-i + a)) (-(-j + a))
  zero i j hij := by
    rw [s.zero _ _ (by
      change ¬ i + 1 = j at hij
      change ¬ -(-i + a) + 1 = -(-j + a)
      omega), smul_zero]
    rfl
  d_h_d i j := by
    change (a.negOnePow • K.d (-(-i + a)) (-(-j + a))) ≫
        (a.negOnePow • s.hom (-(-j + a)) (-(-i + a))) ≫
          (a.negOnePow • K.d (-(-i + a)) (-(-j + a))) =
      a.negOnePow • K.d (-(-i + a)) (-(-j + a))
    simpa only [Linear.units_smul_comp, Linear.comp_units_smul,
      smul_smul, Int.units_mul_self, one_smul, mul_one, one_mul] using
      congrArg (fun f : K.X (-(-i + a)) ⟶ K.X (-(-j + a)) => a.negOnePow • f)
        (s.d_h_d (-(-i + a)) (-(-j + a)))

/--
Let K be an integer chain complex in a preadditive category C, s a splitting and a∈ℤ. Write
K⟨a⟩ for the chain shift with degree-i term K_{i−a} and differential sign (−1)ᵃ. In the
chain-shift indexing, its component is (−1)ᵃ•s.hom(−(−i+a))(−(−j+a)), with −(−i+a)=i−a and
likewise for j.
-/
@[simp]
lemma chainShift_hom (s : Splitting K) (a i j : ℤ) :
    (s.chainShift a).hom i j =
      a.negOnePow • s.hom (-(-i + a)) (-(-j + a)) := rfl

/--
Let K be an integer chain complex in a preadditive category C, s a splitting and a∈ℤ. Write
K⟨a⟩ for the chain shift with degree-i term K_{i−a} and differential sign (−1)ᵃ. Let
θᵢ:(K⟨a⟩)ᵢ≅K_{i−a} and θⱼ be the canonical term isomorphisms. The inverse component is
θᵢ.hom≫((−1)ᵃ•s.hom(i−a)(j−a))≫θⱼ.inv.
-/
lemma chainShift_hom_via_termIso (s : Splitting K) (a i j : ℤ) :
    (s.chainShift a).hom i j =
      (ChainComplex.nativeShiftObjXIso K a i).hom ≫
        (a.negOnePow • s.hom (i - a) (j - a)) ≫
          (ChainComplex.nativeShiftObjXIso K a j).inv := by
  change a.negOnePow • s.hom (-(-i + a)) (-(-j + a)) =
    (K.XIsoOfEq (show -(-i + a) = i - a by omega)).hom ≫
      (a.negOnePow • s.hom (i - a) (j - a)) ≫
        (K.XIsoOfEq (show -(-j + a) = j - a by omega)).inv
  simpa only [chainShift_hom, ChainComplex.nativeShiftObjXIso,
    Linear.comp_units_smul, Linear.units_smul_comp] using
    congrArg (fun f : K.X (-(-i + a)) ⟶ K.X (-(-j + a)) => a.negOnePow • f)
      (hom_congr s (show -(-i + a) = i - a by omega)
        (show -(-j + a) = j - a by omega))

/--
Let K be an integer chain complex in a preadditive category C, s a splitting and a∈ℤ. Write
K⟨a⟩ for the chain shift with degree-i term K_{i−a} and differential sign (−1)ᵃ. Reflexive
normalization commutes with chain shifting: (s.chainShift a).reflexive=s.reflexive.chainShift
a.
-/
lemma chainShift_reflexive (s : Splitting K) (a : ℤ) :
    (s.chainShift a).reflexive = s.reflexive.chainShift a := by
  ext i j
  simp only [reflexive_hom, chainShift_hom, ChainComplex.nativeShift_obj_d]
  change (a.negOnePow • s.hom (-(-i + a)) (-(-j + a))) ≫
      (a.negOnePow • K.d (-(-j + a)) (-(-i + a))) ≫
        (a.negOnePow • s.hom (-(-i + a)) (-(-j + a))) =
    a.negOnePow • (s.hom (-(-i + a)) (-(-j + a)) ≫
      K.d (-(-j + a)) (-(-i + a)) ≫ s.hom (-(-i + a)) (-(-j + a)))
  simp only [Linear.units_smul_comp, Linear.comp_units_smul, smul_smul,
    Int.units_mul_self, one_smul, mul_one, one_mul]

/--
Let K be an integer chain complex in a preadditive category C, s a splitting and a∈ℤ. Write
K⟨a⟩ for the chain shift with degree-i term K_{i−a} and differential sign (−1)ᵃ. The
square-zero normalization commutes with chain shifting: (s.chainShift
a).normalize=s.normalize.chainShift a.
-/
lemma chainShift_normalize (s : Splitting K) (a : ℤ) :
    (s.chainShift a).normalize = s.normalize.chainShift a := by
  have hnext (p : ℤ) : (ComplexShape.down ℤ).next p = p - 1 :=
    (ComplexShape.down ℤ).next_eq' (by change (p - 1) + 1 = p; omega)
  have htranslate (p : ℤ) :
      -(-((ComplexShape.down ℤ).next p) + a) =
        (ComplexShape.down ℤ).next (-(-p + a)) := by
    rw [hnext, hnext]
    omega
  ext i j
  simp only [normalize_hom, chainShift_reflexive, chainShift_hom,
    ChainComplex.nativeShift_obj_X, ChainComplex.nativeShift_obj_d, htranslate,
    Linear.units_smul_comp,
    Linear.comp_units_smul, smul_smul, Int.units_mul_self,
    one_smul, mul_one, one_mul]
  rw [htranslate i]
  rfl

/--
Let K be an integer chain complex in a preadditive category C, s a splitting and a∈ℤ. Write
K⟨a⟩ for the chain shift with degree-i term K_{i−a} and differential sign (−1)ᵃ. For e:K≅L,
shifting s.ofIso e agrees with transporting s.chainShift a along the shifted complex
isomorphism K⟨a⟩≅L⟨a⟩.
-/
lemma chainShift_ofIso (s : Splitting K) (e : K ≅ L) (a : ℤ) :
    (s.ofIso e).chainShift a =
      (s.chainShift a).ofIso ((ChainComplex.nativeShift C a).mapIso e) := by
  ext i j
  simp only [ofIso_hom, chainShift_hom, Functor.mapIso_hom, Functor.mapIso_inv,
    ChainComplex.nativeShift_map_f]
  change a.negOnePow • (e.inv.f (-(-i + a)) ≫ s.hom (-(-i + a)) (-(-j + a)) ≫
      e.hom.f (-(-j + a))) =
    e.inv.f (-(-i + a)) ≫ (a.negOnePow • s.hom (-(-i + a)) (-(-j + a))) ≫ e.hom.f (-(-j + a))
  simp only [Linear.units_smul_comp, Linear.comp_units_smul]

/--
Let K be an integer chain complex in a preadditive category C, s a splitting and a∈ℤ. Write
K⟨a⟩ for the chain shift with degree-i term K_{i−a} and differential sign (−1)ᵃ. At a=0,
transport along the canonical chain-shift isomorphism K⟨0⟩≅K restores s.
-/
@[simp]
lemma chainShift_zero (s : Splitting K) :
    (s.chainShift 0).ofIso ((ChainComplex.nativeShiftZero C).app K) = s := by
  ext i j
  simp only [ofIso_hom, chainShift_hom, Iso.app_hom, Iso.app_inv,
    Int.negOnePow_zero, one_smul, ChainComplex.nativeShiftZero_hom_app_f,
    ChainComplex.nativeShiftZero_inv_app_f]
  have hi : i = -(-i + 0) := by omega
  have hj : j = -(-j + 0) := by omega
  change (K.XIsoOfEq hi).hom ≫ s.hom (-(-i + 0)) (-(-j + 0)) ≫ (K.XIsoOfEq hj).inv = s.hom i j
  exact (hom_congr s hi hj).symm

/--
Let K be an integer chain complex in a preadditive category C, s a splitting and a∈ℤ. Write
K⟨a⟩ for the chain shift with degree-i term K_{i−a} and differential sign (−1)ᵃ. For b∈ℤ,
transport along K⟨a+b⟩≅(K⟨a⟩)⟨b⟩ identifies s.chainShift(a+b) with (s.chainShift a).chainShift
b.
-/
lemma chainShift_add (s : Splitting K) (a b : ℤ) :
    (s.chainShift (a + b)).ofIso ((ChainComplex.nativeShiftAdd C a b).app K) =
      (s.chainShift a).chainShift b := by
  ext i j
  simp only [ofIso_hom, chainShift_hom, Iso.app_hom, Iso.app_inv,
    ChainComplex.nativeShiftAdd_inv_app_f,
    ChainComplex.nativeShiftAdd_hom_app_f]
  have hi : -(-(-(-i + b)) + a) = -(-i + (a + b)) := by omega
  have hj : -(-(-(-j + b)) + a) = -(-j + (a + b)) := by omega
  change (K.XIsoOfEq hi).hom ≫
        ((a + b).negOnePow • s.hom (-(-i + (a + b))) (-(-j + (a + b)))) ≫
          (K.XIsoOfEq hj).inv =
      b.negOnePow • (a.negOnePow •
        s.hom (-(-(-(-i + b)) + a)) (-(-(-(-j + b)) + a)))
  have hh := congrArg
    (fun f : K.X (-(-(-(-i + b)) + a)) ⟶ K.X (-(-(-(-j + b)) + a)) => (a + b).negOnePow • f)
    (hom_congr s hi hj)
  simpa only [Linear.comp_units_smul, Linear.units_smul_comp, smul_smul,
    Int.negOnePow_add, mul_comm] using hh.symm

end Chain

end HomologicalComplex.Splitting

namespace HomologicalComplex

universe u v

variable {C : Type u} [Category.{v} C] [Preadditive C]

/--
For an integer cochain complex K in a preadditive category C and any a∈ℤ, K is split if and
only if its signed shift K⟦a⟧ is split.
-/
lemma isSplit_cochainShift_iff (K : CochainComplex C ℤ) (a : ℤ) :
    IsSplit K ↔ IsSplit (K⟦a⟧) := by
  constructor
  · rintro ⟨s⟩
    exact ⟨s.cochainShift a⟩
  · rintro ⟨s⟩
    let e : (K⟦a⟧)⟦-a⟧ ≅ K :=
      ((CategoryTheory.shiftFunctorAdd' (CochainComplex C ℤ) a (-a) 0
        (add_neg_cancel a)).app K).symm ≪≫
          (CategoryTheory.shiftFunctorZero (CochainComplex C ℤ) ℤ).app K
    exact ⟨(s.cochainShift (-a)).ofIso e⟩

/--
For an integer chain complex K in a preadditive category C and any a∈ℤ, K is split if and only
if the signed chain shift with terms K_{i−a} is split.
-/
lemma isSplit_chainShift_iff (K : ChainComplex C ℤ) (a : ℤ) :
    IsSplit K ↔ IsSplit ((ChainComplex.nativeShift C a).obj K) := by
  constructor
  · rintro ⟨s⟩
    exact ⟨s.chainShift a⟩
  · rintro ⟨s⟩
    let e : (ChainComplex.nativeShift C (-a)).obj
        ((ChainComplex.nativeShift C a).obj K) ≅ K :=
      ((ChainComplex.nativeShiftAdd' C a (-a) 0 (add_neg_cancel a)).app K).symm ≪≫
        (ChainComplex.nativeShiftZero C).app K
    exact ⟨(s.chainShift (-a)).ofIso e⟩

end HomologicalComplex
