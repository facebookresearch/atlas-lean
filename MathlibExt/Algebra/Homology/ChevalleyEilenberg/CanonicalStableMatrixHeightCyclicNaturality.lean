/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Algebra.Homology.ChevalleyEilenberg.CanonicalStableMatrixConnesWorkingHeight
public import MathlibExt.Algebra.Homology.ChevalleyEilenberg.CanonicalStableMatrixHeightCyclic
public import MathlibExt.Algebra.Homology.ChainComplex.PositiveTailHomologyMapFunctor

/-!
# The stable Lie trace factorization and its lifted naturality

Let k be a commutative ring and A an associative unital k-algebra.
For C = C_*(Mat_∞(A)), the CE differential d₁ : C₁ → C₀ is zero.
Consequently the positive-tail shift gives
s_n : H_n(positiveTail(C)) ≅ H_(n+1)(C).
The same statement holds after termwise lifting to H = max(u,v,z).

If k is a ℚ-algebra, the signed positive-tail trace W into Cλ(A)
defines Γ_n = H_n(W) ∘ s_n⁻¹ from stable matrix Lie homology
in degree n+1 to H_n(Cλ(A)). The stable cyclic map Θ_n satisfies
Ξ_n ∘ Θ_n = Γ_n, where Ξ_n : HC_n(A) ≅ H_n(Cλ(A)) is the rational
Connes comparison.

At a chosen height, Θ_n^H has target U(HC_n(A)) and Γ_n^H has
target H_n(Cλ^H(A)); they satisfy the corresponding factorization
through Ξ_n^H. Both maps are natural for unital algebra maps A → B
across independent worlds, at H = max(u,v,w,z).
Their normalization 1/(n+1) and degree sign (−1)^n are preserved.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits

universe u v w z

namespace ChevalleyEilenberg

attribute [local instance 100] LieRing.ofAssociativeRing

variable (k : Type u) [CommRing k] (A : Type v) [Ring A] [Algebra k A]

/-- For a commutative ring k and an associative unital
k-algebra A, the CE differential
C₁(Mat_∞(A)) → C₀(Mat_∞(A)) is zero.
There is no bracket pair in a degree-one wedge. -/
theorem canonicalStableMatrixCEComplex_d_one_zero :
    (canonicalStableMatrixCEComplex k A).d 1 0 = 0 := by
  let e := canonicalStableMatrixCEIso k A
  let : IsIso (e.hom.f 1) :=
    ((HomologicalComplex.eval (ModuleCat.{max u v} k) (ComplexShape.down ℕ) 1).mapIso e).isIso_hom
  apply (cancel_epi (e.hom.f 1)).1
  rw [Limits.comp_zero]
  exact (e.hom.comm 1 0).trans
    ((congrArg (fun f => f ≫ e.hom.f 0) (stableMatrixCEComplex_d_one_zero k A)).trans
      Limits.zero_comp)

/-- For a commutative ring k, an associative unital k-algebra A
and n ≥ 0, the zero degree-one CE differential gives
H_n(positiveTail(C_*(Mat_∞(A)))) ≅ H_(n+1)(C_*(Mat_∞(A))).
The positive tail has term C_(n+1) in degree n. -/
def canonicalStableMatrixPositiveTailHomologyIso (n : ℕ) :
    (ChainComplex.positiveTail (canonicalStableMatrixCEComplex k A)).homology n ≅
      (canonicalStableMatrixCEComplex k A).homology (n + 1) :=
  ChainComplex.positiveTailHomologyIso (canonicalStableMatrixCEComplex k A)
    (canonicalStableMatrixCEComplex_d_one_zero k A) n

/-- For a commutative ring k, an associative unital k-algebra A
and H = max(u,v,z), the termwise-lifted stable CE complex has
d₁ : C₁^H → C₀^H equal to zero.
The ring, algebra and additional-height worlds are independent. -/
theorem canonicalStableMatrixCEComplexAtHeight_d_one_zero :
    (canonicalStableMatrixCEComplexAtHeight.{u,v,z} k A).d 1 0 = 0 :=
  ChainComplex.mapHomologicalComplex_d_one_zero
    (ModuleCat.uliftFunctor.{max u v z, max u v} k) (canonicalStableMatrixCEComplex k A)
      (canonicalStableMatrixCEComplex_d_one_zero k A)

/-- For a commutative ring k, an associative unital k-algebra A,
H = max(u,v,z) and n ≥ 0, there is an isomorphism
H_n(positiveTail(C_*^H(Mat_∞(A)))) ≅ H_(n+1)(C_*^H(Mat_∞(A))).
It uses the zero degree-one differential of the lifted CE complex. -/
def canonicalStableMatrixPositiveTailHomologyIsoAtHeight (n : ℕ) :
    (ChainComplex.positiveTail (canonicalStableMatrixCEComplexAtHeight.{u,v,z} k A)).homology n ≅
      (canonicalStableMatrixCEComplexAtHeight.{u,v,z} k A).homology (n + 1) :=
  ChainComplex.positiveTailHomologyIso (canonicalStableMatrixCEComplexAtHeight.{u,v,z} k A)
    (canonicalStableMatrixCEComplexAtHeight_d_one_zero.{u,v,z} k A) n

variable [Algebra ℚ k]

/-- For a commutative ℚ-algebra k, an associative unital
k-algebra A and n ≥ 0, the map
Γ_n : H_(n+1)(C_*(Mat_∞(A))) → H_n(Cλ(A))
is H_n(W) ∘ s_n⁻¹, where W is the signed positive-tail trace
and s_n is the positive-tail homology shift. -/
def canonicalStableMatrixCyclicConnesHomologyMap (n : ℕ) :
    (canonicalStableMatrixCEComplex k A).homology (n + 1) ⟶
      ModuleCat.Algebra.Hochschild.NonUnital.connesHomology k A n :=
  (canonicalStableMatrixPositiveTailHomologyIso k A n).inv ≫
    HomologicalComplex.homologyMap (canonicalStableMatrixCyclicWeibelChainMap k A) n

/-- For a commutative ℚ-algebra k, an associative unital
k-algebra A and H = max(u,v,z), the map
Γ_n^H : H_(n+1)(C_*^H(Mat_∞(A))) → H_n(Cλ^H(A))
is the homology map of W^H composed after the inverse
positive-tail homology shift, for every n ≥ 0. -/
def canonicalStableMatrixCyclicConnesHomologyMapAtHeight (n : ℕ) :
    (canonicalStableMatrixCEComplexAtHeight.{u,v,z} k A).homology (n + 1) ⟶
      ModuleCat.Algebra.Hochschild.NonUnital.connesHomologyAtHeight.{u,v,z} k A n :=
  (canonicalStableMatrixPositiveTailHomologyIsoAtHeight.{u,v,z} k A n).inv ≫
    HomologicalComplex.homologyMap (canonicalStableMatrixCyclicWeibelChainMapAtHeight.{u,v,z} k A) n

/-- For a commutative ℚ-algebra k, an associative unital
k-algebra A and n ≥ 0, the stable cyclic map Θ_n satisfies
Ξ_n ∘ Θ_n = Γ_n.
Here Ξ_n : HC_n(A) ≅ H_n(Cλ(A)) is the rational cyclic-to-Connes
comparison, and Γ_n is the shifted homology map of the signed trace. -/
theorem canonicalStableMatrixCyclicHomologyMap_comp_connes (n : ℕ) :
    canonicalStableMatrixCyclicHomologyMap k A n ≫
        ModuleCat.Algebra.Hochschild.NonUnital.cyclicToConnesHomology k A n =
      canonicalStableMatrixCyclicConnesHomologyMap k A n := by
  let e := canonicalStableMatrixCEIso k A
  let s := stableMatrixPositiveTailHomologyIso k A n
  let c := canonicalStableMatrixPositiveTailHomologyIso k A n
  let t := HomologicalComplex.homologyMap e.inv (n + 1)
  let ht := HomologicalComplex.homologyMap (ChainComplex.positiveTailMap e.inv) n
  let hs := HomologicalComplex.homologyMap (stableMatrixCyclicWeibelChainMap k A) n
  have h : ht ≫ s.hom = c.hom ≫ t :=
    ChainComplex.positiveTailHomologyIso_naturality e.inv
      (canonicalStableMatrixCEComplex_d_one_zero k A) (stableMatrixCEComplex_d_one_zero k A) n
  have hInv : t ≫ s.inv = c.inv ≫ ht := by
    apply (cancel_mono s.hom).1
    rw [Category.assoc, Iso.inv_hom_id, Category.comp_id, Category.assoc, h,
      ← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  have hChain : HomologicalComplex.homologyMap (canonicalStableMatrixCyclicWeibelChainMap k A) n =
      ht ≫ hs := HomologicalComplex.homologyMap_comp _ _ n
  have hOriginal := stableMatrixCyclicHomologyMap_comp_connes k A n
  change (t ≫ stableMatrixCyclicHomologyMap k A n) ≫
    ModuleCat.Algebra.Hochschild.NonUnital.cyclicToConnesHomology k A n =
      c.inv ≫ HomologicalComplex.homologyMap (canonicalStableMatrixCyclicWeibelChainMap k A) n
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun f => t ≫ f) hOriginal).trans
      ((Category.assoc t s.inv hs).symm.trans
        ((congrArg (fun f => f ≫ hs) hInv).trans
          ((Category.assoc c.inv ht hs).trans (congrArg (fun f => c.inv ≫ f) hChain.symm)))))

/-- For a commutative ℚ-algebra k, an associative unital
k-algebra A and H = max(u,v,z), let U lift k-modules to H.
Let χ_C identify H_(n+1)(U(C)) with U(H_(n+1)(C)), and let χ_Q
identify H_n(U(Cλ(A))) with U(H_n(Cλ(A))).
If e_Q : U(Cλ(A)) ≅ Cλ^H(A) is the complex cokernel comparison,
then Γ_n^H = H_n(e_Q) ∘ χ_Q⁻¹ ∘ U(Γ_n) ∘ χ_C.
This gives the precise map from lifted stable Lie homology to
the homology of the lifted Connes quotient. -/
theorem canonicalStableMatrixCyclicConnesHomologyMapAtHeight_eq_lift (n : ℕ) :
    canonicalStableMatrixCyclicConnesHomologyMapAtHeight.{u,v,z} k A n =
      (((ModuleCat.uliftFunctor.{max u v z, max u v} k).mapHomologicalComplexHomologyIso
        (ComplexShape.down ℕ) (n + 1)).app (canonicalStableMatrixCEComplex k A)).hom ≫
        (ModuleCat.uliftFunctor.{max u v z, max u v} k).map
          (canonicalStableMatrixCyclicConnesHomologyMap k A n) ≫
          (((ModuleCat.uliftFunctor.{max u v z, max u v} k).mapHomologicalComplexHomologyIso
            (ComplexShape.down ℕ) n).app
              (ModuleCat.Algebra.Hochschild.NonUnital.connesComplex k A)).inv ≫
            HomologicalComplex.homologyMap
              (ModuleCat.Algebra.Hochschild.NonUnital.connesComplexLiftIsoAtHeight.{u,v,z} k A).hom n := by
  let U := ModuleCat.uliftFunctor.{max u v z, max u v} k
  let F := U.mapHomologicalComplex (ComplexShape.down ℕ)
  let K : ChainComplex (ModuleCat.{max u v} k) ℕ := canonicalStableMatrixCEComplex k A
  let Q : ChainComplex (ModuleCat.{max u v} k) ℕ := ModuleCat.Algebra.Hochschild.NonUnital.connesComplex k A
  let T : ChainComplex (ModuleCat.{max u v} k) ℕ := ChainComplex.positiveTail K
  let KU : ChainComplex (ModuleCat.{max u v z} k) ℕ := F.obj K
  let TU : ChainComplex (ModuleCat.{max u v z} k) ℕ := ChainComplex.positiveTail KU
  let FT : ChainComplex (ModuleCat.{max u v z} k) ℕ := F.obj T
  let FQ : ChainComplex (ModuleCat.{max u v z} k) ℕ := F.obj Q
  let QH : ChainComplex (ModuleCat.{max u v z} k) ℕ :=
    ModuleCat.Algebra.Hochschild.NonUnital.connesComplexAtHeight.{u,v,z} k A
  let w : T ⟶ Q := canonicalStableMatrixCyclicWeibelChainMap k A
  let e : TU ≅ FT := (ChainComplex.positiveTailMapFunctorIso U).app K
  let qN : FQ ⟶ QH := (ModuleCat.Algebra.Hochschild.NonUnital.connesComplexLiftIsoAtHeight.{u,v,z} k A).hom
  let s : U.obj (T.homology n) ≅ U.obj (K.homology (n + 1)) :=
    U.mapIso (canonicalStableMatrixPositiveTailHomologyIso k A n)
  let sH : TU.homology n ≅ KU.homology (n + 1) :=
    canonicalStableMatrixPositiveTailHomologyIsoAtHeight.{u,v,z} k A n
  let χK : KU.homology (n + 1) ≅ U.obj (K.homology (n + 1)) :=
    (U.mapHomologicalComplexHomologyIso (ComplexShape.down ℕ) (n + 1)).app K
  let χT : FT.homology n ≅ U.obj (T.homology n) :=
    (U.mapHomologicalComplexHomologyIso (ComplexShape.down ℕ) n).app T
  let χQ : FQ.homology n ≅ U.obj (Q.homology n) :=
    (U.mapHomologicalComplexHomologyIso (ComplexShape.down ℕ) n).app Q
  let he : TU.homology n ⟶ FT.homology n := HomologicalComplex.homologyMap e.hom n
  let hw : FT.homology n ⟶ FQ.homology n := HomologicalComplex.homologyMap (F.map w) n
  let hq : FQ.homology n ⟶ QH.homology n := HomologicalComplex.homologyMap qN n
  have hShift : he ≫ χT.hom ≫ s.hom = sH.hom ≫ χK.hom :=
    ChainComplex.positiveTailHomologyIso_map U K (canonicalStableMatrixCEComplex_d_one_zero k A) n
  have hShiftInv : sH.inv ≫ he ≫ χT.hom = χK.hom ≫ s.inv := by
    apply (Iso.eq_comp_inv s).2
    exact (Category.assoc sH.inv (he ≫ χT.hom) s.hom).trans
      ((congrArg (fun f => sH.inv ≫ f) ((Category.assoc he χT.hom s.hom).trans hShift)).trans
        ((Category.assoc sH.inv sH.hom χK.hom).symm.trans
          ((congrArg (fun f => f ≫ χK.hom) sH.inv_hom_id).trans (Category.id_comp χK.hom))))
  have hW : χT.hom ≫ U.map (HomologicalComplex.homologyMap w n) ≫ χQ.inv = hw := by
    have hNat := U.mapHomologicalComplexHomologyIso_hom_naturality (ComplexShape.down ℕ) n w
    exact (congrArg (fun f => f ≫ χQ.inv) hNat.symm).trans
      ((Category.assoc hw χQ.hom χQ.inv).trans
        ((congrArg (fun f => hw ≫ f) χQ.hom_inv_id).trans (Category.comp_id hw)))
  let H : ChainComplex (ModuleCat.{max u v z} k) ℕ ⥤ ModuleCat.{max u v z} k :=
    HomologicalComplex.homologyFunctor (ModuleCat.{max u v z} k) (ComplexShape.down ℕ) n
  have hChain : HomologicalComplex.homologyMap
      (canonicalStableMatrixCyclicWeibelChainMapAtHeight.{u,v,z} k A) n = he ≫ hw ≫ hq := by
    change H.map (e.hom ≫ F.map w ≫ qN) = he ≫ hw ≫ hq
    exact (H.map_comp e.hom (F.map w ≫ qN)).trans
      (congrArg (fun f => he ≫ f) (H.map_comp (F.map w) qN))
  have hExpand : sH.inv ≫ he ≫ hw ≫ hq =
      (sH.inv ≫ he ≫ χT.hom) ≫ U.map (HomologicalComplex.homologyMap w n) ≫ χQ.inv ≫ hq := by
    exact (congrArg (fun f : FT.homology n ⟶ FQ.homology n => sH.inv ≫ he ≫ f ≫ hq) hW.symm).trans
      (by simp only [Category.assoc])
  have hMap : U.map (canonicalStableMatrixCyclicConnesHomologyMap k A n) =
      s.inv ≫ U.map (HomologicalComplex.homologyMap w n) :=
    U.map_comp (canonicalStableMatrixPositiveTailHomologyIso k A n).inv (HomologicalComplex.homologyMap w n)
  change sH.inv ≫ HomologicalComplex.homologyMap
      (canonicalStableMatrixCyclicWeibelChainMapAtHeight.{u,v,z} k A) n =
    χK.hom ≫ U.map (canonicalStableMatrixCyclicConnesHomologyMap k A n) ≫ χQ.inv ≫ hq
  exact (congrArg (fun f => sH.inv ≫ f) hChain).trans
    (hExpand.trans
      ((congrArg (fun f => f ≫ U.map (HomologicalComplex.homologyMap w n) ≫ χQ.inv ≫ hq) hShiftInv).trans
        ((show (χK.hom ≫ s.inv) ≫ U.map (HomologicalComplex.homologyMap w n) ≫ χQ.inv ≫ hq =
            χK.hom ≫ (s.inv ≫ U.map (HomologicalComplex.homologyMap w n)) ≫ χQ.inv ≫ hq by
          simp only [Category.assoc]).trans
          (congrArg (fun f => χK.hom ≫ f ≫ χQ.inv ≫ hq) hMap.symm))))

/-- For a commutative ℚ-algebra k, an associative unital
k-algebra A, H = max(u,v,z) and n ≥ 0, the lifted maps satisfy
Ξ_n^H ∘ Θ_n^H = Γ_n^H.
The comparison Ξ_n^H has source U(HC_n(A)) and target H_n(Cλ^H(A)),
while the common source of the trace maps is H_(n+1)(C_*^H(Mat_∞(A))). -/
theorem canonicalStableMatrixCyclicHomologyMapAtHeight_comp_connes (n : ℕ) :
    canonicalStableMatrixCyclicHomologyMapAtHeight.{u,v,z} k A n ≫
        (ModuleCat.Algebra.Hochschild.NonUnital.cyclicToConnesHomologyIsoAtHeight.{u,v,z} k A n).hom =
      canonicalStableMatrixCyclicConnesHomologyMapAtHeight.{u,v,z} k A n := by
  let U := ModuleCat.uliftFunctor.{max u v z, max u v} k
  let χ := (U.mapHomologicalComplexHomologyIso (ComplexShape.down ℕ) (n + 1)).app
    (canonicalStableMatrixCEComplex k A)
  let q := (((U.mapHomologicalComplexHomologyIso (ComplexShape.down ℕ) n).app
    (ModuleCat.Algebra.Hochschild.NonUnital.connesComplex k A)).inv ≫
      HomologicalComplex.homologyMap
        (ModuleCat.Algebra.Hochschild.NonUnital.connesComplexLiftIsoAtHeight.{u,v,z} k A).hom n)
  have h := U.congr_map (canonicalStableMatrixCyclicHomologyMap_comp_connes k A n)
  rw [U.map_comp] at h
  rw [canonicalStableMatrixCyclicConnesHomologyMapAtHeight_eq_lift,
    ModuleCat.Algebra.Hochschild.NonUnital.cyclicToConnesHomologyIsoAtHeight_hom]
  change (χ.hom ≫ U.map (canonicalStableMatrixCyclicHomologyMap k A n)) ≫
      (U.map (ModuleCat.Algebra.Hochschild.NonUnital.cyclicToConnesHomology k A n) ≫ q) =
    χ.hom ≫ U.map (canonicalStableMatrixCyclicConnesHomologyMap k A n) ≫ q
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun f => χ.hom ≫ f) (Category.assoc _ _ _).symm).trans
      (congrArg (fun f => χ.hom ≫ f ≫ q) h))

variable {B : Type w} [Ring B] [Algebra k B]

/-- For a commutative ℚ-algebra k, a unital k-algebra map
f : A → B and H = max(u,v,w,z), the chosen-height maps satisfy
Γ_(B,n)^H ∘ H_(n+1)(C^H(f)) =
H_n(Cλ^H(f)) ∘ Γ_(A,n)^H.
The source is stable matrix Lie homology for A in degree n+1,
and the target is H_n(Cλ^H(B)). -/
@[reassoc]
theorem canonicalStableMatrixCyclicConnesHomologyMapAtHeight_naturality (f : A →ₐ[k] B) (n : ℕ) :
    HomologicalComplex.homologyMap
        (canonicalStableMatrixCoefficientCEMapAtHeight.{u,v,w,z} k A f) (n + 1) ≫
      canonicalStableMatrixCyclicConnesHomologyMapAtHeight.{u,w,max u v w z} k B n =
    canonicalStableMatrixCyclicConnesHomologyMapAtHeight.{u,v,max u v w z} k A n ≫
      ModuleCat.Algebra.Hochschild.NonUnital.connesHomologyMapAtHeight.{u,v,w,z} k A
        f.toNonUnitalAlgHom n := by
  let c := canonicalStableMatrixCoefficientCEMapAtHeight.{u,v,w,z} k A f
  let sA := canonicalStableMatrixPositiveTailHomologyIsoAtHeight.{u,v,max u v w z} k A n
  let sB := canonicalStableMatrixPositiveTailHomologyIsoAtHeight.{u,w,max u v w z} k B n
  let h := HomologicalComplex.homologyMap c (n + 1)
  let ht := HomologicalComplex.homologyMap (ChainComplex.positiveTailMap c) n
  let wA := HomologicalComplex.homologyMap
    (canonicalStableMatrixCyclicWeibelChainMapAtHeight.{u,v,max u v w z} k A) n
  let wB := HomologicalComplex.homologyMap
    (canonicalStableMatrixCyclicWeibelChainMapAtHeight.{u,w,max u v w z} k B) n
  let q := ModuleCat.Algebra.Hochschild.NonUnital.connesHomologyMapAtHeight.{u,v,w,z} k A
    f.toNonUnitalAlgHom n
  have hs : ht ≫ sB.hom = sA.hom ≫ h :=
    ChainComplex.positiveTailHomologyIso_naturality c
      (canonicalStableMatrixCEComplexAtHeight_d_one_zero.{u,v,max u v w z} k A)
      (canonicalStableMatrixCEComplexAtHeight_d_one_zero.{u,w,max u v w z} k B) n
  have hsInv : h ≫ sB.inv = sA.inv ≫ ht := by
    apply (cancel_mono sB.hom).1
    rw [Category.assoc, Iso.inv_hom_id, Category.comp_id, Category.assoc, hs,
      ← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  have hw : ht ≫ wB = wA ≫ q := by
    have hh := congrArg (fun f => HomologicalComplex.homologyMap f n)
      (canonicalStableMatrixCyclicWeibelChainMapAtHeight_naturality.{u,v,w,z} k A f)
    simp only [HomologicalComplex.homologyMap_comp] at hh
    exact hh
  change h ≫ (sB.inv ≫ wB) = (sA.inv ≫ wA) ≫ q
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun f => f ≫ wB) hsInv).trans
      ((Category.assoc _ _ _).trans
        ((congrArg (fun f => sA.inv ≫ f) hw).trans (Category.assoc _ _ _).symm)))

/-- For a commutative ℚ-algebra k, a unital k-algebra map
f : A → B and H = max(u,v,w,z), the lifted cyclic maps satisfy
Θ_(B,n)^H ∘ H_(n+1)(C^H(f)) = HC_n^H(f) ∘ Θ_(A,n)^H.
The target is the lifted cyclic homology U(HC_n(B)).
Both algebra carrier worlds and the extra height remain independent. -/
@[reassoc]
theorem canonicalStableMatrixCyclicHomologyMapAtHeight_naturality (f : A →ₐ[k] B) (n : ℕ) :
    HomologicalComplex.homologyMap
        (canonicalStableMatrixCoefficientCEMapAtHeight.{u,v,w,z} k A f) (n + 1) ≫
      canonicalStableMatrixCyclicHomologyMapAtHeight.{u,w,max u v w z} k B n =
    canonicalStableMatrixCyclicHomologyMapAtHeight.{u,v,max u v w z} k A n ≫
      ModuleCat.Algebra.Hochschild.NonUnital.cyclicHomologyMapAtHeight.{u,v,w,z}
        f.toNonUnitalAlgHom n := by
  let eA := ModuleCat.Algebra.Hochschild.NonUnital.cyclicToConnesHomologyIsoAtHeight.{u,v,max u v w z}
    k A n
  let eB := ModuleCat.Algebra.Hochschild.NonUnital.cyclicToConnesHomologyIsoAtHeight.{u,w,max u v w z}
    k B n
  let h := HomologicalComplex.homologyMap
    (canonicalStableMatrixCoefficientCEMapAtHeight.{u,v,w,z} k A f) (n + 1)
  let cA := canonicalStableMatrixCyclicHomologyMapAtHeight.{u,v,max u v w z} k A n
  let cB := canonicalStableMatrixCyclicHomologyMapAtHeight.{u,w,max u v w z} k B n
  let m := ModuleCat.Algebra.Hochschild.NonUnital.cyclicHomologyMapAtHeight.{u,v,w,z}
    f.toNonUnitalAlgHom n
  let q := ModuleCat.Algebra.Hochschild.NonUnital.connesHomologyMapAtHeight.{u,v,w,z} k A
    f.toNonUnitalAlgHom n
  have hA : cA ≫ eA.hom = canonicalStableMatrixCyclicConnesHomologyMapAtHeight.{u,v,max u v w z}
      k A n := canonicalStableMatrixCyclicHomologyMapAtHeight_comp_connes.{u,v,max u v w z} k A n
  have hB : cB ≫ eB.hom = canonicalStableMatrixCyclicConnesHomologyMapAtHeight.{u,w,max u v w z}
      k B n := canonicalStableMatrixCyclicHomologyMapAtHeight_comp_connes.{u,w,max u v w z} k B n
  have hM : m ≫ eB.hom = eA.hom ≫ q :=
    ModuleCat.Algebra.Hochschild.NonUnital.cyclicToConnesHomologyIsoAtHeight_hom_naturality.{u,v,w,z}
      k A f.toNonUnitalAlgHom n
  apply (cancel_mono eB.hom).1
  exact (Category.assoc h cB eB.hom).trans
    ((congrArg (fun f => h ≫ f) hB).trans
      ((canonicalStableMatrixCyclicConnesHomologyMapAtHeight_naturality.{u,v,w,z} k A f n).trans
        ((congrArg (fun f => f ≫ q) hA.symm).trans
          ((Category.assoc cA eA.hom q).trans
            ((congrArg (fun f => cA ≫ f) hM.symm).trans (Category.assoc cA m eB.hom).symm)))))

end ChevalleyEilenberg
