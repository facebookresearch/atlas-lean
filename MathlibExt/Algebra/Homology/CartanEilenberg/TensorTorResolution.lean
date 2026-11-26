/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.Algebra.Homology.CartanEilenberg.TensorConvolution
public import MathlibExt.Algebra.Homology.CartanEilenberg.RowHomologyResolution
public import MathlibExt.Algebra.Homology.ChainGradedPairingHomologyAdapter
public import Mathlib.Algebra.Homology.Additive
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.CategoryTheory.Monoidal.Tor

/-!
# Finite Tor resolutions of a tensor antidiagonal

Let R be commutative, K,L nonnegative R-module complexes and P a Cartan–Eilenberg resolution of
L. In inner degree q, the finite sum of Hᵢ(K) tensored with the vertical-homology resolution of
Hⱼ(L), over i+j=q, is a resolution-degree chain complex. Its outer homology is ⨁_{i+j=q}
Tor_p^R(Hᵢ(K),Hⱼ(L)), with the second factor resolved.

The ordinary homogeneous tensor pairing gives a canonical map to vertical homology of the
tensor-convolution bicomplex. Its summand formulas retain the actual row projective resolutions
and their degree-zero augmentations.
-/

@[expose] public section

set_option autoImplicit false
set_option warningAsError true

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory

namespace HomologicalComplex

variable {R : Type u} [CommRing R]
variable {L : ChainComplex (ModuleCat.{u} R) ℕ}

local instance : HasFiniteBiproducts (ModuleCat.{u} R) :=
  CategoryTheory.Abelian.hasFiniteBiproducts

local instance :
    HasFiniteBiproducts (ChainComplex (ModuleCat.{u} R) ℕ) :=
  CategoryTheory.Abelian.hasFiniteBiproducts

/-- For q ∈ ℕ, the Künneth antidiagonal is the finite set of pairs (i,j) of natural numbers with
i+j=q. -/
abbrev KunnethAntidiagonal (q : ℕ) :=
  Finset.antidiagonal q

/-- Let R be a commutative ring, K,L nonnegative chain complexes of R-modules, and P a
Cartan–Eilenberg resolution of L. The bicomplex has resolution index a and inner tensor degree
q. For a pair (i,j) with i+j=q, the summand resolution complex is Hᵢ(K) tensored with P's
vertical-homology projective resolution of Hⱼ(L). Its resolution homology computes
Tor_p^R(Hᵢ(K),Hⱼ(L)), with Hⱼ(L) the resolved second factor. -/
noncomputable def kunnethTorResolutionSummand
    (K : ChainComplex (ModuleCat.{u} R) ℕ)
    (P : CartanEilenbergResolution L) {q : ℕ}
    (ij : KunnethAntidiagonal q) :
    ChainComplex (ModuleCat.{u} R) ℕ :=
  (((tensoringLeft (ModuleCat.{u} R)).obj
      (K.homology ij.val.1)).mapHomologicalComplex
        (ComplexShape.down ℕ)).obj
    (P.cartanEilenbergVerticalHomologyResolution ij.val.2).complex

@[simp]
theorem kunnethTorResolutionSummand_X
    (K : ChainComplex (ModuleCat.{u} R) ℕ)
    (P : CartanEilenbergResolution L) {q : ℕ}
    (ij : KunnethAntidiagonal q) (a : ℕ) :
    (kunnethTorResolutionSummand K P ij).X a =
      K.homology ij.val.1 ⊗
        (P.bicomplex.verticalHomologyComplex ij.val.2).X a :=
  rfl

@[simp]
theorem kunnethTorResolutionSummand_d
    (K : ChainComplex (ModuleCat.{u} R) ℕ)
    (P : CartanEilenbergResolution L) {q : ℕ}
    (ij : KunnethAntidiagonal q) (a : ℕ) :
    (kunnethTorResolutionSummand K P ij).d (a + 1) a =
      𝟙 (K.homology ij.val.1) ⊗ₘ
        (P.bicomplex.verticalHomologyComplex ij.val.2).d (a + 1) a :=
  rfl

/-- Let R be a commutative ring, K,L nonnegative chain complexes of R-modules, and P a
Cartan–Eilenberg resolution of L. The bicomplex has resolution index a and inner tensor degree
q. For each inner degree q, the outer resolution complex is the finite biproduct, over i+j=q, of
Hᵢ(K) ⊗ the stored vertical-homology resolution of Hⱼ(L). -/
noncomputable def kunnethTorResolutionComplex
    (K : ChainComplex (ModuleCat.{u} R) ℕ)
    (P : CartanEilenbergResolution L) (q : ℕ) :
    ChainComplex (ModuleCat.{u} R) ℕ :=
  ⨁ fun ij : KunnethAntidiagonal q =>
    kunnethTorResolutionSummand K P ij

/-- Let R be a commutative ring, K,L nonnegative chain complexes of R-modules, and P a
Cartan–Eilenberg resolution of L. The bicomplex has resolution index a and inner tensor degree
q. The ordinary homology tensor pairing in each antidiagonal summand defines a chain map from
the finite Tor-resolution complex to the vertical-homology complex of the tensor convolution in
inner degree q. -/
noncomputable def kunnethCEVerticalHomologyPairing
    (K : ChainComplex (ModuleCat.{u} R) ℕ)
    (P : CartanEilenbergResolution L) (q : ℕ) :
    kunnethTorResolutionComplex K P q ⟶
      (kunnethCEBicomplex K P).verticalHomologyComplex q := by
  let A : KunnethAntidiagonal q → ChainComplex (ModuleCat.{u} R) ℕ :=
    fun ij => kunnethTorResolutionSummand K P ij
  let Y : ChainComplex (ModuleCat.{u} R) ℕ :=
    (kunnethCEBicomplex K P).verticalHomologyComplex q
  let component : ∀ ij, A ij ⟶ Y := fun ij =>
    ChainComplex.ofHom
      (fun a =>
        (ChainGradedPairing.pairHomology
            (𝟙 (tensorObj K (P.bicomplex.X a)))
            (ChainGradedPairing.homologyDescentData
              (𝟙 (tensorObj K (P.bicomplex.X a))))
            ij.val.1 ij.val.2) ≫
          (homologyIsoOfEq (tensorObj K (P.bicomplex.X a))
            (Finset.mem_antidiagonal.mp ij.property)).hom)
      (fun a => by
        let g := P.bicomplex.d (a + 1) a
        let P₁ : ChainGradedPairing K (P.bicomplex.X (a + 1))
            (tensorObj K (P.bicomplex.X (a + 1))) :=
          𝟙 (tensorObj K (P.bicomplex.X (a + 1)))
        let P₀ : ChainGradedPairing K (P.bicomplex.X a)
            (tensorObj K (P.bicomplex.X a)) :=
          𝟙 (tensorObj K (P.bicomplex.X a))
        have hpair : ∀ i j,
            P₁.pair i j ≫ (tensorHom (𝟙 K) g).f (i + j) =
              (𝟙 (K.X i) ⊗ₘ g.f j) ≫ P₀.pair i j := by
          intro i j
          exact (ChainGradedPairing.pair_naturality P₁ P₀
            (𝟙 K) g (tensorHom (𝟙 K) g)
            (by simp [P₁, P₀]) i j).symm
        have hnat := ChainGradedPairing.pairHomology_naturality
          P₁ (ChainGradedPairing.homologyDescentData P₁)
          P₀ (ChainGradedPairing.homologyDescentData P₀)
          (𝟙 K) g (tensorHom (𝟙 K) g) hpair ij.val.1 ij.val.2
        let hij : ij.val.1 + ij.val.2 = q :=
          Finset.mem_antidiagonal.mp ij.property
        change
          ChainGradedPairing.pairHomology P₁
                (ChainGradedPairing.homologyDescentData P₁)
                ij.val.1 ij.val.2 ≫
              (homologyIsoOfEq
                (tensorObj K (P.bicomplex.X (a + 1))) hij).hom ≫
              homologyMap (tensorHom (𝟙 K) g) q =
            (𝟙 (K.homology ij.val.1) ⊗ₘ homologyMap g ij.val.2) ≫
              ChainGradedPairing.pairHomology P₀
                (ChainGradedPairing.homologyDescentData P₀)
                ij.val.1 ij.val.2 ≫
              (homologyIsoOfEq (tensorObj K (P.bicomplex.X a)) hij).hom
        rw [← homologyIsoOfEq_hom_naturality
            (tensorHom (𝟙 K) g) hij,
          ← Category.assoc, hnat.symm]
        simp only [homologyMap_id, Category.assoc])
  unfold kunnethTorResolutionComplex
  change (⨁ A) ⟶ Y
  exact biproduct.desc component

/-- Let R be a commutative ring, K,L nonnegative chain complexes of R-modules, and P a
Cartan–Eilenberg resolution of L. The bicomplex has resolution index a and inner tensor degree
q. In resolution degree a and antidiagonal summand (i,j), the pairing map is the ordinary
homology pairing Hᵢ(K) ⊗ Hⱼ(P.bicomplex.Xₐ) → H_q(K ⊗ P.bicomplex.Xₐ), followed by the canonical
total-degree identification i+j=q. -/
@[reassoc]
theorem kunnethCEVerticalHomologyPairing_ι_f
    (K : ChainComplex (ModuleCat.{u} R) ℕ)
    (P : CartanEilenbergResolution L) (q a : ℕ)
    (ij : KunnethAntidiagonal q) :
    ((biproduct.ι
        (fun ij : KunnethAntidiagonal q =>
          kunnethTorResolutionSummand K P ij) ij).f a) ≫
        (kunnethCEVerticalHomologyPairing K P q).f a =
      (ChainGradedPairing.pairHomology
        (𝟙 (tensorObj K (P.bicomplex.X a)))
        (ChainGradedPairing.homologyDescentData
          (𝟙 (tensorObj K (P.bicomplex.X a))))
        ij.val.1 ij.val.2) ≫
        (homologyIsoOfEq
          (tensorObj K (P.bicomplex.X a))
            (Finset.mem_antidiagonal.mp ij.property)).hom := by
  unfold kunnethCEVerticalHomologyPairing
  dsimp only
  change
    (biproduct.ι
        (fun ij : KunnethAntidiagonal q =>
          kunnethTorResolutionSummand K P ij) ij ≫
      biproduct.desc _).f a = _
  rw [biproduct.ι_desc]
  rfl

/-- Let R be a commutative ring, K,L nonnegative chain complexes of R-modules, and P a
Cartan–Eilenberg resolution of L. The bicomplex has resolution index a and inner tensor degree
q. For p,q ∈ ℕ, the outer homology H_p of the finite degree-q resolution complex is canonically
isomorphic to ⨁_{i+j=q} Tor_p^R(Hᵢ(K),Hⱼ(L)). The second factor Hⱼ(L) is computed by P's actual
vertical-homology projective resolution. -/
noncomputable def kunnethTorResolutionHomologyIso
    (K : ChainComplex (ModuleCat.{u} R) ℕ)
    (P : CartanEilenbergResolution L) (p q : ℕ) :
    (kunnethTorResolutionComplex K P q).homology p ≅
      ⨁ fun ij : KunnethAntidiagonal q =>
        ((CategoryTheory.Tor (ModuleCat.{u} R) p).obj
          (K.homology ij.val.1)).obj (L.homology ij.val.2) :=
  by
    let A : KunnethAntidiagonal q →
        ChainComplex (ModuleCat.{u} R) ℕ := fun ij =>
      kunnethTorResolutionSummand K P ij
    let D := Discrete.functor A
    let F := homologyFunctor (ModuleCat.{u} R) (ComplexShape.down ℕ) p
    let HA : KunnethAntidiagonal q → ModuleCat.{u} R := fun ij =>
      (A ij).homology p
    letI : F.Additive := by infer_instance
    letI : PreservesFiniteBiproducts F := by infer_instance
    letI : PreservesColimit D F := by infer_instance
    let eComplex : kunnethTorResolutionComplex K P q ≅
        ⨁ A :=
      eqToIso (by rfl)
    let eHomologyDiagram :
        (D ⋙ F) ≅ Discrete.functor HA :=
      Discrete.natIso fun _ => Iso.refl _
    exact
      F.mapIso eComplex ≪≫
        F.mapIso (biproduct.isoCoproduct A) ≪≫
        preservesColimitIso F D ≪≫
        colim.mapIso eHomologyDiagram ≪≫
        (biproduct.isoCoproduct HA).symm ≪≫
        biproduct.mapIso (fun ij : KunnethAntidiagonal q =>
          ((P.cartanEilenbergVerticalHomologyResolution ij.val.2).isoLeftDerivedObj
            ((tensoringLeft (ModuleCat.{u} R)).obj (K.homology ij.val.1)) p).symm)

/-- Let R be a commutative ring, K,L nonnegative chain complexes of R-modules, and P a
Cartan–Eilenberg resolution of L. The bicomplex has resolution index a and inner tensor degree
q. For p,q ∈ ℕ and i+j=q, the homology map of the selected resolution-summand injection,
followed by the global Tor isomorphism, is the summand's projective-resolution-derived
comparison followed by the (i,j) Tor injection. -/
theorem kunnethTorResolutionHomologyIso_ι
    (K : ChainComplex (ModuleCat.{u} R) ℕ)
    (P : CartanEilenbergResolution L) (p q : ℕ)
    (ij : KunnethAntidiagonal q) :
    HomologicalComplex.homologyMap
        (biproduct.ι
          (fun kl : KunnethAntidiagonal q =>
            kunnethTorResolutionSummand K P kl) ij) p ≫
      (kunnethTorResolutionHomologyIso K P p q).hom =
        ((P.cartanEilenbergVerticalHomologyResolution ij.val.2).isoLeftDerivedObj
            ((tensoringLeft (ModuleCat.{u} R)).obj
              (K.homology ij.val.1)) p).inv ≫
          biproduct.ι
            (fun kl : KunnethAntidiagonal q =>
              ((CategoryTheory.Tor (ModuleCat.{u} R) p).obj
                (K.homology kl.val.1)).obj
                  (L.homology kl.val.2)) ij := by
  let A : KunnethAntidiagonal q →
      ChainComplex (ModuleCat.{u} R) ℕ := fun kl =>
    kunnethTorResolutionSummand K P kl
  let D := Discrete.functor A
  let H := homologyFunctor (ModuleCat.{u} R) (ComplexShape.down ℕ) p
  let HA : KunnethAntidiagonal q → ModuleCat.{u} R := fun kl =>
    H.obj (A kl)
  let TorFamily : KunnethAntidiagonal q → ModuleCat.{u} R := fun kl =>
    ((CategoryTheory.Tor (ModuleCat.{u} R) p).obj
      (K.homology kl.val.1)).obj (L.homology kl.val.2)
  let _ : H.Additive := by infer_instance
  let _ : PreservesFiniteBiproducts H := by infer_instance
  let _ : PreservesColimit D H := by infer_instance
  let eComplex : kunnethTorResolutionComplex K P q ≅ ⨁ A := by
    change (⨁ A) ≅ ⨁ A
    exact Iso.refl _
  let eHomologyDiagram : (D ⋙ H) ≅ Discrete.functor HA :=
    Discrete.natIso fun _ => Iso.refl _
  let eFinite :=
    H.mapIso (biproduct.isoCoproduct A) ≪≫
      preservesColimitIso H D ≪≫
      colim.mapIso eHomologyDiagram ≪≫
      (biproduct.isoCoproduct HA).symm
  let eTor : ∀ kl : KunnethAntidiagonal q, HA kl ≅ TorFamily kl := fun kl =>
    ((P.cartanEilenbergVerticalHomologyResolution kl.val.2).isoLeftDerivedObj
      ((tensoringLeft (ModuleCat.{u} R)).obj (K.homology kl.val.1)) p).symm
  have hFinite : H.map (biproduct.ι A ij) ≫ eFinite.hom =
      biproduct.ι HA ij := by
    simp only [eFinite, Iso.trans_hom, Functor.mapIso_hom]
    rw [← Functor.map_comp_assoc]
    rw [biproduct.isoCoproduct_hom]
    rw [biproduct.ι_desc]
    rw [ι_preservesColimitIso_hom_assoc]
    rw [colim_map]
    rw [ι_colimMap_assoc]
    simp
    rfl
  let eGlobal := H.mapIso eComplex ≪≫ eFinite ≪≫ biproduct.mapIso eTor
  have hGlobal : kunnethTorResolutionHomologyIso K P p q = eGlobal := rfl
  change H.map (biproduct.ι A ij) ≫
      (kunnethTorResolutionHomologyIso K P p q).hom =
    (eTor ij).hom ≫ biproduct.ι TorFamily ij
  rw [hGlobal]
  dsimp only [eGlobal, eComplex, Iso.trans_hom, Functor.mapIso_hom,
    Iso.refl_hom]
  change H.map (biproduct.ι A ij) ≫
      (H.map (𝟙 (⨁ A)) ≫ eFinite.hom ≫
        (biproduct.mapIso eTor).hom) =
    (eTor ij).hom ≫ biproduct.ι TorFamily ij
  rw [H.map_id, Category.id_comp]
  let m := (biproduct.mapIso eTor).hom
  have hMap : biproduct.ι HA ij ≫ m =
      (eTor ij).hom ≫ biproduct.ι TorFamily ij := by
    dsimp only [m, biproduct.mapIso_hom]
    exact biproduct.ι_map (fun kl => (eTor kl).hom) ij
  calc
    H.map (biproduct.ι A ij) ≫ eFinite.hom ≫ m =
        (H.map (biproduct.ι A ij) ≫ eFinite.hom) ≫ m :=
      (Category.assoc _ _ _).symm
    _ = biproduct.ι HA ij ≫ m :=
      congrArg (fun k => k ≫ m) hFinite
    _ = (eTor ij).hom ≫ biproduct.ι TorFamily ij := hMap

/-- Let R be a commutative ring, K,L nonnegative chain complexes of R-modules, and P a
Cartan–Eilenberg resolution of L. The bicomplex has resolution index a and inner tensor degree
q. For p,q ∈ ℕ and i+j=q, the selected summand's homology injection followed by the global Tor
comparison and projection back to that Tor factor equals the inverse canonical
projective-resolution coordinate for tensoring Hᵢ(K) with the resolution of Hⱼ(L). -/
theorem kunnethTorResolutionHomologyIso_ι_π
    (K : ChainComplex (ModuleCat.{u} R) ℕ)
    (P : CartanEilenbergResolution L) (p q : ℕ)
    (ij : KunnethAntidiagonal q) :
    HomologicalComplex.homologyMap
        (biproduct.ι
          (fun kl : KunnethAntidiagonal q =>
            kunnethTorResolutionSummand K P kl) ij) p ≫
      (kunnethTorResolutionHomologyIso K P p q).hom ≫
      biproduct.π
        (fun kl : KunnethAntidiagonal q =>
          ((CategoryTheory.Tor (ModuleCat.{u} R) p).obj
            (K.homology kl.val.1)).obj (L.homology kl.val.2)) ij =
      ((P.cartanEilenbergVerticalHomologyResolution ij.val.2).isoLeftDerivedObj
          ((tensoringLeft (ModuleCat.{u} R)).obj
            (K.homology ij.val.1)) p).inv := by
  let A : KunnethAntidiagonal q →
      ChainComplex (ModuleCat.{u} R) ℕ := fun kl =>
    kunnethTorResolutionSummand K P kl
  let D := Discrete.functor A
  let H := homologyFunctor (ModuleCat.{u} R) (ComplexShape.down ℕ) p
  let HA : KunnethAntidiagonal q → ModuleCat.{u} R := fun kl =>
    H.obj (A kl)
  let TorFamily : KunnethAntidiagonal q → ModuleCat.{u} R := fun kl =>
    ((CategoryTheory.Tor (ModuleCat.{u} R) p).obj
      (K.homology kl.val.1)).obj (L.homology kl.val.2)
  let _ : H.Additive := by infer_instance
  let _ : PreservesFiniteBiproducts H := by infer_instance
  let _ : PreservesColimit D H := by infer_instance
  let eComplex : kunnethTorResolutionComplex K P q ≅ ⨁ A := by
    change (⨁ A) ≅ ⨁ A
    exact Iso.refl _
  let eHomologyDiagram : (D ⋙ H) ≅ Discrete.functor HA :=
    Discrete.natIso fun _ => Iso.refl _
  let eFinite :=
    H.mapIso (biproduct.isoCoproduct A) ≪≫
      preservesColimitIso H D ≪≫
      colim.mapIso eHomologyDiagram ≪≫
      (biproduct.isoCoproduct HA).symm
  let eTor : ∀ kl : KunnethAntidiagonal q, HA kl ≅ TorFamily kl := fun kl =>
    ((P.cartanEilenbergVerticalHomologyResolution kl.val.2).isoLeftDerivedObj
      ((tensoringLeft (ModuleCat.{u} R)).obj (K.homology kl.val.1)) p).symm
  have hFinite : H.map (biproduct.ι A ij) ≫ eFinite.hom =
      biproduct.ι HA ij := by
    simp only [eFinite, Iso.trans_hom, Functor.mapIso_hom]
    rw [← Functor.map_comp_assoc]
    rw [biproduct.isoCoproduct_hom]
    rw [biproduct.ι_desc]
    rw [ι_preservesColimitIso_hom_assoc]
    rw [colim_map]
    rw [ι_colimMap_assoc]
    simp
    rfl
  let eGlobal := H.mapIso eComplex ≪≫ eFinite ≪≫ biproduct.mapIso eTor
  have hGlobal : kunnethTorResolutionHomologyIso K P p q = eGlobal := rfl
  change H.map (biproduct.ι A ij) ≫
      (kunnethTorResolutionHomologyIso K P p q).hom ≫
      biproduct.π TorFamily ij = (eTor ij).hom
  rw [hGlobal]
  dsimp only [eGlobal, eComplex, Iso.trans_hom, Functor.mapIso_hom,
    Iso.refl_hom]
  change H.map (biproduct.ι A ij) ≫
      (H.map (𝟙 (⨁ A)) ≫ eFinite.hom ≫
        (biproduct.mapIso eTor).hom) ≫
      biproduct.π TorFamily ij = (eTor ij).hom
  rw [H.map_id, Category.id_comp]
  let m := (biproduct.mapIso eTor).hom
  let π := biproduct.π TorFamily ij
  have hMap : biproduct.ι HA ij ≫ m =
      (eTor ij).hom ≫ biproduct.ι TorFamily ij := by
    dsimp only [m, biproduct.mapIso_hom]
    exact biproduct.ι_map (fun kl => (eTor kl).hom) ij
  calc
    (H.map (biproduct.ι A ij) ≫ eFinite.hom ≫ m) ≫ π =
        ((H.map (biproduct.ι A ij) ≫ eFinite.hom) ≫ m) ≫ π :=
      congrArg (fun k => k ≫ π)
        (Category.assoc (H.map (biproduct.ι A ij)) eFinite.hom m).symm
    _ = (biproduct.ι HA ij ≫ m) ≫ π :=
      congrArg (fun k => (k ≫ m) ≫ π) hFinite
    _ = ((eTor ij).hom ≫ biproduct.ι TorFamily ij) ≫ π :=
      congrArg (fun k => k ≫ π) hMap
    _ = (eTor ij).hom ≫ (biproduct.ι TorFamily ij ≫ π) :=
      Category.assoc _ _ _
    _ = (eTor ij).hom := by
      dsimp only [π]
      rw [biproduct.ι_π_self, Category.comp_id]

/-- Let R be a commutative ring, K,L nonnegative chain complexes of R-modules, and P a
Cartan–Eilenberg resolution of L. The bicomplex has resolution index a and inner tensor degree
q. For i+j=q and outer degree zero, the selected Tor-resolution coordinate followed by
Tor₀^R(Hᵢ(K),Hⱼ(L)) ≅ Hᵢ(K) ⊗ Hⱼ(L) is tensoring Hᵢ(K) with the canonical column-zero homology
augmentation of the actual resolution of Hⱼ(L). -/
theorem kunnethTorResolutionHomologyIso_zero_component
    (K : ChainComplex (ModuleCat.{u} R) ℕ)
    (P : CartanEilenbergResolution L) (q : ℕ)
    (ij : KunnethAntidiagonal q) :
    (kunnethTorResolutionSummand K P ij).pOpcycles 0 ≫
        (kunnethTorResolutionSummand K P ij).isoHomologyι₀.inv ≫
        HomologicalComplex.homologyMap
          (biproduct.ι
            (fun kl : KunnethAntidiagonal q =>
              kunnethTorResolutionSummand K P kl) ij) 0 ≫
        (kunnethTorResolutionHomologyIso K P 0 q).hom ≫
        biproduct.π
          (fun kl : KunnethAntidiagonal q =>
            ((CategoryTheory.Tor (ModuleCat.{u} R) 0).obj
              (K.homology kl.val.1)).obj (L.homology kl.val.2)) ij ≫
        (((tensoringLeft (ModuleCat.{u} R)).obj
          (K.homology ij.val.1)).leftDerivedZeroIsoSelf).hom.app
            (L.homology ij.val.2) =
      ((tensoringLeft (ModuleCat.{u} R)).obj
        (K.homology ij.val.1)).map
          (P.termColumnZeroHomologyAugmentation ij.val.2) := by
  let U := P.cartanEilenbergVerticalHomologyResolution ij.val.2
  let T := (tensoringLeft (ModuleCat.{u} R)).obj
    (K.homology ij.val.1)
  let A := kunnethTorResolutionSummand K P ij
  let eU : A.homology 0 ≅
      (T.leftDerived 0).obj (L.homology ij.val.2) :=
    (U.isoLeftDerivedObj T 0).symm
  let fromU : A.opcycles 0 ⟶ T.obj (L.homology ij.val.2) :=
    U.fromLeftDerivedZero' T
  let _ : Epi (T.map (U.π.f 0)) := by infer_instance
  have hAug (j : ℕ) :
      (P.cartanEilenbergVerticalHomologyResolution j).π.f 0 =
        P.termColumnZeroHomologyAugmentation j := by
    rcases j with _ | r
    · change (P.rowHomologyAugmentation 0).f 0 =
        P.termColumnZeroHomologyAugmentation 0
      exact P.rowHomologyAugmentation_f_zero 0
    · let C := P.bicomplex.X 0
      let eS := C.cyclesIsoSc' (r + 2) (r + 1) r (by simp) (by simp)
      let eL : (C.sc' (r + 2) (r + 1) r).cycles ≅
          (P.cyclesResolution (r + 1)).complex.X 0 :=
        (P.cartanEilenbergRowHomologySuccLeftData 0 r).cyclesIso
      let eC : C.cycles (r + 1) ≅
          (P.cyclesResolution (r + 1)).complex.X 0 := eS ≪≫ eL
      let πTerm : (P.termResolution (r + 1)).complex.X 0 ⟶
          L.X (r + 1) := (P.termResolution (r + 1)).π.f 0
      let πCycles : (P.cyclesResolution (r + 1)).complex.X 0 ⟶
          L.cycles (r + 1) := (P.cyclesResolution (r + 1)).π.f 0
      let πHomology : (P.homologyResolution (r + 1)).complex.X 0 ⟶
          L.homology (r + 1) := (P.homologyResolution (r + 1)).π.f 0
      have hπTerm : πTerm = P.termColumnZeroAugmentation.f (r + 1) := by
        dsimp only [πTerm]
        exact (P.termColumnZeroAugmentation_f (r + 1)).symm
      have hEL : eL.hom ≫ (P.termComponentShortComplex 0 (r + 1)).f =
          (C.sc' (r + 2) (r + 1) r).iCycles :=
        (P.cartanEilenbergRowHomologySuccLeftData 0 r).cyclesIso_hom_comp_i
      have hELpost := congrArg (fun k => eS.hom ≫ k) hEL
      have hEnd : eS.hom ≫ (C.sc' (r + 2) (r + 1) r).iCycles =
          C.iCycles (r + 1) :=
        HomologicalComplex.cyclesIsoSc'_hom_iCycles C
          (r + 2) (r + 1) r (by simp) (by simp)
      have hInc : eC.hom ≫ (P.termComponentShortComplex 0 (r + 1)).f =
          C.iCycles (r + 1) := by
        dsimp only [eC, Iso.trans_hom]
        exact (Category.assoc _ _ _).trans (hELpost.trans hEnd)
      have hIncRaw : eC.hom ≫ (P.termHorseshoe (r + 1)).i.f 0 =
          C.iCycles (r + 1) := by
        simpa only [CartanEilenbergResolution.termComponentShortComplex,
          CartanEilenbergResolution.termShortComplex, ShortComplex.map_f,
          HomologicalComplex.eval_map] using hInc
      have hTerm :
          (P.termHorseshoe (r + 1)).i.f 0 ≫
              πTerm = πCycles ≫ L.iCycles (r + 1) := by
        have h := HomologicalComplex.congr_hom
          (P.termHorseshoe (r + 1)).i_augmentation 0
        convert h using 1 <;>
          simp only [HomologicalComplex.comp_f,
            ChainComplex.single₀_map_f_zero,
            HomologicalComplex.single_obj_X_self,
            cyclesTermBoundaryShortComplex] <;> rfl
      have hCycles :
          (P.cyclesHorseshoe (r + 1)).p.f 0 ≫
              πHomology = πCycles ≫ L.homologyπ (r + 1) := by
        have h := HomologicalComplex.congr_hom
          (P.cyclesHorseshoe (r + 1)).p_augmentation 0
        convert h using 1 <;>
          simp only [HomologicalComplex.comp_f,
            ChainComplex.single₀_map_f_zero,
            HomologicalComplex.single_obj_X_self,
            boundaryCyclesHomologyShortComplex] <;> rfl
      have hCycleAug : eC.hom ≫
            πCycles =
          HomologicalComplex.cyclesMap P.termColumnZeroAugmentation (r + 1) := by
        apply (cancel_mono (L.iCycles (r + 1))).1
        rw [Category.assoc]
        rw [← hTerm]
        rw [← Category.assoc, hIncRaw]
        change C.iCycles (r + 1) ≫ πTerm = _
        rw [hπTerm]
        exact (HomologicalComplex.cyclesMap_i
          P.termColumnZeroAugmentation (r + 1)).symm
      change (P.cartanEilenbergRowHomologySuccIso 0 r).hom ≫
          (P.homologyResolution (r + 1)).π.f 0 =
        P.termColumnZeroHomologyAugmentation (r + 1)
      apply (cancel_epi ((P.bicomplex.X 0).homologyπ (r + 1))).1
      rw [P.homologyπ_comp_cartanEilenbergRowHomologySuccIso_hom_assoc]
      change eC.hom ≫ (P.cyclesHorseshoe (r + 1)).p.f 0 ≫
          πHomology =
        (P.bicomplex.X 0).homologyπ (r + 1) ≫
          P.termColumnZeroHomologyAugmentation (r + 1)
      rw [hCycles, ← Category.assoc, hCycleAug]
      have hNat := HomologicalComplex.homologyπ_naturality
        (φ := P.termColumnZeroAugmentation) (i := r + 1)
      simpa only [P.termColumnZeroHomologyAugmentation_eq_homologyMap] using
        hNat.symm
  let As : KunnethAntidiagonal q →
      ChainComplex (ModuleCat.{u} R) ℕ := fun kl =>
    kunnethTorResolutionSummand K P kl
  let D := Discrete.functor As
  let H := homologyFunctor (ModuleCat.{u} R) (ComplexShape.down ℕ) 0
  let HA : KunnethAntidiagonal q → ModuleCat.{u} R := fun kl =>
    H.obj (As kl)
  let TorFamily : KunnethAntidiagonal q → ModuleCat.{u} R := fun kl =>
    ((CategoryTheory.Tor (ModuleCat.{u} R) 0).obj
      (K.homology kl.val.1)).obj (L.homology kl.val.2)
  let _ : H.Additive := by infer_instance
  let _ : PreservesFiniteBiproducts H := by infer_instance
  let _ : PreservesColimit D H := by infer_instance
  let eComplex : kunnethTorResolutionComplex K P q ≅ ⨁ As := by
    change (⨁ As) ≅ ⨁ As
    exact Iso.refl _
  let eHomologyDiagram : (D ⋙ H) ≅ Discrete.functor HA :=
    Discrete.natIso fun _ => Iso.refl _
  let eFinite :=
    H.mapIso (biproduct.isoCoproduct As) ≪≫
      preservesColimitIso H D ≪≫
      colim.mapIso eHomologyDiagram ≪≫
      (biproduct.isoCoproduct HA).symm
  let eTor : ∀ kl : KunnethAntidiagonal q, HA kl ≅ TorFamily kl := fun kl =>
    ((P.cartanEilenbergVerticalHomologyResolution kl.val.2).isoLeftDerivedObj
      ((tensoringLeft (ModuleCat.{u} R)).obj (K.homology kl.val.1)) 0).symm
  have hFinite : H.map (biproduct.ι As ij) ≫ eFinite.hom =
      biproduct.ι HA ij := by
    simp only [eFinite, Iso.trans_hom, Functor.mapIso_hom]
    rw [← Functor.map_comp_assoc]
    rw [biproduct.isoCoproduct_hom]
    rw [biproduct.ι_desc]
    rw [ι_preservesColimitIso_hom_assoc]
    rw [colim_map]
    rw [ι_colimMap_assoc]
    simp
    rfl
  let eGlobal := H.mapIso eComplex ≪≫ eFinite ≪≫ biproduct.mapIso eTor
  have hGlobal : kunnethTorResolutionHomologyIso K P 0 q = eGlobal := rfl
  have hSelected :
      HomologicalComplex.homologyMap
          (biproduct.ι
            (fun kl : KunnethAntidiagonal q =>
              kunnethTorResolutionSummand K P kl) ij) 0 ≫
          (kunnethTorResolutionHomologyIso K P 0 q).hom ≫
          biproduct.π
            (fun kl : KunnethAntidiagonal q =>
              ((CategoryTheory.Tor (ModuleCat.{u} R) 0).obj
                (K.homology kl.val.1)).obj (L.homology kl.val.2)) ij =
        (eTor ij).hom := by
    change H.map (biproduct.ι As ij) ≫
        (kunnethTorResolutionHomologyIso K P 0 q).hom ≫
        biproduct.π TorFamily ij = (eTor ij).hom
    rw [hGlobal]
    dsimp only [eGlobal, eComplex, Iso.trans_hom, Functor.mapIso_hom,
      Iso.refl_hom]
    change H.map (biproduct.ι As ij) ≫
        (H.map (𝟙 (⨁ As)) ≫ eFinite.hom ≫
          (biproduct.mapIso eTor).hom) ≫
        biproduct.π TorFamily ij = (eTor ij).hom
    rw [H.map_id, Category.id_comp]
    let m := (biproduct.mapIso eTor).hom
    let p := biproduct.π TorFamily ij
    have hMap : biproduct.ι HA ij ≫ m =
        (eTor ij).hom ≫ biproduct.ι TorFamily ij := by
      dsimp only [m, biproduct.mapIso_hom]
      exact biproduct.ι_map (fun kl => (eTor kl).hom) ij
    calc
      (H.map (biproduct.ι As ij) ≫ eFinite.hom ≫ m) ≫ p =
          ((H.map (biproduct.ι As ij) ≫ eFinite.hom) ≫ m) ≫ p :=
        congrArg (fun k => k ≫ p)
          (Category.assoc (H.map (biproduct.ι As ij)) eFinite.hom m).symm
      _ = (biproduct.ι HA ij ≫ m) ≫ p :=
        congrArg (fun k => (k ≫ m) ≫ p) hFinite
      _ = ((eTor ij).hom ≫ biproduct.ι TorFamily ij) ≫ p :=
        congrArg (fun k => k ≫ p) hMap
      _ = (eTor ij).hom ≫ (biproduct.ι TorFamily ij ≫ p) :=
        Category.assoc _ _ _
      _ = (eTor ij).hom := by
        dsimp only [p]
        rw [biproduct.ι_π_self, Category.comp_id]
  let f₀ := HomologicalComplex.homologyMap
    (biproduct.ι
      (fun kl : KunnethAntidiagonal q =>
        kunnethTorResolutionSummand K P kl) ij) 0
  let f₁ := (kunnethTorResolutionHomologyIso K P 0 q).hom
  let f₂ := biproduct.π
    (fun kl : KunnethAntidiagonal q =>
      ((CategoryTheory.Tor (ModuleCat.{u} R) 0).obj
        (K.homology kl.val.1)).obj (L.homology kl.val.2)) ij
  let f₃ := T.leftDerivedZeroIsoSelf.hom.app (L.homology ij.val.2)
  have hSelectedTail := congrArg
    (fun k => k ≫ f₃) hSelected
  have hRoute :
      HomologicalComplex.homologyMap
            (biproduct.ι
              (fun kl : KunnethAntidiagonal q =>
                kunnethTorResolutionSummand K P kl) ij) 0 ≫
          (kunnethTorResolutionHomologyIso K P 0 q).hom ≫
          biproduct.π
            (fun kl : KunnethAntidiagonal q =>
              ((CategoryTheory.Tor (ModuleCat.{u} R) 0).obj
                (K.homology kl.val.1)).obj (L.homology kl.val.2)) ij ≫
          T.leftDerivedZeroIsoSelf.hom.app (L.homology ij.val.2) =
        (eTor ij).hom ≫
          T.leftDerivedZeroIsoSelf.hom.app (L.homology ij.val.2) := by
    change f₀ ≫ f₁ ≫ f₂ ≫ f₃ = (eTor ij).hom ≫ f₃
    change (f₀ ≫ f₁ ≫ f₂) ≫ f₃ = (eTor ij).hom ≫ f₃ at hSelectedTail
    have hAssoc : (f₀ ≫ f₁ ≫ f₂) ≫ f₃ =
        f₀ ≫ f₁ ≫ f₂ ≫ f₃ :=
      (Category.assoc f₀ (f₁ ≫ f₂) f₃).trans
        (congrArg (fun k => f₀ ≫ k) (Category.assoc f₁ f₂ f₃))
    exact hAssoc.symm.trans hSelectedTail
  change A.pOpcycles 0 ≫ A.isoHomologyι₀.inv ≫
      HomologicalComplex.homologyMap
        (biproduct.ι
          (fun kl : KunnethAntidiagonal q =>
            kunnethTorResolutionSummand K P kl) ij) 0 ≫
      (kunnethTorResolutionHomologyIso K P 0 q).hom ≫
      biproduct.π
        (fun kl : KunnethAntidiagonal q =>
          ((CategoryTheory.Tor (ModuleCat.{u} R) 0).obj
            (K.homology kl.val.1)).obj (L.homology kl.val.2)) ij ≫
      T.leftDerivedZeroIsoSelf.hom.app (L.homology ij.val.2) =
    T.map (P.termColumnZeroHomologyAugmentation ij.val.2)
  rw [← hAug ij.val.2]
  rw [hRoute]
  change A.pOpcycles 0 ≫ A.isoHomologyι₀.inv ≫
        eU.hom ≫
        T.fromLeftDerivedZero.app (L.homology ij.val.2) =
      T.map (U.π.f 0)
  have hDerived :
      T.fromLeftDerivedZero.app (L.homology ij.val.2) =
        eU.inv ≫ A.isoHomologyι₀.hom ≫ fromU := by
    exact ProjectiveResolution.fromLeftDerivedZero_eq U T
  have hFrom : A.pOpcycles 0 ≫ fromU = T.map (U.π.f 0) := by
    exact U.pOpcycles_comp_fromLeftDerivedZero' T
  rw [hDerived]
  rw [eU.hom_inv_id_assoc]
  rw [A.isoHomologyι₀.inv_hom_id_assoc]
  exact hFrom

end HomologicalComplex

end
