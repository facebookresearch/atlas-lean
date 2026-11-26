/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Algebra.Category.ModuleCat.UliftRestriction
public import MathlibExt.Algebra.Category.ModuleCat.Bimodule.TorScalarChangeCoherence
public import MathlibExt.CategoryTheory.Functor.ComparisonTransport
public import MathlibExt.CategoryTheory.Abelian.LeftDerived.TransportComparison

/-!
# Height transport of canonical bimodule Tor ring-change maps

Let R,S be rings and B an (R,S)-bimodule, represented as an enveloping
ring module. Put Γ=max(r,a,b,z), Γ′=max(r,a,b,z,t).
Tensoring at Γ′ after lifting the source is naturally isomorphic
to lifting the tensor output from Γ. Deriving gives the corresponding
Tor height isomorphism; the source lift preserves projectives because
Γ contains R, and the output lift is exact.

For endpoint maps R→R′, S→S′ and compatible source/coefficient maps,
the Tor ring-change square commutes with these height comparisons.
Restriction of the outer action commutes with lifting its carrier,
so the inverse comparisons also preserve the ring-change map.
The ring and carrier worlds remain independent, and neither outer
ring world is bounded by the sufficient source height.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits MulOpposite
open ModuleCat.BalancedTensorRight
open scoped TensorProduct

universe rGlobal rGlobal' sGlobal sGlobal' aGlobal aGlobal' bGlobal bGlobal' zGlobal tGlobal


namespace ModuleCat.Bimodule.Tensor

variable (R : Type rGlobal) (S : Type sGlobal) [Ring R] [Ring S]

/-- For an (R,S)-bimodule B, source lift Γ→Γ′ followed
by tensoring with the coefficient lifted to Γ′ is naturally
isomorphic to tensoring with its Γ-lift and then lifting
the output. Here Γ=max(r,a,b,z), Γ′=max(r,a,b,z,t). -/
def coefficientLargeTensorHeightIsoAt.{t, z, r, s, a, b} (R : Type r) (S : Type s) [Ring R] [Ring S]
    (B : coefficientCategory.{r, s, b} R S) :
    ModuleCat.uliftFunctor.{max r a b z t, max r a b z} Rᵐᵒᵖ ⋙
        (coefficientTensorObj R S
          ((ModuleCat.uliftFunctor.{max r a b z t, b} (R ⊗[ℤ] Sᵐᵒᵖ)).obj B)).obj ≅
      (coefficientTensorObj R S
          ((ModuleCat.uliftFunctor.{max r a b z, b} (R ⊗[ℤ] Sᵐᵒᵖ)).obj B)).obj ⋙
        ModuleCat.uliftFunctor.{max r a b z t, max r a b z} Sᵐᵒᵖ := by
  letI := coefficientLeftModule R S B
  letI := coefficientRightModule R S B
  letI := coefficientActionsCommute R S B
  exact tensorHeightIsoAt.{t, z, r, s, a, b} R S B

/-- For an (R,S)-bimodule B and n≥0, the output lift of
its height-Γ derived tensor functor is naturally isomorphic
to height-Γ′ derived tensor after source lifting.
Both source heights contain R, and the outer ring S is independent. -/
def coefficientLargeTorHeightIsoAt.{t, z, r, s, a, b} (R : Type r) (S : Type s) [Ring R] [Ring S]
    (B : coefficientCategory.{r, s, b} R S) (n : ℕ) :
    (coefficientTorFunctor.{r, s, max r a b z} R S n).obj
        ((ModuleCat.uliftFunctor.{max r a b z, b} (R ⊗[ℤ] Sᵐᵒᵖ)).obj B) ⋙
      ModuleCat.uliftFunctor.{max r a b z t, max r a b z} Sᵐᵒᵖ ≅
    ModuleCat.uliftFunctor.{max r a b z t, max r a b z} Rᵐᵒᵖ ⋙
      (coefficientTorFunctor.{r, s, max r a b z t} R S n).obj
        ((ModuleCat.uliftFunctor.{max r a b z t, b} (R ⊗[ℤ] Sᵐᵒᵖ)).obj B) := by
  letI := coefficientLeftModule R S B
  letI := coefficientRightModule R S B
  letI := coefficientActionsCommute R S B
  exact largeTorHeightIsoAt.{t, z, r, s, a, b} R S B n

/-- For an (R,S)-bimodule B and heights Γ≤Γ′, the inverse
of the canonical Tor height isomorphism equals the derived
map determined by the tensor comparison
F_Γ′∘U_R→U_S∘F_Γ.
Source lifting preserves projective resolutions and output
lifting preserves homology. -/
theorem coefficientLargeTorHeightIsoAt_inv_square.{t, z, r, s, a, b} (R : Type r) (S : Type s) [Ring R] [Ring S]
    (B : coefficientCategory.{r, s, b} R S) (n : ℕ) :
    let U := ModuleCat.uliftFunctor.{max r a b z t, max r a b z} Rᵐᵒᵖ
    let V := ModuleCat.uliftFunctor.{max r a b z t, max r a b z} Sᵐᵒᵖ
    letI : U.PreservesHomology := Functor.preservesHomologyOfExact U
    letI : V.PreservesHomology := Functor.preservesHomologyOfExact V
    (coefficientLargeTorHeightIsoAt.{t, z, r, s, a, b} R S B n).inv =
      Functor.leftDerivedSquareHom U V
        (coefficientTensorObj R S
          ((ModuleCat.uliftFunctor.{max r a b z t, b} (R ⊗[ℤ] Sᵐᵒᵖ)).obj B)).obj
        (coefficientTensorObj R S
          ((ModuleCat.uliftFunctor.{max r a b z, b} (R ⊗[ℤ] Sᵐᵒᵖ)).obj B)).obj
        (coefficientLargeTensorHeightIsoAt.{t, z, r, s, a, b} R S B).hom n := by
  let U := ModuleCat.uliftFunctor.{max r a b z t, max r a b z} Rᵐᵒᵖ
  let V := ModuleCat.uliftFunctor.{max r a b z t, max r a b z} Sᵐᵒᵖ
  letI : U.PreservesHomology := Functor.preservesHomologyOfExact U
  letI : V.PreservesHomology := Functor.preservesHomologyOfExact V
  letI : U.PreservesProjectiveObjects := inferInstance
  letI := coefficientLeftModule R S B
  letI := coefficientRightModule R S B
  letI := coefficientActionsCommute R S B
  let F := (coefficientTensorObj R S
    ((ModuleCat.uliftFunctor.{max r a b z, b} (R ⊗[ℤ] Sᵐᵒᵖ)).obj B)).obj
  let G := (coefficientTensorObj R S
    ((ModuleCat.uliftFunctor.{max r a b z t, b} (R ⊗[ℤ] Sᵐᵒᵖ)).obj B)).obj
  let e := coefficientLargeTensorHeightIsoAt.{t, z, r, s, a, b} R S B
  change (coefficientLargeTorHeightIsoAt.{t, z, r, s, a, b} R S B n).inv =
    Functor.leftDerivedSquareHom U V G F e.hom n
  rw [Functor.leftDerivedSquareHom_of_preservesProjectives]
  exact Functor.leftDerivedTransportIso_inv U V F G e n


/-- For an (R,S)-bimodule B and n≥0, lifting the output
of its independently sourced Tor functor at Γ gives an
isomorphism with the functor at Γ′.
The source remains ModuleCat^a(Rᵒᵖ), with Γ=max(r,a,b,z)
and Γ′=max(r,a,b,z,t). -/
def coefficientTorHeightIsoAt.{t, z, r, s, a, b} (R : Type r) (S : Type s) [Ring R] [Ring S]
    (B : coefficientCategory.{r, s, b} R S) (n : ℕ) :
    (torCoefficientFunctorAt.{z, r, s, a, b} R S n).obj B ⋙
      ModuleCat.uliftFunctor.{max r a b z t, max r a b z} Sᵐᵒᵖ ≅
        (torCoefficientFunctorAt.{max z t, r, s, a, b} R S n).obj B := by
  letI := coefficientLeftModule R S B
  letI := coefficientRightModule R S B
  letI := coefficientActionsCommute R S B
  exact torHeightIsoAt.{t, z, r, s, a, b} R S B n

/-- For an original right R-module A, the coefficient Tor
height map first applies the sufficient-world comparison
at ULift^Γ A, then applies the higher derived functor to
ULift^Γ′(ULift^Γ A)→ULift^Γ′A.
This is its canonical source-flattening factorization. -/
theorem coefficientTorHeightIsoAt_hom_app.{t, z, r, s, a, b} (R : Type r) (S : Type s) [Ring R] [Ring S]
    (B : coefficientCategory.{r, s, b} R S) (A : ModuleCat.{a} Rᵐᵒᵖ) (n : ℕ) :
    (coefficientTorHeightIsoAt.{t, z, r, s, a, b} R S B n).hom.app A =
      (coefficientLargeTorHeightIsoAt.{t, z, r, s, a, b} R S B n).hom.app
          ((ModuleCat.uliftFunctor.{max r a b z, a} Rᵐᵒᵖ).obj A) ≫
        ((coefficientTorFunctor.{r, s, max r a b z t} R S n).obj
          ((ModuleCat.uliftFunctor.{max r a b z t, b} (R ⊗[ℤ] Sᵐᵒᵖ)).obj B)).map
          ((ModuleCat.uliftFunctorCompIso.{max r a b z, max r a b z t, a} Rᵐᵒᵖ).hom.app A) := by
  letI := coefficientLeftModule R S B
  letI := coefficientRightModule R S B
  letI := coefficientActionsCommute R S B
  exact torHeightIsoAt_hom_app.{t, z, r, s, a, b} R S B n A

/-- For an original right R-module A, the inverse coefficient
Tor height map first applies the higher derived functor
to ULift^Γ′A→ULift^Γ′(ULift^Γ A), then uses the inverse
sufficient-world comparison at ULift^Γ A. -/
theorem coefficientTorHeightIsoAt_inv_app.{t, z, r, s, a, b} (R : Type r) (S : Type s) [Ring R] [Ring S]
    (B : coefficientCategory.{r, s, b} R S) (A : ModuleCat.{a} Rᵐᵒᵖ) (n : ℕ) :
    (coefficientTorHeightIsoAt.{t, z, r, s, a, b} R S B n).inv.app A =
      ((coefficientTorFunctor.{r, s, max r a b z t} R S n).obj
          ((ModuleCat.uliftFunctor.{max r a b z t, b} (R ⊗[ℤ] Sᵐᵒᵖ)).obj B)).map
        ((ModuleCat.uliftFunctorCompIso.{max r a b z, max r a b z t, a} Rᵐᵒᵖ).inv.app A) ≫
      (coefficientLargeTorHeightIsoAt.{t, z, r, s, a, b} R S B n).inv.app
        ((ModuleCat.uliftFunctor.{max r a b z, a} Rᵐᵒᵖ).obj A) := by
  letI := coefficientLeftModule R S B
  letI := coefficientRightModule R S B
  letI := coefficientActionsCommute R S B
  exact Functor.precompositionComparisonIso_inv_app
    (ModuleCat.uliftFunctor.{max r a b z, a} Rᵐᵒᵖ)
    (ModuleCat.uliftFunctor.{max r a b z t, a} Rᵐᵒᵖ)
    (ModuleCat.uliftFunctor.{max r a b z t, max r a b z} Rᵐᵒᵖ)
    (ModuleCat.uliftFunctor.{max r a b z t, max r a b z} Sᵐᵒᵖ)
    ((coefficientTorFunctor.{r, s, max r a b z} R S n).obj
      ((ModuleCat.uliftFunctor.{max r a b z, b} (R ⊗[ℤ] Sᵐᵒᵖ)).obj B))
    ((coefficientTorFunctor.{r, s, max r a b z t} R S n).obj
      ((ModuleCat.uliftFunctor.{max r a b z t, b} (R ⊗[ℤ] Sᵐᵒᵖ)).obj B))
    (coefficientLargeTorHeightIsoAt.{t, z, r, s, a, b} R S B n)
    (ModuleCat.uliftFunctorCompIso.{max r a b z, max r a b z t, a} Rᵐᵒᵖ) A

section RingHeight

variable {R' : Type rGlobal'} {S' : Type sGlobal'} [Ring R'] [Ring S']

/-- For endpoint maps φ:R→R′, ψ:S→S′ and compatible
coefficient/source maps at Γ=max(r,r′,a,a′,b,b′,z),
the higher Tor ring-change map commutes with the inverse
source and target height isomorphisms Γ′→Γ.
The outer target comparison includes the canonical interchange
of scalar restriction with carrier lifting. -/
theorem torRingChangeLargeHeight_inverse.{t, z, r, r', s, s', a, a', b, b'} (R : Type r) (S : Type s) [Ring R]
  [Ring S] {R' : Type r'} {S' : Type s'} [Ring R'] [Ring S']
    (φ : R →+* R') (ψ : S →+* S')
    (B : coefficientCategory.{r, s, b} R S)
    (B' : coefficientCategory.{r', s', b'} R' S')
    (f : B →ₛₗ[RingChange.envelopingRingHom φ ψ] B')
    (X : ModuleCat.{max r r' a a' b b' z} Rᵐᵒᵖ)
    (Y : ModuleCat.{max r r' a a' b b' z} R'ᵐᵒᵖ)
    (g : X ⟶ (ModuleCat.restrictScalars φ.op).obj Y) (n : ℕ) :
    let I := ModuleCat.uliftFunctor.{max r r' a a' b b' z t, max r r' a a' b b' z} Rᵐᵒᵖ
    let K := ModuleCat.uliftFunctor.{max r r' a a' b b' z t, max r r' a a' b b' z} Sᵐᵒᵖ
    let eU := ModuleCat.uliftRestrictionIso.{t, max r r' a a' b b' z, r, r'} φ.op
    let eV := ModuleCat.uliftRestrictionIso.{t, max r r' a a' b b' z, s, s'} ψ.op
    let C₀ := (ModuleCat.uliftFunctor.{max r r' a a' b b' z, b}
      (R ⊗[ℤ] Sᵐᵒᵖ)).obj B
    let C₁ := (ModuleCat.uliftFunctor.{max r r' a a' b b' z t, b}
      (R ⊗[ℤ] Sᵐᵒᵖ)).obj B
    let D₀ := (ModuleCat.uliftFunctor.{max r r' a a' b b' z, b'}
      (R' ⊗[ℤ] S'ᵐᵒᵖ)).obj B'
    let D₁ := (ModuleCat.uliftFunctor.{max r r' a a' b b' z t, b'}
      (R' ⊗[ℤ] S'ᵐᵒᵖ)).obj B'
    let f₀ := liftCoefficientRingChangeAt.{z, r, r', s, s', a, a', b, b'} R S φ ψ B B' f
    let f₁ := liftCoefficientRingChangeAt.{max z t, r, r', s, s', a, a', b, b'} R S φ ψ B B' f
    torRingChangeMap R S φ ψ C₁ D₁ f₁ n (I.map g ≫ eU.hom.app Y) ≫
        (ModuleCat.restrictScalars ψ.op).map
          ((coefficientLargeTorHeightIsoAt.{t, max r a b z, r', s', a', b'}
            R' S' B' n).inv.app Y) ≫
        eV.inv.app (((coefficientTorFunctor.{r', s', max r r' a a' b b' z} R' S' n).obj D₀).obj Y) =
      (coefficientLargeTorHeightIsoAt.{t, max r' a' b' z, r, s, a, b} R S B n).inv.app X ≫
        K.map (torRingChangeMap R S φ ψ C₀ D₀ f₀ n g) := by
  let I := ModuleCat.uliftFunctor.{max r r' a a' b b' z t, max r r' a a' b b' z} Rᵐᵒᵖ
  let J := ModuleCat.uliftFunctor.{max r r' a a' b b' z t, max r r' a a' b b' z} R'ᵐᵒᵖ
  let K := ModuleCat.uliftFunctor.{max r r' a a' b b' z t, max r r' a a' b b' z} Sᵐᵒᵖ
  let L := ModuleCat.uliftFunctor.{max r r' a a' b b' z t, max r r' a a' b b' z} S'ᵐᵒᵖ
  let U₀ := ModuleCat.restrictScalars.{max r r' a a' b b' z} φ.op
  let U₁ := ModuleCat.restrictScalars.{max r r' a a' b b' z t} φ.op
  let V₀ := ModuleCat.restrictScalars.{max r r' a a' b b' z} ψ.op
  let V₁ := ModuleCat.restrictScalars.{max r r' a a' b b' z t} ψ.op
  letI : I.PreservesHomology := Functor.preservesHomologyOfExact I
  letI : J.PreservesHomology := Functor.preservesHomologyOfExact J
  letI : K.PreservesHomology := Functor.preservesHomologyOfExact K
  letI : L.PreservesHomology := Functor.preservesHomologyOfExact L
  letI : U₀.PreservesHomology := Functor.preservesHomologyOfExact U₀
  letI : U₁.PreservesHomology := Functor.preservesHomologyOfExact U₁
  letI : V₀.PreservesHomology := Functor.preservesHomologyOfExact V₀
  letI : V₁.PreservesHomology := Functor.preservesHomologyOfExact V₁
  let eU := ModuleCat.uliftRestrictionIso.{t, max r r' a a' b b' z, r, r'} φ.op
  let eV := ModuleCat.uliftRestrictionIso.{t, max r r' a a' b b' z, s, s'} ψ.op
  let C₀ := (ModuleCat.uliftFunctor.{max r r' a a' b b' z, b} (R ⊗[ℤ] Sᵐᵒᵖ)).obj B
  let C₁ := (ModuleCat.uliftFunctor.{max r r' a a' b b' z t, b} (R ⊗[ℤ] Sᵐᵒᵖ)).obj B
  let D₀ := (ModuleCat.uliftFunctor.{max r r' a a' b b' z, b'} (R' ⊗[ℤ] S'ᵐᵒᵖ)).obj B'
  let D₁ := (ModuleCat.uliftFunctor.{max r r' a a' b b' z t, b'} (R' ⊗[ℤ] S'ᵐᵒᵖ)).obj B'
  let F₀ := (coefficientTensorObj R S C₀).obj
  let F₁ := (coefficientTensorObj R S C₁).obj
  let G₀ := (coefficientTensorObj R' S' D₀).obj
  let G₁ := (coefficientTensorObj R' S' D₁).obj
  let f₀ := liftCoefficientRingChangeAt.{z, r, r', s, s', a, a', b, b'} R S φ ψ B B' f
  let f₁ := liftCoefficientRingChangeAt.{max z t, r, r', s, s', a, a', b, b'} R S φ ψ B B' f
  let α₀ := tensorRingChangeTransformation R S φ ψ C₀ D₀ f₀
  let α₁ := tensorRingChangeTransformation R S φ ψ C₁ D₁ f₁
  let eF := coefficientLargeTensorHeightIsoAt.{t, max r' a' b' z, r, s, a, b} R S B
  let eG := coefficientLargeTensorHeightIsoAt.{t, max r a b z, r', s', a', b'} R' S' B'
  have hCube :
      Functor.composeLeftDerivedSquare I U₀ (U₀ ⋙ I) (Iso.refl _) K V₀ (V₀ ⋙ K) (Iso.refl _)
          F₁ F₀ G₀ eF.hom α₀ =
        Functor.composeLeftDerivedSquare U₁ J (U₀ ⋙ I) eU.symm V₁ L (V₀ ⋙ K) eV.symm
          F₁ G₁ G₀ α₁ eG.hom := by
    apply NatTrans.ext
    funext Z
    rw [Functor.composeLeftDerivedSquare_app, Functor.composeLeftDerivedSquare_app]
    simp only [Iso.refl_hom, Iso.refl_inv, Iso.symm_hom, Iso.symm_inv,
      NatTrans.id_app, Functor.map_id, Category.id_comp, Category.comp_id]
    apply hom_ext R S C₁ (I.obj (U₀.obj Z))
    intro x y
    cases x
    cases y
    rfl
  have h := Functor.leftDerivedSquareHom_cube_inverse
    I J K L U₀ U₁ V₀ V₁ eU eV F₀ F₁ G₀ G₁ eF eG α₀ α₁ hCube n Y
  rw [← coefficientLargeTorHeightIsoAt_inv_square.{t, max r' a' b' z, r, s, a, b} R S B n,
    ← coefficientLargeTorHeightIsoAt_inv_square.{t, max r a b z, r', s', a', b'} R' S' B' n] at h
  have h' := congrArg (fun m => (F₁.leftDerived n).map (I.map g) ≫ m) h
  have hNat := (coefficientLargeTorHeightIsoAt.{t, max r' a' b' z, r, s, a, b}
    R S B n).inv.naturality g
  have hNat' : (F₁.leftDerived n).map (I.map g) ≫
      (coefficientLargeTorHeightIsoAt.{t, max r' a' b' z, r, s, a, b}
        R S B n).inv.app (U₀.obj Y) =
    (coefficientLargeTorHeightIsoAt.{t, max r' a' b' z, r, s, a, b}
      R S B n).inv.app X ≫ K.map ((F₀.leftDerived n).map g) := hNat
  conv_lhs at h' => rw [← Category.assoc, ← Functor.map_comp]
  have hRight := congrArg
    (fun m => m ≫ K.map ((Functor.leftDerivedSquareHom U₀ V₀ F₀ G₀ α₀ n).app Y)) hNat'
  have hCollapse :
      ((coefficientLargeTorHeightIsoAt.{t, max r' a' b' z, r, s, a, b}
        R S B n).inv.app X ≫ K.map ((F₀.leftDerived n).map g)) ≫
        K.map ((Functor.leftDerivedSquareHom U₀ V₀ F₀ G₀ α₀ n).app Y) =
      (coefficientLargeTorHeightIsoAt.{t, max r' a' b' z, r, s, a, b}
        R S B n).inv.app X ≫
        K.map ((F₀.leftDerived n).map g ≫
          (Functor.leftDerivedSquareHom U₀ V₀ F₀ G₀ α₀ n).app Y) :=
    (Category.assoc _ _ _).trans (congrArg
      (fun m => (coefficientLargeTorHeightIsoAt.{t, max r' a' b' z, r, s, a, b}
        R S B n).inv.app X ≫ m) (K.map_comp _ _).symm)
  exact h'.trans (hRight.trans hCollapse)

end RingHeight

section OriginalHeight

variable {R' : Type rGlobal'} {S' : Type sGlobal'} [Ring R'] [Ring S']

/-- For endpoint maps φ,ψ and independently sized semilinear
coefficient/input maps f,g, the Tor change at Γ′ followed by
the inverse target height and restriction/lift comparisons
equals the inverse source height map followed by the lifted
Tor change at Γ, where Γ′=max(Γ,t). -/
theorem torRingChangeMapAt_height_inverse.{t, z, r, r', s, s', a, a', b, b'} (R : Type r) (S : Type s) [Ring R]
  [Ring S] {R' : Type r'} {S' : Type s'} [Ring R'] [Ring S']
    (φ : R →+* R') (ψ : S →+* S')
    (B : coefficientCategory.{r, s, b} R S)
    (B' : coefficientCategory.{r', s', b'} R' S')
    (f : B →ₛₗ[RingChange.envelopingRingHom φ ψ] B')
    (A : ModuleCat.{a} Rᵐᵒᵖ) (A' : ModuleCat.{a'} R'ᵐᵒᵖ) (g : A →ₛₗ[φ.op] A') (n : ℕ) :
    torRingChangeMapAt.{max z t, r, r', s, s', a, a', b, b'} R S φ ψ B B' f A A' g n ≫
        (ModuleCat.restrictScalars ψ.op).map
          ((coefficientTorHeightIsoAt.{t, max r a b z, r', s', a', b'} R' S' B' n).inv.app A') ≫
        (ModuleCat.uliftRestrictionIso.{t, max r r' a a' b b' z, s, s'} ψ.op).inv.app
          (((torCoefficientFunctorAt.{max r a b z, r', s', a', b'} R' S' n).obj B').obj A') =
      (coefficientTorHeightIsoAt.{t, max r' a' b' z, r, s, a, b} R S B n).inv.app A ≫
        (ModuleCat.uliftFunctor.{max r r' a a' b b' z t, max r r' a a' b b' z} Sᵐᵒᵖ).map
          (torRingChangeMapAt.{z, r, r', s, s', a, a', b, b'} R S φ ψ B B' f A A' g n) := by
  let I := ModuleCat.uliftFunctor.{max r r' a a' b b' z t, max r r' a a' b b' z} Rᵐᵒᵖ
  let K := ModuleCat.uliftFunctor.{max r r' a a' b b' z t, max r r' a a' b b' z} Sᵐᵒᵖ
  let U₁ := ModuleCat.restrictScalars.{max r r' a a' b b' z t} φ.op
  let V₁ := ModuleCat.restrictScalars.{max r r' a a' b b' z t} ψ.op
  let eU := ModuleCat.uliftRestrictionIso.{t, max r r' a a' b b' z, r, r'} φ.op
  let X := (ModuleCat.uliftFunctor.{max r r' a a' b b' z, a} Rᵐᵒᵖ).obj A
  let Y := (ModuleCat.uliftFunctor.{max r r' a a' b b' z, a'} R'ᵐᵒᵖ).obj A'
  let C₁ := (ModuleCat.uliftFunctor.{max r r' a a' b b' z t, b} (R ⊗[ℤ] Sᵐᵒᵖ)).obj B
  let D₁ := (ModuleCat.uliftFunctor.{max r r' a a' b b' z t, b'} (R' ⊗[ℤ] S'ᵐᵒᵖ)).obj B'
  let TF := (coefficientTorFunctor.{r, s, max r r' a a' b b' z t} R S n).obj C₁
  let TG := (coefficientTorFunctor.{r', s', max r r' a a' b b' z t} R' S' n).obj D₁
  let eX := (ModuleCat.uliftFunctorCompIso.{max r r' a a' b b' z,
    max r r' a a' b b' z t, a} Rᵐᵒᵖ).app A
  let eY := (ModuleCat.uliftFunctorCompIso.{max r r' a a' b b' z,
    max r r' a a' b b' z t, a'} R'ᵐᵒᵖ).app A'
  let g₀ := liftInputRingChangeAt.{z, r, r', a, a', b, b'} R φ A A' g
  let g₁ := liftInputRingChangeAt.{max z t, r, r', a, a', b, b'} R φ A A' g
  let gDouble := I.map g₀ ≫ eU.hom.app Y
  let f₁ := liftCoefficientRingChangeAt.{max z t, r, r', s, s', a, a', b, b'} R S φ ψ B B' f
  have hInput : eX.inv ≫ gDouble = g₁ ≫ U₁.map eY.inv := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    cases x
    rfl
  have hMap : torRingChangeMap R S φ ψ C₁ D₁ f₁ n g₁ ≫ V₁.map (TG.map eY.inv) =
      TF.map eX.inv ≫ torRingChangeMap R S φ ψ C₁ D₁ f₁ n gDouble := by
    rw [torRingChangeMap_naturality_target, ← hInput, ← torRingChangeMap_naturality_source]
  have hLarge := torRingChangeLargeHeight_inverse.{t, z, r, r', s, s', a, a', b, b'}
    R S φ ψ B B' f X Y g₀ n
  have h := congrArg (fun m => TF.map eX.inv ≫ m) hLarge
  have hSource := coefficientTorHeightIsoAt_inv_app.{t, max r' a' b' z, r, s, a, b} R S B A n
  have hSource' : TF.map eX.inv ≫
      (coefficientLargeTorHeightIsoAt.{t, max r' a' b' z, r, s, a, b}
        R S B n).inv.app X =
    (coefficientTorHeightIsoAt.{t, max r' a' b' z, r, s, a, b}
      R S B n).inv.app A := hSource.symm
  have hTarget := coefficientTorHeightIsoAt_inv_app.{t, max r a b z, r', s', a', b'} R' S' B' A' n
  have hTarget' : TG.map eY.inv ≫
      (coefficientLargeTorHeightIsoAt.{t, max r a b z, r', s', a', b'}
        R' S' B' n).inv.app Y =
      (coefficientTorHeightIsoAt.{t, max r a b z, r', s', a', b'}
        R' S' B' n).inv.app A' := hTarget.symm
  conv_lhs at h =>
    rw [← Category.assoc, ← hMap]
    simp only [Category.assoc]
    rw [← Category.assoc (V₁.map (TG.map eY.inv)), ← V₁.map_comp, hTarget']
  conv_rhs at h =>
    rw [← Category.assoc, hSource']
  exact h

end OriginalHeight

end ModuleCat.Bimodule.Tensor
