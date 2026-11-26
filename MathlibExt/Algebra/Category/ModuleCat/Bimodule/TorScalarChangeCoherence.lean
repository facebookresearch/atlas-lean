/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Algebra.Category.ModuleCat.Bimodule.TorScalarChange
public import MathlibExt.CategoryTheory.Abelian.LeftDerived.SquareCoherence

/-!
# Composition coherence of bimodule Tor ring-change maps

Let R→R′→R″ and S→S′→S″ be ring maps, with compatible bimodule
maps f,f′ and right-module maps g,g′. Composing their restricted
coefficient and input maps uses the canonical scalar-restriction
composition comparisons, which retain the underlying values.

The corresponding tensor maps between resolution complexes compose
in the same order. If the three common-world source categories have
projective resolutions, the canonical Tor ring-change maps therefore
compose to the map for the composite endpoint maps and coefficient/input
maps.

For independent source and coefficient worlds, the same law holds at
Γ=max(r,r′,r″,a,a′,a″,b,b′,b″,z). The outer ring worlds s,s′,s″
remain independent of Γ. Every Tor degree n≥0 is covered.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits MulOpposite
open ModuleCat.BalancedTensorRight
open scoped TensorProduct

universe rGlobal rGlobal' rGlobal'' sGlobal sGlobal' sGlobal'' v aGlobal aGlobal' aGlobal'' bGlobal bGlobal'
  bGlobal'' zGlobal

namespace ModuleCat.Bimodule.Tensor

variable (R : Type rGlobal) (S : Type sGlobal) [Ring R] [Ring S]
  {R' : Type rGlobal'} {S' : Type sGlobal'} [Ring R'] [Ring S']
  {R'' : Type rGlobal''} {S'' : Type sGlobal''} [Ring R''] [Ring S'']
  (φ : R →+* R') (ψ : S →+* S') (φ' : R' →+* R'') (ψ' : S' →+* S'')

/-- For B→Res_(φ,ψ)(B′) and B′→Res_(φ′,ψ′)(B″),
the composite coefficient map is B→Res_(φ′φ,ψ′ψ)(B″).
It applies the two maps in order and uses the canonical
restriction-composition isomorphism on the target. -/
def compositeCoefficientRingChange
    {B : coefficientCategory.{rGlobal, sGlobal, v} R S}
    {B' : coefficientCategory.{rGlobal', sGlobal', v} R' S'}
    {B'' : coefficientCategory.{rGlobal'', sGlobal'', v} R'' S''}
    (f : B ⟶ (RingChange.restrictFunctor φ ψ).obj B')
    (f' : B' ⟶ (RingChange.restrictFunctor φ' ψ').obj B'') :
    B ⟶ (RingChange.restrictFunctor (φ'.comp φ) (ψ'.comp ψ)).obj B'' :=
  f ≫ (RingChange.restrictFunctor φ ψ).map f' ≫
    (RingChange.restrictComp φ ψ φ' ψ').inv.app B''

/-- For A→Res_(φᵒᵖ)(A′) and A′→Res_(φ′ᵒᵖ)(A″),
the composite input is A→Res_((φ′φ)ᵒᵖ)(A″).
Its underlying value is g′(g(x)), with the canonical
comparison of the two restrictions. -/
def compositeInputRingChange
    {A : ModuleCat.{v} Rᵐᵒᵖ} {A' : ModuleCat.{v} R'ᵐᵒᵖ}
    {A'' : ModuleCat.{v} R''ᵐᵒᵖ}
    (g : A ⟶ (ModuleCat.restrictScalars φ.op).obj A')
    (g' : A' ⟶ (ModuleCat.restrictScalars φ'.op).obj A'') :
    A ⟶ (ModuleCat.restrictScalars (φ'.comp φ).op).obj A'' :=
  g ≫ (ModuleCat.restrictScalars φ.op).map g' ≫
    (ModuleCat.restrictScalarsComp' φ.op φ'.op (φ'.comp φ).op
      (by ext rGlobal; rfl)).inv.app A''

/-- For projective resolutions P,Q,T and chain comparisons
P→Res_φ(Q), Q→Res_(φ′)(T), the two tensor ring-change
chain maps compose to the tensor map for the composed
comparison. Coefficients f,f′ compose in the same order,
and source/output restrictions use their canonical comparisons. -/
theorem tensorRingChangeResolutionMap_comp
    {B : coefficientCategory.{rGlobal, sGlobal, v} R S}
    {B' : coefficientCategory.{rGlobal', sGlobal', v} R' S'}
    {B'' : coefficientCategory.{rGlobal'', sGlobal'', v} R'' S''}
    (f : B ⟶ (RingChange.restrictFunctor φ ψ).obj B')
    (f' : B' ⟶ (RingChange.restrictFunctor φ' ψ').obj B'')
    {A : ModuleCat.{v} Rᵐᵒᵖ} {A' : ModuleCat.{v} R'ᵐᵒᵖ}
    {A'' : ModuleCat.{v} R''ᵐᵒᵖ}
    (P : ProjectiveResolution A) (Q : ProjectiveResolution A') (T : ProjectiveResolution A'')
    (aGlobal : P.complex ⟶
      ((ModuleCat.restrictScalars φ.op).mapHomologicalComplex (ComplexShape.down ℕ)).obj
        Q.complex)
    (aGlobal' : Q.complex ⟶
      ((ModuleCat.restrictScalars φ'.op).mapHomologicalComplex (ComplexShape.down ℕ)).obj
        T.complex) :
    let eR := ModuleCat.restrictScalarsComp' φ.op φ'.op (φ'.comp φ).op (by ext rGlobal; rfl)
    let eS := ModuleCat.restrictScalarsComp' ψ.op ψ'.op (ψ'.comp ψ).op (by ext sGlobal; rfl)
    let c := aGlobal ≫ ((ModuleCat.restrictScalars φ.op).mapHomologicalComplex
        (ComplexShape.down ℕ)).map aGlobal' ≫
      (Functor.mapHomologicalComplexCompIso
        (F := ModuleCat.restrictScalars φ'.op) (G := ModuleCat.restrictScalars φ.op)
        eR.symm (ComplexShape.down ℕ)).hom.app T.complex
    tensorRingChangeResolutionMap R S φ ψ B B' f P Q aGlobal ≫
        ((ModuleCat.restrictScalars ψ.op).mapHomologicalComplex (ComplexShape.down ℕ)).map
          (tensorRingChangeResolutionMap R' S' φ' ψ' B' B'' f' Q T aGlobal') ≫
        (Functor.mapHomologicalComplexCompIso
          (F := ModuleCat.restrictScalars ψ'.op) (G := ModuleCat.restrictScalars ψ.op)
          eS.symm (ComplexShape.down ℕ)).hom.app
            ((((coefficientTensorObj R'' S'' B'').obj).mapHomologicalComplex
              (ComplexShape.down ℕ)).obj T.complex) =
      tensorRingChangeResolutionMap R S (φ'.comp φ) (ψ'.comp ψ) B B''
        (compositeCoefficientRingChange R S φ ψ φ' ψ' f f') P T c := by
  dsimp only
  apply HomologicalComplex.hom_ext
  intro i
  apply hom_ext R S B (P.complex.X i)
  intro x y
  rfl

section Derived

variable [HasProjectiveResolutions (ModuleCat.{v} Rᵐᵒᵖ)]
  [HasProjectiveResolutions (ModuleCat.{v} R'ᵐᵒᵖ)]
  [HasProjectiveResolutions (ModuleCat.{v} R''ᵐᵒᵖ)]

/-- For the three endpoint ring pairs and their compatible
coefficient/input maps, assume projective resolutions in
each common-world right-module source category.
The Tor change R→R′ followed by restricted Tor change R′→R″,
and the output restriction-composition comparison, equals
Tor change for φ′φ,ψ′ψ and the composed maps. -/
theorem torRingChangeMap_comp
    {B : coefficientCategory.{rGlobal, sGlobal, v} R S}
    {B' : coefficientCategory.{rGlobal', sGlobal', v} R' S'}
    {B'' : coefficientCategory.{rGlobal'', sGlobal'', v} R'' S''}
    (f : B ⟶ (RingChange.restrictFunctor φ ψ).obj B')
    (f' : B' ⟶ (RingChange.restrictFunctor φ' ψ').obj B'')
    {A : ModuleCat.{v} Rᵐᵒᵖ} {A' : ModuleCat.{v} R'ᵐᵒᵖ}
    {A'' : ModuleCat.{v} R''ᵐᵒᵖ}
    (g : A ⟶ (ModuleCat.restrictScalars φ.op).obj A')
    (g' : A' ⟶ (ModuleCat.restrictScalars φ'.op).obj A'') (n : ℕ) :
    torRingChangeMap R S φ ψ B B' f n g ≫
        (ModuleCat.restrictScalars ψ.op).map
          (torRingChangeMap R' S' φ' ψ' B' B'' f' n g') ≫
        (ModuleCat.restrictScalarsComp' ψ.op ψ'.op (ψ'.comp ψ).op
          (by ext sGlobal; rfl)).inv.app (((coefficientTorFunctor R'' S'' n).obj B'').obj A'') =
      torRingChangeMap R S (φ'.comp φ) (ψ'.comp ψ) B B''
        (compositeCoefficientRingChange R S φ ψ φ' ψ' f f') n
        (compositeInputRingChange R φ φ' g g') := by
  let U := ModuleCat.restrictScalars.{v} φ.op
  let U' := ModuleCat.restrictScalars.{v} φ'.op
  let Uc := ModuleCat.restrictScalars.{v} (φ'.comp φ).op
  let V := ModuleCat.restrictScalars.{v} ψ.op
  let V' := ModuleCat.restrictScalars.{v} ψ'.op
  let Vc := ModuleCat.restrictScalars.{v} (ψ'.comp ψ).op
  letI : U.PreservesHomology := Functor.preservesHomologyOfExact U
  letI : U'.PreservesHomology := Functor.preservesHomologyOfExact U'
  letI : Uc.PreservesHomology := Functor.preservesHomologyOfExact Uc
  letI : V.PreservesHomology := Functor.preservesHomologyOfExact V
  letI : V'.PreservesHomology := Functor.preservesHomologyOfExact V'
  letI : Vc.PreservesHomology := Functor.preservesHomologyOfExact Vc
  let eR := ModuleCat.restrictScalarsComp' φ.op φ'.op (φ'.comp φ).op (by ext rGlobal; rfl)
  let eS := ModuleCat.restrictScalarsComp' ψ.op ψ'.op (ψ'.comp ψ).op (by ext sGlobal; rfl)
  let F := (coefficientTensorObj R S B).obj
  let G := (coefficientTensorObj R' S' B').obj
  let H := (coefficientTensorObj R'' S'' B'').obj
  let α := tensorRingChangeTransformation R S φ ψ B B' f
  let β := tensorRingChangeTransformation R' S' φ' ψ' B' B'' f'
  let α₀ := tensorRingChangeTransformation R S (φ'.comp φ) (ψ'.comp ψ) B B''
    (compositeCoefficientRingChange R S φ ψ φ' ψ' f f')
  have hα : Functor.composeLeftDerivedSquare U U' Uc eR.symm V V' Vc eS.symm F G H α β = α₀ := by
    apply NatTrans.ext
    funext Z
    apply hom_ext R S B (Uc.obj Z)
    intro x y
    rfl
  have h := Functor.leftDerivedSquareHom_comp_with_input
    U U' Uc eR.symm V V' Vc eS.symm F G H α β g g' n
  rw [hα] at h
  exact h

end Derived

section RawComposition

/-- For coefficient maps f:B→B′ and f′:B′→B″ semilinear
over the two enveloping ring maps, f′∘f is semilinear
over the enveloping map of φ′φ and ψ′ψ.
All three coefficient carrier worlds may be independent. -/
def composeCoefficientSemilinear
    (B : coefficientCategory.{rGlobal, sGlobal, bGlobal} R S)
    (B' : coefficientCategory.{rGlobal', sGlobal', bGlobal'} R' S')
    (B'' : coefficientCategory.{rGlobal'', sGlobal'', bGlobal''} R'' S'')
    (f : B →ₛₗ[RingChange.envelopingRingHom φ ψ] B')
    (f' : B' →ₛₗ[RingChange.envelopingRingHom φ' ψ'] B'') :
    B →ₛₗ[RingChange.envelopingRingHom (φ'.comp φ) (ψ'.comp ψ)] B'' := by
  letI : RingHomCompTriple (RingChange.envelopingRingHom φ ψ)
      (RingChange.envelopingRingHom φ' ψ')
      (RingChange.envelopingRingHom (φ'.comp φ) (ψ'.comp ψ)) :=
    ⟨RingChange.envelopingRingHom_comp φ ψ φ' ψ'⟩
  exact f'.comp f

/-- For g:A→A′ semilinear over φᵒᵖ and g′:A′→A″
semilinear over φ′ᵒᵖ, their composite is semilinear over
(φ′φ)ᵒᵖ. The three source carrier worlds are independent. -/
def composeInputSemilinear
    (A : ModuleCat.{aGlobal} Rᵐᵒᵖ) (A' : ModuleCat.{aGlobal'} R'ᵐᵒᵖ) (A'' : ModuleCat.{aGlobal''} R''ᵐᵒᵖ)
    (g : A →ₛₗ[φ.op] A') (g' : A' →ₛₗ[φ'.op] A'') : A →ₛₗ[(φ'.comp φ).op] A'' := by
  letI : RingHomCompTriple φ.op φ'.op (φ'.comp φ).op := ⟨by ext rGlobal; rfl⟩
  exact g'.comp g

/-- For three endpoint ring pairs, compatible semilinear
coefficient maps f,f′ and source maps g,g′, all Tor changes
are compared in Γ=max(r,r′,r″,a,a′,a″,b,b′,b″,z).
The first change followed by the restricted second change
and the canonical output-restriction comparison equals
the change for their composites, in every degree n≥0. -/
theorem torRingChangeMapAt_comp.{z, r, r', r'', s, s', s'', a, a', a'', b, b', b''} (R : Type r) (S : Type s)
  [Ring R] [Ring S]
    {R' : Type r'} {R'' : Type r''} {S' : Type s'} {S'' : Type s''}
    [Ring R'] [Ring R''] [Ring S'] [Ring S'']
    (φ : R →+* R') (ψ : S →+* S') (φ' : R' →+* R'') (ψ' : S' →+* S'')
    (B : coefficientCategory.{r, s, b} R S)
    (B' : coefficientCategory.{r', s', b'} R' S')
    (B'' : coefficientCategory.{r'', s'', b''} R'' S'')
    (f : B →ₛₗ[RingChange.envelopingRingHom φ ψ] B')
    (f' : B' →ₛₗ[RingChange.envelopingRingHom φ' ψ'] B'')
    (A : ModuleCat.{a} Rᵐᵒᵖ) (A' : ModuleCat.{a'} R'ᵐᵒᵖ) (A'' : ModuleCat.{a''} R''ᵐᵒᵖ)
    (g : A →ₛₗ[φ.op] A') (g' : A' →ₛₗ[φ'.op] A'') (n : ℕ) :
    torRingChangeMapAt.{max r'' a'' b'' z, r, r', s, s', a, a', b, b'}
        R S φ ψ B B' f A A' g n ≫
      (ModuleCat.restrictScalars ψ.op).map
        (torRingChangeMapAt.{max r a b z, r', r'', s', s'', a', a'', b', b''}
          R' S' φ' ψ' B' B'' f' A' A'' g' n) ≫
      (ModuleCat.restrictScalarsComp' ψ.op ψ'.op (ψ'.comp ψ).op
        (by ext s; rfl)).inv.app
          (((torCoefficientFunctorAt.{max r a b (max r' a' b' z), r'', s'', a'', b''}
            R'' S'' n).obj B'').obj A'') =
    torRingChangeMapAt.{max r' a' b' z, r, r'', s, s'', a, a'', b, b''}
      R S (φ'.comp φ) (ψ'.comp ψ) B B''
        (composeCoefficientSemilinear R S φ ψ φ' ψ' B B' B'' f f') A A''
        (composeInputSemilinear R φ φ' A A' A'' g g') n := by
  letI : HasProjectiveResolutions
      (ModuleCat.{max r r' r'' a a' a'' b b' b'' z} Rᵐᵒᵖ) := inferInstance
  letI : HasProjectiveResolutions
      (ModuleCat.{max r r' r'' a a' a'' b b' b'' z} R'ᵐᵒᵖ) := inferInstance
  letI : HasProjectiveResolutions
      (ModuleCat.{max r r' r'' a a' a'' b b' b'' z} R''ᵐᵒᵖ) := inferInstance
  let Z := (ModuleCat.uliftFunctor.{max r r' r'' a a' a'' b b' b'' z, a''} R''ᵐᵒᵖ).obj A''
  let C := (ModuleCat.uliftFunctor.{max r r' r'' a a' a'' b b' b'' z, b}
    (R ⊗[ℤ] Sᵐᵒᵖ)).obj B
  let D := (ModuleCat.uliftFunctor.{max r r' r'' a a' a'' b b' b'' z, b'}
    (R' ⊗[ℤ] S'ᵐᵒᵖ)).obj B'
  let E := (ModuleCat.uliftFunctor.{max r r' r'' a a' a'' b b' b'' z, b''}
    (R'' ⊗[ℤ] S''ᵐᵒᵖ)).obj B''
  let f₀ := liftCoefficientRingChangeAt.{max r'' a'' b'' z, r, r', s, s', a, a', b, b'}
    R S φ ψ B B' f
  let f₁ := liftCoefficientRingChangeAt.{max r a b z, r', r'', s', s'', a', a'', b', b''}
    R' S' φ' ψ' B' B'' f'
  let g₀ := liftInputRingChangeAt.{max r'' a'' b'' z, r, r', a, a', b, b'} R φ A A' g
  let g₁ := liftInputRingChangeAt.{max r a b z, r', r'', a', a'', b', b''} R' φ' A' A'' g'
  let fc := liftCoefficientRingChangeAt.{max r' a' b' z, r, r'', s, s'', a, a'', b, b''}
    R S (φ'.comp φ) (ψ'.comp ψ) B B''
      (composeCoefficientSemilinear R S φ ψ φ' ψ' B B' B'' f f')
  let gc := liftInputRingChangeAt.{max r' a' b' z, r, r'', a, a'', b, b''}
    R (φ'.comp φ) A A'' (composeInputSemilinear R φ φ' A A' A'' g g')
  have hfc : fc = compositeCoefficientRingChange R S φ ψ φ' ψ' f₀ f₁ := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    cases x
    rfl
  have hgc : gc = compositeInputRingChange R φ φ' g₀ g₁ := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    cases x
    rfl
  change torRingChangeMap R S φ ψ C D f₀ n g₀ ≫
      (ModuleCat.restrictScalars ψ.op).map (torRingChangeMap R' S' φ' ψ' D E f₁ n g₁) ≫
      (ModuleCat.restrictScalarsComp' ψ.op ψ'.op (ψ'.comp ψ).op
        (by ext s; rfl)).inv.app (((coefficientTorFunctor R'' S'' n).obj E).obj Z) =
    torRingChangeMap R S (φ'.comp φ) (ψ'.comp ψ) C E fc n gc
  rw [hfc, hgc]
  exact torRingChangeMap_comp R S φ ψ φ' ψ' f₀ f₁ g₀ g₁ n

end RawComposition

end ModuleCat.Bimodule.Tensor
