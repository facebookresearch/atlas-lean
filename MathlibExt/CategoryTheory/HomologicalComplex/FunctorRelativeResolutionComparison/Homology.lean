/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import
  MathlibExt.CategoryTheory.HomologicalComplex.FunctorRelativeResolutionComparison.Coherence
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex

/-!
# Homology maps of split relative-resolution comparisons

Let `D` be preadditive with a zero object and kernels, `C,E` preadditive,
and `U : D → C`, `T : D → E` additive. Let `α : Q → X[0]` and
`β : P → Y[0]` be chain augmentations. Assume every term of `Q` is
`U`-relative-projective, `β` has a contracting splitting after `U`, and
`U` preserves the kernel of `β₀` and every differential kernel of `P`.
Two maps `Q → P` lifting the same endpoint map `f : X → Y` are homotopic.
After applying `T`, they induce equal degree-`n` homology maps when the
homologies of `T(Q)` and `T(P)` exist. The corresponding relative-projective,
splitting, kernel-preservation and homology-existence hypotheses give
identity and composition coherence on homology.

For a homology isomorphism, both complexes augment to the same object `X`,
both have `U`-relative-projective terms and contracting splittings after `U`,
and `U` preserves both sets of augmentation and differential kernels.
The degree-`n` homologies of both `T(Q)` and `T(P)` must exist.
The comparison maps over `𝟙 X` then induce inverse homology maps.
-/

@[expose] public section
noncomputable section
open CategoryTheory CategoryTheory.Limits HomologicalComplex
universe uC vC uD vD uE vE
namespace CategoryTheory.Functor

variable {D : Type uD} [Category.{vD} D] [Preadditive D] [HasZeroObject D] [HasKernels D]
  {C : Type uC} [Category.{vC} C] [Preadditive C]
  {E : Type uE} [Category.{vE} E] [Preadditive E]
  (U : D ⥤ C) [U.Additive] (T : D ⥤ E) [T.Additive]

/-- For preadditive categories `D,E`, additive `T : D → E`, and
nonnegative chain complex `Q` in `D`, the mapped complex has terms
`T(Q_n)` and differentials `T(d_Q)`. -/
abbrev mappedResolution (Q : ChainComplex D ℕ) : ChainComplex E ℕ :=
  (T.mapHomologicalComplex (ComplexShape.down ℕ)).obj Q

/-- Let `D` be preadditive with a zero object and kernels, `C,E`
preadditive, and `U : D → C`, `T : D → E` additive. Let
`α : Q → X[0]`, `β : P → Y[0]` be chain augmentations, with
`U(P → Y[0])` contractingly split, all `Q_n` `U`-relative-projective,
and `U` preserving the kernels of `β₀` and every differential of `P`. For `f : X → Y`, applying `T`
to the relative comparison
gives a chain map `T(Q) → T(P)`. -/
def mappedRelativeComparison (Q P : ChainComplex D ℕ) (X Y : D)
    (α : Q ⟶ (ChainComplex.single₀ D).obj X) (β : P ⟶ (ChainComplex.single₀ D).obj Y)
    (σP : AugmentationSplit U P Y β) (hQ : ∀ n, U.IsRelativeProjective (Q.X n))
    [PreservesLimit (parallelPair (β.f 0) 0) U]
    (kP : ∀ n, PreservesLimit (parallelPair (P.d (n + 1) n) 0) U) (f : X ⟶ Y) :
    mappedResolution T Q ⟶ mappedResolution T P :=
  (T.mapHomologicalComplex (ComplexShape.down ℕ)).map
    (comparison U Q P X Y α β σP hQ kP f)

/-- Let `D` be preadditive with a zero object and kernels, `C,E`
preadditive, and `U : D → C`, `T : D → E` additive. Let
`α : Q → X[0]`, `β : P → Y[0]` be chain augmentations, with
`U(P → Y[0])` contractingly split, all `Q_n` `U`-relative-projective,
and `U` preserving the kernels of `β₀` and every differential of `P`. Suppose the degree-`n`
homologies of `T(Q),T(P)` exist. For `f : X → Y`, the mapped relative comparison induces
`H_n(T(Q)) → H_n(T(P))`. -/
def comparisonHomologyMap (Q P : ChainComplex D ℕ) (X Y : D)
    (α : Q ⟶ (ChainComplex.single₀ D).obj X) (β : P ⟶ (ChainComplex.single₀ D).obj Y)
    (σP : AugmentationSplit U P Y β) (hQ : ∀ n, U.IsRelativeProjective (Q.X n))
    [PreservesLimit (parallelPair (β.f 0) 0) U]
    (kP : ∀ n, PreservesLimit (parallelPair (P.d (n + 1) n) 0) U) (f : X ⟶ Y) (n : ℕ)
    [(mappedResolution T Q).HasHomology n] [(mappedResolution T P).HasHomology n] :
    (mappedResolution T Q).homology n ⟶ (mappedResolution T P).homology n :=
  homologyMap (mappedRelativeComparison U T Q P X Y α β σP hQ kP f) n

/-- Let `D` be preadditive with a zero object and kernels, `C,E`
preadditive, and `U : D → C`, `T : D → E` additive. Let
`α : Q → X[0]`, `β : P → Y[0]` be chain augmentations, with
`U(P → Y[0])` contractingly split, all `Q_n` `U`-relative-projective,
and `U` preserving the kernels of `β₀` and every differential of `P`. Suppose the degree-`n`
homologies of `T(Q),T(P)` exist. Any two chain maps `g,h : Q → P` over the same `f : X → Y`
induce equal maps on degree-`n` homology after `T`. -/
theorem mappedHomologyMap_independent (Q P : ChainComplex D ℕ) (X Y : D)
    (α : Q ⟶ (ChainComplex.single₀ D).obj X) (β : P ⟶ (ChainComplex.single₀ D).obj Y)
    (σP : AugmentationSplit U P Y β) (hQ : ∀ n, U.IsRelativeProjective (Q.X n))
    [PreservesLimit (parallelPair (β.f 0) 0) U]
    (kP : ∀ n, PreservesLimit (parallelPair (P.d (n + 1) n) 0) U)
    (f : X ⟶ Y) (g h : Q ⟶ P)
    (hg : g ≫ β = α ≫ (ChainComplex.single₀ D).map f)
    (hh : h ≫ β = α ≫ (ChainComplex.single₀ D).map f) (n : ℕ)
    [(mappedResolution T Q).HasHomology n] [(mappedResolution T P).HasHomology n] :
    homologyMap ((T.mapHomologicalComplex (ComplexShape.down ℕ)).map g) n =
      homologyMap ((T.mapHomologicalComplex (ComplexShape.down ℕ)).map h) n :=
  (T.mapHomotopy (comparisonHomotopy U Q P X Y α β σP hQ kP f g h hg hh)).homologyMap_eq n

/-- Let `D` be preadditive with a zero object and kernels, `C,E`
preadditive, and `U : D → C`, `T : D → E` additive. Let
`α : Q → X[0]`, `β : P → Y[0]` be chain augmentations, with
`U(P → Y[0])` contractingly split, all `Q_n` `U`-relative-projective,
and `U` preserving the kernels of `β₀` and every differential of `P`. Suppose the degree-`n`
homologies of `T(Q),T(P)` exist. Any chain map `g : Q → P` over `f : X → Y` computes the
canonical comparison homology map as `H_n(T(g))`. -/
theorem comparisonHomologyMap_eq_of_augmentation (Q P : ChainComplex D ℕ) (X Y : D)
    (α : Q ⟶ (ChainComplex.single₀ D).obj X) (β : P ⟶ (ChainComplex.single₀ D).obj Y)
    (σP : AugmentationSplit U P Y β) (hQ : ∀ n, U.IsRelativeProjective (Q.X n))
    [PreservesLimit (parallelPair (β.f 0) 0) U]
    (kP : ∀ n, PreservesLimit (parallelPair (P.d (n + 1) n) 0) U)
    (f : X ⟶ Y) (g : Q ⟶ P) (hg : g ≫ β = α ≫ (ChainComplex.single₀ D).map f) (n : ℕ)
    [(mappedResolution T Q).HasHomology n] [(mappedResolution T P).HasHomology n] :
    comparisonHomologyMap U T Q P X Y α β σP hQ kP f n =
      homologyMap ((T.mapHomologicalComplex (ComplexShape.down ℕ)).map g) n :=
  mappedHomologyMap_independent U T Q P X Y α β σP hQ kP f _ g
    (comparison_augmentation U Q P X Y α β σP hQ kP f) hg n

/-- Let `D` be preadditive with a zero object and kernels, `C,E`
preadditive, and `U : D → C`, `T : D → E` additive. For a
`U`-split augmentation `Q → X[0]` with relative-projective terms
and preservation by `U` of its augmentation and differential kernels,
the comparison over `𝟙 X` induces the identity on each existing
`H_n(T(Q))`. -/
theorem comparisonHomologyMap_id (Q : ChainComplex D ℕ) (X : D)
    (α : Q ⟶ (ChainComplex.single₀ D).obj X) (σQ : AugmentationSplit U Q X α)
    (hQ : ∀ n, U.IsRelativeProjective (Q.X n))
    [PreservesLimit (parallelPair (α.f 0) 0) U]
    (kQ : ∀ n, PreservesLimit (parallelPair (Q.d (n + 1) n) 0) U) (n : ℕ)
    [(mappedResolution T Q).HasHomology n] :
    comparisonHomologyMap U T Q Q X X α α σQ hQ kQ (𝟙 X) n = 𝟙 _ := by
  have h := (T.mapHomotopy (comparisonIdHomotopy U Q X α σQ hQ kQ)).homologyMap_eq n
  dsimp only [comparisonHomologyMap, mappedRelativeComparison]
  simpa only [Functor.map_id, homologyMap_id] using h

/-- Let `D` be preadditive with a zero object and kernels, `C`
preadditive, and `U : D → C` additive. Let `Q → X[0]`, `P → Y[0]`, `R → Z[0]` be chain
augmentations,
with the augmentations of `P,R` contractingly split after `U`,
all terms of `Q,P` `U`-relative-projective, and `U` preserving the
augmentation and differential kernels of `P,R`. For additive `T : D → E` with `E` preadditive and
existing
`H_n(T(Q)),H_n(T(P)),H_n(T(R))`, comparison over `f ≫ g` is the
composite of comparison over `f : X → Y` and over `g : Y → Z`. -/
theorem comparisonHomologyMap_comp (Q P R : ChainComplex D ℕ) (X Y Z : D)
    (α : Q ⟶ (ChainComplex.single₀ D).obj X) (β : P ⟶ (ChainComplex.single₀ D).obj Y)
    (γ : R ⟶ (ChainComplex.single₀ D).obj Z)
    (σP : AugmentationSplit U P Y β) (σR : AugmentationSplit U R Z γ)
    (hQ : ∀ n, U.IsRelativeProjective (Q.X n)) (hP : ∀ n, U.IsRelativeProjective (P.X n))
    [PreservesLimit (parallelPair (β.f 0) 0) U] [PreservesLimit (parallelPair (γ.f 0) 0) U]
    (kP : ∀ n, PreservesLimit (parallelPair (P.d (n + 1) n) 0) U)
    (kR : ∀ n, PreservesLimit (parallelPair (R.d (n + 1) n) 0) U)
    (f : X ⟶ Y) (g : Y ⟶ Z) (n : ℕ)
    [(mappedResolution T Q).HasHomology n] [(mappedResolution T P).HasHomology n]
    [(mappedResolution T R).HasHomology n] :
    comparisonHomologyMap U T Q R X Z α γ σR hQ kR (f ≫ g) n =
      comparisonHomologyMap U T Q P X Y α β σP hQ kP f n ≫
        comparisonHomologyMap U T P R Y Z β γ σR hP kR g n := by
  have h := (T.mapHomotopy
    (comparisonCompHomotopy U Q P R X Y Z α β γ σP σR hQ hP kP kR f g)).homologyMap_eq n
  dsimp only [comparisonHomologyMap, mappedRelativeComparison]
  simpa only [Functor.map_comp, homologyMap_comp] using h

/-- Let `D` be preadditive with a zero object and kernels, `C,E`
preadditive, and `U : D → C`, `T : D → E` additive. Let
`Q → X[0]`, `P → X[0]` have contracting splittings after `U`,
with all terms `U`-relative-projective, and `U` preserving each
augmentation kernel and differential kernel of both complexes.
Suppose the degree-`n` homologies of `T(Q),T(P)` exist. The inverse comparisons over `𝟙 X` give a
canonical
isomorphism `H_n(T(Q)) ≅ H_n(T(P))`. -/
def comparisonHomologyIso (Q P : ChainComplex D ℕ) (X : D)
    (α : Q ⟶ (ChainComplex.single₀ D).obj X) (β : P ⟶ (ChainComplex.single₀ D).obj X)
    (σQ : AugmentationSplit U Q X α) (σP : AugmentationSplit U P X β)
    (hQ : ∀ n, U.IsRelativeProjective (Q.X n)) (hP : ∀ n, U.IsRelativeProjective (P.X n))
    [PreservesLimit (parallelPair (α.f 0) 0) U] [PreservesLimit (parallelPair (β.f 0) 0) U]
    (kQ : ∀ n, PreservesLimit (parallelPair (Q.d (n + 1) n) 0) U)
    (kP : ∀ n, PreservesLimit (parallelPair (P.d (n + 1) n) 0) U) (n : ℕ)
    [(mappedResolution T Q).HasHomology n] [(mappedResolution T P).HasHomology n] :
    (mappedResolution T Q).homology n ≅ (mappedResolution T P).homology n :=
  (T.mapHomotopyEquiv (comparisonHomotopyEquiv U Q P X α β σQ σP hQ hP kQ kP)).toHomologyIso n

/-- Let `D` be preadditive with a zero object and kernels, `C,E`
preadditive, and `U : D → C`, `T : D → E` additive. Let
`Q → X[0]`, `P → X[0]` have contracting splittings after `U`,
with all terms `U`-relative-projective, and `U` preserving each
augmentation kernel and differential kernel of both complexes.
Suppose the degree-`n` homologies of `T(Q),T(P)` exist. The forward map of the canonical homology
isomorphism
is the comparison homology map from `Q` to `P` over `𝟙 X`. -/
theorem comparisonHomologyIso_hom (Q P : ChainComplex D ℕ) (X : D)
    (α : Q ⟶ (ChainComplex.single₀ D).obj X) (β : P ⟶ (ChainComplex.single₀ D).obj X)
    (σQ : AugmentationSplit U Q X α) (σP : AugmentationSplit U P X β)
    (hQ : ∀ n, U.IsRelativeProjective (Q.X n)) (hP : ∀ n, U.IsRelativeProjective (P.X n))
    [PreservesLimit (parallelPair (α.f 0) 0) U] [PreservesLimit (parallelPair (β.f 0) 0) U]
    (kQ : ∀ n, PreservesLimit (parallelPair (Q.d (n + 1) n) 0) U)
    (kP : ∀ n, PreservesLimit (parallelPair (P.d (n + 1) n) 0) U) (n : ℕ)
    [(mappedResolution T Q).HasHomology n] [(mappedResolution T P).HasHomology n] :
    (comparisonHomologyIso U T Q P X α β σQ σP hQ hP kQ kP n).hom =
      comparisonHomologyMap U T Q P X X α β σP hQ kP (𝟙 X) n := rfl

/-- Let `D` be preadditive with a zero object and kernels, `C,E`
preadditive, and `U : D → C`, `T : D → E` additive. Let
`α : Q → X[0]`, `β : P → Y[0]` be chain augmentations, with
`U(P → Y[0])` contractingly split, all `Q_n` `U`-relative-projective,
and `U` preserving the kernels of `β₀` and every differential of `P`. For `f : X → Y`, the mapped
chain comparison satisfies
`T(comparison_f) ≫ T(β) = T(α) ≫ T(f[0])`. -/
theorem mappedRelativeComparison_augmentation (Q P : ChainComplex D ℕ) (X Y : D)
    (α : Q ⟶ (ChainComplex.single₀ D).obj X) (β : P ⟶ (ChainComplex.single₀ D).obj Y)
    (σP : AugmentationSplit U P Y β) (hQ : ∀ n, U.IsRelativeProjective (Q.X n))
    [PreservesLimit (parallelPair (β.f 0) 0) U]
    (kP : ∀ n, PreservesLimit (parallelPair (P.d (n + 1) n) 0) U) (f : X ⟶ Y) :
    mappedRelativeComparison U T Q P X Y α β σP hQ kP f ≫
        (T.mapHomologicalComplex (ComplexShape.down ℕ)).map β =
      (T.mapHomologicalComplex (ComplexShape.down ℕ)).map α ≫
        (T.mapHomologicalComplex (ComplexShape.down ℕ)).map ((ChainComplex.single₀ D).map f) := by
  have h := congrArg ((T.mapHomologicalComplex (ComplexShape.down ℕ)).map)
    (comparison_augmentation U Q P X Y α β σP hQ kP f)
  dsimp only [mappedRelativeComparison]
  simpa only [Functor.map_comp] using h

/-- Let `D` be preadditive with a zero object and kernels, `C,E`
preadditive, and `U : D → C`, `T : D → E` additive. Let
`α : Q → X[0]`, `β : P → Y[0]` be chain augmentations, with
`U(P → Y[0])` contractingly split, all `Q_n` `U`-relative-projective,
and `U` preserving the kernels of `β₀` and every differential of `P`. Suppose the degree-`n`
homologies of `T(Q),T(P)` exist. Suppose also the degree-`n` homologies of `T(X[0]),T(Y[0])`
exist. The comparison homology map satisfies
`H_n(T(comparison_f)) ≫ H_n(T(β)) = H_n(T(α)) ≫ H_n(T(f[0]))`. -/
theorem comparisonHomologyMap_augmentation (Q P : ChainComplex D ℕ) (X Y : D)
    (α : Q ⟶ (ChainComplex.single₀ D).obj X) (β : P ⟶ (ChainComplex.single₀ D).obj Y)
    (σP : AugmentationSplit U P Y β) (hQ : ∀ n, U.IsRelativeProjective (Q.X n))
    [PreservesLimit (parallelPair (β.f 0) 0) U]
    (kP : ∀ n, PreservesLimit (parallelPair (P.d (n + 1) n) 0) U) (f : X ⟶ Y) (n : ℕ)
    [(mappedResolution T Q).HasHomology n] [(mappedResolution T P).HasHomology n]
    [(mappedResolution T ((ChainComplex.single₀ D).obj X)).HasHomology n]
    [(mappedResolution T ((ChainComplex.single₀ D).obj Y)).HasHomology n] :
    comparisonHomologyMap U T Q P X Y α β σP hQ kP f n ≫
        homologyMap ((T.mapHomologicalComplex (ComplexShape.down ℕ)).map β) n =
      homologyMap ((T.mapHomologicalComplex (ComplexShape.down ℕ)).map α) n ≫
        homologyMap ((T.mapHomologicalComplex (ComplexShape.down ℕ)).map
          ((ChainComplex.single₀ D).map f)) n := by
  have h := congrArg (fun z => homologyMap z n)
    (mappedRelativeComparison_augmentation U T Q P X Y α β σP hQ kP f)
  dsimp only [comparisonHomologyMap]
  simpa only [homologyMap_comp] using h

omit [HasKernels D] in
/-- Let `D` be preadditive with a zero object, `E` preadditive,
`T : D → E` additive, and `α : Q → X[0]` a chain augmentation.
The degree-zero component of its mapped chain map is `T(α₀)`. -/
theorem mappedAugmentation_f_zero (Q : ChainComplex D ℕ) (X : D)
    (α : Q ⟶ (ChainComplex.single₀ D).obj X) :
    ((T.mapHomologicalComplex (ComplexShape.down ℕ)).map α).f 0 = T.map (α.f 0) := rfl

end CategoryTheory.Functor
