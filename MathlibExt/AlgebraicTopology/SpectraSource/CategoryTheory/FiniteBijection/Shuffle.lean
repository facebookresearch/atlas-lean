/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

/-
Completed Apache source port from TauCeti, commit 62bbc0596dc3539d488232e4e924a338548ea0a9.
Original copyright and authors are retained; module/namespace paths are adapted for Atlas.
Source: https://github.com/TauCetiProject/TauCeti/blob/62bbc0596dc3539d488232e4e924a338548ea0a9/TauCeti/CategoryTheory/FiniteBijection/Shuffle.lean
License: https://github.com/TauCetiProject/TauCeti/blob/62bbc0596dc3539d488232e4e924a338548ea0a9/LICENSE
-/

public import Mathlib.CategoryTheory.Functor.KanExtension.Pointwise
public import Mathlib.CategoryTheory.Limits.Final
public import Mathlib.CategoryTheory.Monoidal.DayConvolution.DayFunctor
public import Mathlib.Data.Fintype.Sort
public import MathlibExt.AlgebraicTopology.SpectraSource.CategoryTheory.FiniteBijection

/-!
# Shuffles and the wedge formula for left Kan extensions along the block sum

A subset `S` of `Fin n` determines the *shuffle* `FiniteBijection.shuffle S : mk #S ⊗ mk #Sᶜ ⟶ n`,
which enumerates `S` on the first block and its complement on the second block, both in
increasing order. Every bijection `σ : p ⊗ q ⟶ n` factors uniquely as a pair of block
bijections followed by the shuffle of the image `blockImage σ` of the first block:
`(blockLeft σ ⊗ₘ blockRight σ) ≫ shuffle (blockImage σ) = σ`. Equivalently, the comma category
`CostructuredArrow (tensor FiniteBijection) n` is equivalent to the discrete category on the
subsets of `Fin n` (`shuffleFunctor n`).

Consequently, a pointwise left Kan extension `L` of a functor `H` along the block sum has levels
`L(n) = ∐_{S ⊆ Fin n} H(#S, #Sᶜ)`, with the summand of `S` included along the shuffle of `S`
(`IsPointwiseLeftKanExtensionAt.isColimitShuffleCofan`). For Day convolution of symmetric
sequences this is the wedge formula of Hovey, Shipley and Smith,
`(X ⊗ Y)_n = ⋁_{p+q=n} (Σ_n)₊ ∧_{Σ_p × Σ_q} (X_p ∧ Y_q)`:
the subsets of `Fin n` with `p` elements are the cosets `Σ_n / (Σ_p × Σ_q)`, and the shuffles
are the standard coset representatives. The action of a bijection `τ : n ⟶ m` carries the
summand of `S` to the summand of `S.map τ`, through the block bijections of `shuffle S ≫ τ`
(`hom_app_comp_map_eq_map_comp_shuffleCofan_inj`,
`DayFunctor.η_app_comp_map_eq_tensorHom_comp_shuffleCofan_inj`, `blockImage_shuffle_comp`).

## Main definitions

* `FiniteBijection.shuffle S`: the shuffle of a subset `S` of `Fin n`.
* `FiniteBijection.blockImage σ`, `FiniteBijection.blockLeft σ`, `FiniteBijection.blockRight σ`:
  the shuffle factorization of a bijection `σ : p ⊗ q ⟶ n`.
* `FiniteBijection.shuffleFunctor n`: the equivalence from the discrete category on the subsets
  of `Fin n` to `CostructuredArrow (tensor FiniteBijection) n`.
* `Functor.LeftExtension.shuffleCofan E n`: the cofan of the shuffle summands of a left extension
  along the block sum, and `DayFunctor.shuffleCofan F G n`, its specialization to Day convolution.

## Main statements

* `FiniteBijection.blockLeft_tensorHom_blockRight_comp_shuffle`: the shuffle factorization.
* `Functor.LeftExtension.IsPointwiseLeftKanExtensionAt.isColimitShuffleCofan`: the levels of a
  pointwise left Kan extension along the block sum are the coproducts of the shuffle summands.
* `DayFunctor.isColimitShuffleCofan`: the wedge formula for Day convolution of functors out of
  `FiniteBijection`.

## References

* M. Hovey, B. Shipley and J. Smith, *Symmetric spectra*, J. Amer. Math. Soc. 13 (2000),
  Section 2.1.
* S. Schwede, *Symmetric spectra*, book project, Chapter I.
-/

public section

universe v u

open CategoryTheory MonoidalCategory Limits Finset

namespace MathlibExt.SpectraSource

namespace FiniteBijection

variable {n m p q : FiniteBijection}

/-! ### Shuffles -/

/-- The shuffle of a subset `S` of `Fin n`: the bijection `mk #S ⊗ mk #Sᶜ ⟶ n` enumerating `S`
on the first block and `Sᶜ` on the second block, both in increasing order. -/
def shuffle (S : Finset (Fin n.len)) : mk #S ⊗ mk #Sᶜ ⟶ n :=
  ⟨finSumFinEquiv.symm.trans (finSumEquivOfFinset rfl rfl)⟩

@[simp]
lemma toEquiv_shuffle_castAdd (S : Finset (Fin n.len)) (i : Fin #S) :
    (shuffle S).toEquiv (Fin.castAdd #Sᶜ i) = S.orderEmbOfFin rfl i := by
  simp [shuffle, finSumFinEquiv_symm_apply_castAdd i]

@[simp]
lemma toEquiv_shuffle_natAdd (S : Finset (Fin n.len)) (i : Fin #Sᶜ) :
    (shuffle S).toEquiv (Fin.natAdd #S i) = Sᶜ.orderEmbOfFin rfl i := by
  simp [shuffle, finSumFinEquiv_symm_apply_natAdd i]

/-! ### The shuffle factorization -/

/-- The image of the first block under a bijection `σ : p ⊗ q ⟶ n`. -/
def blockImage (σ : p ⊗ q ⟶ n) : Finset (Fin n.len) :=
  univ.map ⟨fun i ↦ σ.toEquiv (Fin.castAdd q.len i),
    σ.toEquiv.injective.comp (Fin.castAdd_injective _ _)⟩

@[simp]
lemma mem_blockImage {σ : p ⊗ q ⟶ n} {x : Fin n.len} :
    x ∈ blockImage σ ↔ ∃ i, σ.toEquiv (Fin.castAdd q.len i) = x := by
  simp [blockImage]

/-- A point lies outside the image of the first block exactly when it is the image of a point of
the second block. -/
lemma notMem_blockImage {σ : p ⊗ q ⟶ n} {x : Fin n.len} :
    x ∉ blockImage σ ↔ ∃ j, σ.toEquiv (Fin.natAdd p.len j) = x := by
  obtain ⟨y, rfl⟩ := σ.toEquiv.surjective x
  simp only [mem_blockImage, σ.toEquiv.injective.eq_iff]
  induction y using Fin.addCases with
  | left i =>
    refine iff_of_false (fun h ↦ h ⟨i, rfl⟩) fun ⟨j, hj⟩ ↦ ?_
    have := congrArg Fin.val hj
    simp only [Fin.val_natAdd, Fin.val_castAdd] at this
    omega
  | right j =>
    refine iff_of_true (fun ⟨i, hi⟩ ↦ ?_) ⟨j, rfl⟩
    have := congrArg Fin.val hi
    simp only [Fin.val_natAdd, Fin.val_castAdd] at this
    omega

@[simp]
lemma card_blockImage (σ : p ⊗ q ⟶ n) : #(blockImage σ) = p.len := by
  simp [blockImage]

@[simp]
lemma card_compl_blockImage (σ : p ⊗ q ⟶ n) : #(blockImage σ)ᶜ = q.len := by
  have : p.len + q.len = n.len := congrArg len (eq_of_hom σ)
  simp [card_compl]
  omega

/-- The first factor of the shuffle factorization of `σ : p ⊗ q ⟶ n`: the bijection from the first
block onto the enumeration of its image. -/
noncomputable def blockLeft (σ : p ⊗ q ⟶ n) : p ⟶ mk #(blockImage σ) :=
  ⟨Equiv.ofBijective
    (fun i ↦ ((blockImage σ).orderIsoOfFin rfl).symm ⟨_, mem_blockImage.2 ⟨i, rfl⟩⟩)
    ((Fintype.bijective_iff_injective_and_card _).2
      ⟨fun _ _ h ↦ Fin.castAdd_injective _ _ <| σ.toEquiv.injective <|
        congrArg Subtype.val (((blockImage σ).orderIsoOfFin rfl).symm.injective h),
        by simp⟩)⟩

/-- The second factor of the shuffle factorization of `σ : p ⊗ q ⟶ n`: the bijection from the
second block onto the enumeration of the complement of the image of the first block. -/
noncomputable def blockRight (σ : p ⊗ q ⟶ n) : q ⟶ mk #(blockImage σ)ᶜ :=
  ⟨Equiv.ofBijective
    (fun j ↦ ((blockImage σ)ᶜ.orderIsoOfFin rfl).symm
      ⟨_, mem_compl.2 (notMem_blockImage.2 ⟨j, rfl⟩)⟩)
    ((Fintype.bijective_iff_injective_and_card _).2
      ⟨fun _ _ h ↦ Fin.natAdd_injective _ _ <| σ.toEquiv.injective <|
        congrArg Subtype.val (((blockImage σ)ᶜ.orderIsoOfFin rfl).symm.injective h),
        by simp⟩)⟩

@[simp]
lemma orderEmbOfFin_blockLeft (σ : p ⊗ q ⟶ n) (i : Fin p.len) :
    (blockImage σ).orderEmbOfFin rfl ((blockLeft σ).toEquiv i) =
      σ.toEquiv (Fin.castAdd q.len i) := by
  simp [blockLeft, ← coe_orderIsoOfFin_apply]

@[simp]
lemma orderEmbOfFin_blockRight (σ : p ⊗ q ⟶ n) (j : Fin q.len) :
    (blockImage σ)ᶜ.orderEmbOfFin rfl ((blockRight σ).toEquiv j) =
      σ.toEquiv (Fin.natAdd p.len j) := by
  simp [blockRight, ← coe_orderIsoOfFin_apply]

/-- **Shuffle factorization.** Every bijection `σ : p ⊗ q ⟶ n` is a pair of block bijections
followed by the shuffle of the image of the first block. -/
@[reassoc (attr := simp)]
theorem blockLeft_tensorHom_blockRight_comp_shuffle (σ : p ⊗ q ⟶ n) :
    (blockLeft σ ⊗ₘ blockRight σ) ≫ shuffle (blockImage σ) = σ := by
  refine hom_ext fun x ↦ ?_
  induction x using Fin.addCases with
  -- `simp` alone does not rewrite with `orderEmbOfFin_blockLeft` here: the cardinality in the
  -- shuffle lemmas is `#S`, while the factor lemmas carry the length of `mk #S`.
  | left i => simpa using orderEmbOfFin_blockLeft σ i
  | right j => simpa using orderEmbOfFin_blockRight σ j

@[simp]
lemma blockImage_shuffle (S : Finset (Fin n.len)) : blockImage (shuffle S) = S := by
  ext x
  rw [mem_blockImage]
  simp only [toEquiv_shuffle_castAdd]
  exact ⟨fun ⟨i, hi⟩ ↦ hi ▸ S.orderEmbOfFin_mem rfl i, fun hx ↦
    ⟨(S.orderIsoOfFin rfl).symm ⟨x, hx⟩, by simp [← coe_orderIsoOfFin_apply]⟩⟩

/-- Precomposing with a pair of block bijections does not change the image of the first block. -/
@[simp]
lemma blockImage_tensorHom_comp {p' q' : FiniteBijection} (f : p' ⟶ p) (g : q' ⟶ q)
    (σ : p ⊗ q ⟶ n) : blockImage ((f ⊗ₘ g) ≫ σ) = blockImage σ := by
  ext x
  simp only [mem_blockImage, toEquiv_comp, Equiv.trans_apply, toEquiv_tensorHom_castAdd]
  exact ⟨fun ⟨i, hi⟩ ↦ ⟨_, hi⟩, fun ⟨i, hi⟩ ↦ ⟨f.toEquiv.symm i, by simpa using hi⟩⟩

/-- Postcomposing with a bijection `τ` moves the image of the first block along `τ`. -/
lemma blockImage_comp (σ : p ⊗ q ⟶ n) (τ : n ⟶ m) :
    blockImage (σ ≫ τ) = (blockImage σ).map τ.toEquiv.toEmbedding := by
  ext x
  simp [mem_blockImage, Equiv.eq_symm_apply]

/-- The subset carried by the shuffle `shuffle S ≫ τ` is the image of `S` under `τ`. -/
@[simp]
lemma blockImage_shuffle_comp (S : Finset (Fin n.len)) (τ : n ⟶ m) :
    blockImage (shuffle S ≫ τ) = S.map τ.toEquiv.toEmbedding := by
  rw [blockImage_comp, blockImage_shuffle]

/-! ### The comma category of the block sum -/

/-- A morphism of the comma category of the block sum is determined by its source and target:
the block bijections of a factorization through a bijection are unique. -/
instance {X Y : CostructuredArrow (tensor FiniteBijection) n} : Subsingleton (X ⟶ Y) where
  allEq f g := by
    have h : f.left.1 ⊗ₘ f.left.2 = g.left.1 ⊗ₘ g.left.2 :=
      (cancel_mono Y.hom).1 ((CostructuredArrow.w f).trans (CostructuredArrow.w g).symm)
    exact CostructuredArrow.hom_ext _ _ (Prod.ext (tensorHom_inj.1 h).1 (tensorHom_inj.1 h).2)

/-- The shuffle of a subset `S` of `Fin n`, as an object of the comma category of the block sum
over `n`. -/
abbrev shuffleArrow (S : Finset (Fin n.len)) : CostructuredArrow (tensor FiniteBijection) n :=
  .mk (Y := (mk #S, mk #Sᶜ)) (shuffle S)

/-- The functor from the discrete category on the subsets of `Fin n` to the comma category of the
block sum over `n`, sending a subset to its shuffle. It is an equivalence. -/
abbrev shuffleFunctor (n : FiniteBijection) :
    Discrete (Finset (Fin n.len)) ⥤ CostructuredArrow (tensor FiniteBijection) n :=
  Discrete.functor shuffleArrow

instance : (shuffleFunctor n).Faithful where
  map_injective _ := Subsingleton.elim _ _

instance : (shuffleFunctor n).Full where
  map_surjective {S S'} f := by
    have h : S.as = S'.as := by
      simpa using congrArg blockImage (CostructuredArrow.w f).symm
    exact ⟨eqToHom (Discrete.ext h), Subsingleton.elim _ _⟩

instance : (shuffleFunctor n).EssSurj where
  -- An object `σ : p ⊗ q ⟶ n` is isomorphic to the shuffle of `blockImage σ`, through the
  -- shuffle factorization.
  mem_essImage X := ⟨⟨blockImage X.hom⟩, ⟨(CostructuredArrow.isoMk (asIso
    ((blockLeft X.hom, blockRight X.hom) :
      X.left ⟶ (mk #(blockImage X.hom), mk #(blockImage X.hom)ᶜ)))
    (blockLeft_tensorHom_blockRight_comp_shuffle X.hom)).symm⟩⟩

instance : (shuffleFunctor n).IsEquivalence where

end FiniteBijection

end MathlibExt.SpectraSource

/-! ### The wedge formula for left Kan extensions along the block sum -/

namespace CategoryTheory.Functor.LeftExtension

open MathlibExt.SpectraSource MathlibExt.SpectraSource.FiniteBijection

variable {V : Type u} [Category.{v} V] {H : FiniteBijection × FiniteBijection ⥤ V}
  {n p q : FiniteBijection}

/-- The cofan of the shuffle summands of a left extension `E` of `H` along the block sum: the
summand `H(#S, #Sᶜ)` of a subset `S` of `Fin n` maps to `E(n)` through the unit of `E` followed
by the action of the shuffle of `S`. -/
@[expose] def shuffleCofan (E : (tensor FiniteBijection).LeftExtension H) (n : FiniteBijection) :
    Cofan fun S : Finset (Fin n.len) ↦ H.obj (FiniteBijection.mk #S, FiniteBijection.mk #Sᶜ) :=
  Cofan.mk (E.right.obj n) fun S ↦
    E.hom.app (FiniteBijection.mk #S, FiniteBijection.mk #Sᶜ) ≫ E.right.map (shuffle S)

@[simp]
lemma shuffleCofan_pt (E : (tensor FiniteBijection).LeftExtension H) (n : FiniteBijection) :
    (E.shuffleCofan n).pt = E.right.obj n :=
  rfl

@[simp]
lemma shuffleCofan_inj (E : (tensor FiniteBijection).LeftExtension H) (n : FiniteBijection)
    (S : Finset (Fin n.len)) :
    (E.shuffleCofan n).inj S =
      E.hom.app (FiniteBijection.mk #S, FiniteBijection.mk #Sᶜ) ≫ E.right.map (shuffle S) :=
  rfl

/-- **The wedge formula.** If `E` is a pointwise left Kan extension of `H` along the block sum at
`n`, then `E(n)` is the coproduct over the subsets `S` of `Fin n` of `H(#S, #Sᶜ)`, with the
summand of `S` included through the shuffle of `S`. -/
noncomputable def IsPointwiseLeftKanExtensionAt.isColimitShuffleCofan
    {E : (tensor FiniteBijection).LeftExtension H} (hE : E.IsPointwiseLeftKanExtensionAt n) :
    IsColimit (E.shuffleCofan n) :=
  -- The comma category over `n` is equivalent to the discrete category on the subsets of `Fin n`.
  let hc := (Functor.Final.isColimitWhiskerEquiv (shuffleFunctor n) _).symm hE
  Cofan.IsColimit.mk _
    (fun t ↦ hc.desc (Cocone.mk t.pt (Discrete.natTrans fun S ↦ t.inj S.as)))
    (fun t S ↦ hc.fac (Cocone.mk t.pt (Discrete.natTrans fun S ↦ t.inj S.as)) ⟨S⟩)
    (fun t _ hf ↦ hc.hom_ext fun S ↦ (hf S.as).trans
      (hc.fac (Cocone.mk t.pt (Discrete.natTrans fun S ↦ t.inj S.as)) S).symm)

/-- The unit of a left extension along the block sum, followed by the action of any bijection
`σ : p ⊗ q ⟶ n`, factors through the shuffle summand of `blockImage σ`, through the block
bijections of `σ`. For `σ = shuffle S ≫ τ`, this describes the action of `τ` on the summands. -/
lemma hom_app_comp_map_eq_map_comp_shuffleCofan_inj (E : (tensor FiniteBijection).LeftExtension H)
    (σ : p ⊗ q ⟶ n) :
    E.hom.app (p, q) ≫ E.right.map σ =
      H.map ((blockLeft σ, blockRight σ) :
        (p, q) ⟶ (FiniteBijection.mk #(blockImage σ), FiniteBijection.mk #(blockImage σ)ᶜ)) ≫
        (E.shuffleCofan n).inj (blockImage σ) := by
  have := E.hom.naturality ((blockLeft σ, blockRight σ) :
    (p, q) ⟶ (FiniteBijection.mk #(blockImage σ), FiniteBijection.mk #(blockImage σ)ᶜ))
  dsimp at this
  dsimp only [shuffleCofan_inj, shuffleCofan_pt]
  rw [reassoc_of% this, ← Functor.map_comp,
    blockLeft_tensorHom_blockRight_comp_shuffle]

end CategoryTheory.Functor.LeftExtension

/-! ### The wedge formula for Day convolution -/

namespace CategoryTheory.MonoidalCategory.DayFunctor

open MathlibExt.SpectraSource MathlibExt.SpectraSource.FiniteBijection
open scoped ExternalProduct

variable {V : Type u} [Category.{v} V] [MonoidalCategory V]
    [∀ (F G : FiniteBijection ⥤ V), (tensor FiniteBijection).HasPointwiseLeftKanExtension (F ⊠ G)]
    [(Functor.fromPUnit.{0} <| 𝟙_ FiniteBijection).HasPointwiseLeftKanExtension
      (Functor.fromPUnit.{0} <| 𝟙_ V)]
    [∀ (v : V) (d : FiniteBijection), PreservesColimitsOfShape
      (CostructuredArrow (tensor FiniteBijection) d) (tensorLeft v)]
    [∀ (v : V) (d : FiniteBijection), PreservesColimitsOfShape
      (CostructuredArrow (tensor FiniteBijection) d) (tensorRight v)]
    [∀ (v : V) (d : FiniteBijection), PreservesColimitsOfShape
      (CostructuredArrow (Functor.fromPUnit.{0} <| 𝟙_ FiniteBijection) d) (tensorLeft v)]
    [∀ (v : V) (d : FiniteBijection), PreservesColimitsOfShape
      (CostructuredArrow (Functor.fromPUnit.{0} <| 𝟙_ FiniteBijection) d) (tensorRight v)]
    [∀ (v : V) (d : FiniteBijection × FiniteBijection), PreservesColimitsOfShape
      (CostructuredArrow ((𝟭 FiniteBijection).prod <| Functor.fromPUnit.{0} <|
        𝟙_ FiniteBijection) d) (tensorRight v)]
    [∀ (v : V) (d : FiniteBijection × FiniteBijection), PreservesColimitsOfShape
      (CostructuredArrow ((tensor FiniteBijection).prod (𝟭 FiniteBijection)) d) (tensorRight v)]

/-- The cofan of the shuffle summands of the Day convolution of `F` and `G` at `n`: the summand
`F(#S) ⊗ G(#Sᶜ)` of a subset `S` of `Fin n` maps to `(F ⊗ G)(n)` through the Day convolution unit
followed by the action of the shuffle of `S`. -/
@[expose] noncomputable def shuffleCofan (F G : FiniteBijection ⊛⥤ V) (n : FiniteBijection) :
    Cofan fun S : Finset (Fin n.len) ↦
      F.functor.obj (FiniteBijection.mk #S) ⊗ G.functor.obj (FiniteBijection.mk #Sᶜ) :=
  (Functor.LeftExtension.mk _ (η F G)).shuffleCofan n

@[simp]
lemma shuffleCofan_pt (F G : FiniteBijection ⊛⥤ V) (n : FiniteBijection) :
    (shuffleCofan F G n).pt = (F ⊗ G).functor.obj n :=
  rfl

@[simp]
lemma shuffleCofan_inj (F G : FiniteBijection ⊛⥤ V) (n : FiniteBijection)
    (S : Finset (Fin n.len)) :
    (shuffleCofan F G n).inj S =
      (η F G).app (FiniteBijection.mk #S, FiniteBijection.mk #Sᶜ) ≫
        (F ⊗ G).functor.map (shuffle S) :=
  rfl

/-- **The wedge formula for Day convolution.** For functors `F` and `G` out of the
finite-bijection groupoid, the level `(F ⊗ G)(n)` of their Day convolution is the coproduct over
the subsets `S` of `Fin n` of `F(#S) ⊗ G(#Sᶜ)`, with the summand of `S` included through the Day
convolution unit followed by the action of the shuffle of `S`. -/
noncomputable def isColimitShuffleCofan (F G : FiniteBijection ⊛⥤ V) (n : FiniteBijection) :
    IsColimit (shuffleCofan F G n) :=
  Functor.LeftExtension.IsPointwiseLeftKanExtensionAt.isColimitShuffleCofan
    (LawfulDayConvolutionMonoidalCategoryStruct.isPointwiseLeftKanExtensionConvolutionExtensionUnit
      F G n)

/-- The Day convolution unit followed by the action of a bijection `σ : p ⊗ q ⟶ n` factors through
the shuffle summand of `blockImage σ`, through the block bijections of `σ`. For
`σ = shuffle S ≫ τ`, this describes the action of `τ` on the summands. -/
lemma η_app_comp_map_eq_tensorHom_comp_shuffleCofan_inj (F G : FiniteBijection ⊛⥤ V)
    {n p q : FiniteBijection} (σ : p ⊗ q ⟶ n) :
    (η F G).app (p, q) ≫ (F ⊗ G).functor.map σ =
      (F.functor.map (blockLeft σ) ⊗ₘ G.functor.map (blockRight σ)) ≫
        (shuffleCofan F G n).inj (blockImage σ) := by
  simpa [tensorHom_def] using
    (Functor.LeftExtension.mk _ (η F G)).hom_app_comp_map_eq_map_comp_shuffleCofan_inj σ

end CategoryTheory.MonoidalCategory.DayFunctor
