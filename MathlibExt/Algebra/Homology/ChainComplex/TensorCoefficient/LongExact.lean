/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Algebra.Homology.ChainComplex.TensorCoefficient
public import MathlibExt.Algebra.Homology.ChainComplex.HomologyZero
public import Mathlib.Algebra.Homology.HomologySequenceLemmas

/-!
# The homology sequence for tensor coefficients

Let R be a commutative ring, K an ℕ-indexed chain complex with flat terms, and 0→A→B→C→0 a
short exact coefficient sequence. Tensoring in the order coefficient⊗K gives a short exact
sequence of complexes. Its homology sequence has connecting map δ : H_{n+1}(C⊗K) → H_n(A⊗K).

The sequence is exact at each consecutive pair of maps, and H₀(B⊗K) → H₀(C⊗K) is epic. The
connecting maps are natural both in coefficient-sequence morphisms and in maps between
flat-term complexes. A cycle, lift, and differential-preimage equation compute δ on homology
classes. Ring, coefficient, and chain-term universes remain independent.
-/

@[expose] public section

noncomputable section

open CategoryTheory

universe u v t

namespace ChainComplex.TensorCoefficient

variable (R : Type u) [CommRing R] (K : ChainComplex (ModuleCat.{v} R) ℕ)

/-- Let R be a commutative ring, K an ℕ-indexed chain complex with terms in ModuleCat.{v} R, and n
∈ ℕ. Define the functor M ↦ H_n(M⊗_R K) from ModuleCat.{t} R to ModuleCat.{max(v,t)} R. It is
the tensor-coefficient functor followed by degree-n homology. -/
def homologyFunctor (n : ℕ) : ModuleCat.{t} R ⥤ ModuleCat.{max v t} R :=
  functor R K ⋙ HomologicalComplex.homologyFunctor
    (ModuleCat.{max v t} R) (ComplexShape.down ℕ) n

/-- For a commutative ring R, an ℕ-indexed R-module chain complex K, and n ∈ ℕ, the functor M ↦
H_n(M⊗_R K) is additive. Thus its induced maps preserve sums of coefficient morphisms, without
a flatness hypothesis. -/
instance homologyFunctor_additive (n : ℕ) : (homologyFunctor.{u, v, t} R K n).Additive := by
  change (functor.{u, v, t} R K ⋙ HomologicalComplex.homologyFunctor
    (ModuleCat.{max v t} R) (ComplexShape.down ℕ) n).Additive
  infer_instance

/-- Let R be a commutative ring, K an ℕ-indexed R-module complex with every K_i flat, and S₁ → S₂
→ S₃ a short exact coefficient sequence. For n ∈ ℕ, its tensor-complex homology sequence
defines δ : H_{n+1}(S₃⊗K) → H_n(S₁⊗K). The coefficient factor is first, and flatness is
required only on K's terms. -/
def connecting (hK : ∀ n, Module.Flat R (K.X n))
    (S : ShortComplex (ModuleCat.{t} R)) (hS : S.ShortExact) (n : ℕ) :
    (homologyFunctor R K (n + 1)).obj S.X₃ ⟶
      (homologyFunctor R K n).obj S.X₁ :=
  (shortExact R K hK S hS).δ (n + 1) n rfl

@[reassoc]
theorem connecting_comp (hK : ∀ n, Module.Flat R (K.X n))
    (S : ShortComplex (ModuleCat.{t} R)) (hS : S.ShortExact) (n : ℕ) :
    connecting R K hK S hS n ≫ (homologyFunctor R K n).map S.f = 0 :=
  (shortExact R K hK S hS).δ_comp (n + 1) n rfl

@[reassoc]
theorem comp_connecting (hK : ∀ n, Module.Flat R (K.X n))
    (S : ShortComplex (ModuleCat.{t} R)) (hS : S.ShortExact) (n : ℕ) :
    (homologyFunctor R K (n + 1)).map S.g ≫ connecting R K hK S hS n = 0 :=
  (shortExact R K hK S hS).comp_δ (n + 1) n rfl

/-- For a commutative ring R, flat-term ℕ-chain complex K, and short exact coefficient sequence S₁
→^f S₂ →^g S₃, the sequence H_{n+1}(S₃⊗K) →^δ H_n(S₁⊗K) →^{H_n(f⊗id)} H_n(S₂⊗K) is exact for
every n ∈ ℕ. -/
theorem exact₁ (hK : ∀ n, Module.Flat R (K.X n))
    (S : ShortComplex (ModuleCat.{t} R)) (hS : S.ShortExact) (n : ℕ) :
    (ShortComplex.mk (connecting R K hK S hS n)
      ((homologyFunctor R K n).map S.f)
      (connecting_comp R K hK S hS n)).Exact :=
  (shortExact R K hK S hS).homology_exact₁ (n + 1) n rfl

/-- Let R be a commutative ring, K an ℕ-indexed chain complex with flat terms, and S a short exact
coefficient sequence. For every n ∈ ℕ, H_n(S₁⊗K) → H_n(S₂⊗K) → H_n(S₃⊗K) is exact. This
includes n=0 and uses the maps induced by S.f and S.g. -/
theorem exact₂ (hK : ∀ n, Module.Flat R (K.X n))
    (S : ShortComplex (ModuleCat.{t} R)) (hS : S.ShortExact) (n : ℕ) :
    (S.map (homologyFunctor R K n)).Exact :=
  (shortExact R K hK S hS).homology_exact₂ n

/-- For a commutative ring R, flat-term ℕ-chain complex K, and short exact coefficient sequence S₁
→^f S₂ →^g S₃, the sequence H_{n+1}(S₂⊗K) →^{H_{n+1}(g⊗id)} H_{n+1}(S₃⊗K) →^δ H_n(S₁⊗K) is
exact for every n ∈ ℕ. -/
theorem exact₃ (hK : ∀ n, Module.Flat R (K.X n))
    (S : ShortComplex (ModuleCat.{t} R)) (hS : S.ShortExact) (n : ℕ) :
    (ShortComplex.mk ((homologyFunctor R K (n + 1)).map S.g)
      (connecting R K hK S hS n) (comp_connecting R K hK S hS n)).Exact :=
  (shortExact R K hK S hS).homology_exact₃ (n + 1) n rfl

/-- Let R be a commutative ring, K an ℕ-chain complex with flat terms, S₁ →^f S₂ →^g S₃ a short
exact coefficient sequence, and n ∈ ℕ. Define the six-object sequence H_{n+1}(S₁⊗K) →
H_{n+1}(S₂⊗K) → H_{n+1}(S₃⊗K) →^δ H_n(S₁⊗K) → H_n(S₂⊗K) → H_n(S₃⊗K). Its five arrows are the
induced f,g maps in the two degrees and the canonical connecting map. -/
def sixTermSequence (hK : ∀ n, Module.Flat R (K.X n))
    (S : ShortComplex (ModuleCat.{t} R)) (hS : S.ShortExact) (n : ℕ) :
    ComposableArrows (ModuleCat.{max v t} R) 5 :=
  HomologicalComplex.HomologySequence.composableArrows₅
    (shortExact R K hK S hS) (n + 1) n rfl

theorem sixTermSequence_exact (hK : ∀ n, Module.Flat R (K.X n))
    (S : ShortComplex (ModuleCat.{t} R)) (hS : S.ShortExact) (n : ℕ) :
    (sixTermSequence R K hK S hS n).Exact :=
  HomologicalComplex.HomologySequence.composableArrows₅_exact
    (shortExact R K hK S hS) (n + 1) n rfl

/-- Let R be a commutative ring, K a flat-term ℕ-chain complex, and τ : S → T a morphism between
short exact coefficient sequences. For n ∈ ℕ, δ_S ≫ H_n(τ₁⊗id_K) = H_{n+1}(τ₃⊗id_K) ≫ δ_T.
This compares the connecting maps for the same complex K and the specified endpoint
coefficient maps. -/
theorem connecting_naturality_sequence (hK : ∀ n, Module.Flat R (K.X n))
    {S T : ShortComplex (ModuleCat.{t} R)} (f : S ⟶ T)
    (hS : S.ShortExact) (hT : T.ShortExact) (n : ℕ) :
    connecting R K hK S hS n ≫ (homologyFunctor R K n).map f.τ₁ =
      (homologyFunctor R K (n + 1)).map f.τ₃ ≫ connecting R K hK T hT n :=
  HomologicalComplex.HomologySequence.δ_naturality
    ((functor R K).mapShortComplex.map f)
    (shortExact R K hK S hS) (shortExact R K hK T hT) (n + 1) n rfl

/-- For a commutative ring R, a flat-term ℕ-chain complex K, and a morphism τ : S → T of short
exact coefficient sequences, the induced homology maps define a morphism between their
six-term sequences in degrees n+1 and n. Its components are H_{n+1}(τ_i⊗id_K) and
H_n(τ_i⊗id_K) for i=1,2,3, and it commutes with all five arrows. -/
def sixTermSequenceMap (hK : ∀ n, Module.Flat R (K.X n))
    {S T : ShortComplex (ModuleCat.{t} R)} (f : S ⟶ T)
    (hS : S.ShortExact) (hT : T.ShortExact) (n : ℕ) :
    sixTermSequence R K hK S hS n ⟶ sixTermSequence R K hK T hT n :=
  HomologicalComplex.HomologySequence.mapComposableArrows₅
    ((functor R K).mapShortComplex.map f)
    (shortExact R K hK S hS) (shortExact R K hK T hT) (n + 1) n rfl

/-- Let R be a commutative ring, f : K → L a map of ℕ-indexed R-module complexes, and S a
coefficient short complex. The maps id_{S_i}⊗f give a morphism S⊗K → S⊗L of short complexes of
chain complexes. This construction needs neither exactness of S nor flatness of K,L. -/
def mapShortComplex {L : ChainComplex (ModuleCat.{v} R) ℕ} (f : K ⟶ L)
    (S : ShortComplex (ModuleCat.{t} R)) :
    S.map (functor R K) ⟶ S.map (functor R L) :=
  S.mapNatTrans (map R f)

/-- Let R be a commutative ring, f : K → L a map of ℕ-chain complexes whose terms are all flat,
and S a short exact coefficient sequence. Then δ_K ≫ H_n(id_{S₁}⊗f) = H_{n+1}(id_{S₃}⊗f) ≫ δ_L
for every n ∈ ℕ. The endpoints are H_{n+1}(S₃⊗K) and H_n(S₁⊗L). -/
theorem connecting_naturality_complex
    {L : ChainComplex (ModuleCat.{v} R) ℕ} (f : K ⟶ L)
    (hK : ∀ n, Module.Flat R (K.X n)) (hL : ∀ n, Module.Flat R (L.X n))
    (S : ShortComplex (ModuleCat.{t} R)) (hS : S.ShortExact) (n : ℕ) :
    connecting R K hK S hS n ≫
        HomologicalComplex.homologyMap ((map R f).app S.X₁) n =
      HomologicalComplex.homologyMap ((map R f).app S.X₃) (n + 1) ≫
        connecting R L hL S hS n :=
  HomologicalComplex.HomologySequence.δ_naturality (mapShortComplex R K f S)
    (shortExact R K hK S hS) (shortExact R L hL S hS) (n + 1) n rfl

/-- For a commutative ring R, a flat-term ℕ-chain complex K, and a short exact coefficient
sequence S₁ → S₂ →^g S₃, the induced map H₀(S₂⊗K) → H₀(S₃⊗K) is an epimorphism. The connective
homology sequence therefore ends in H₀(S₃⊗K) → 0. -/
theorem homologyMap_zero_epi (hK : ∀ n, Module.Flat R (K.X n))
    (S : ShortComplex (ModuleCat.{t} R)) (hS : S.ShortExact) :
    Epi ((homologyFunctor R K 0).map S.g) := by
  let K₂ := (functor R K).obj S.X₂
  let K₃ := (functor R K).obj S.X₃
  let g : K₂ ⟶ K₃ := (functor R K).map S.g
  have hZero := (HomologicalComplex.shortExact_iff_degreewise_shortExact
    (S.map (functor R K))).mp (shortExact R K hK S hS) 0
  letI : Epi (g.f 0) := hZero.epi_g
  letI : Epi (ChainComplex.homologyZeroClass K₃) := by
    unfold ChainComplex.homologyZeroClass
    infer_instance
  letI : Epi (ChainComplex.homologyZeroClass K₂ ≫ HomologicalComplex.homologyMap g 0) := by
    rw [ChainComplex.homologyZeroClass_naturality]
    infer_instance
  exact epi_of_epi (ChainComplex.homologyZeroClass K₂) (HomologicalComplex.homologyMap g 0)

/-- Let R be a commutative ring, K a flat-term ℕ-chain complex, and S₁ →^f S₂ →^g S₃ a short exact
coefficient sequence. For a probe module T, let x₃ : T → (S₃⊗K)_{n+1} be a cycle, choose x₂
with x₂≫g_{n+1}=x₃, and choose x₁ : T → (S₁⊗K)_n with x₁≫f_n=x₂≫d_{n+1,n}. Then x₁ is a cycle
and [x₃]≫δ=[x₁] as maps T → H_n(S₁⊗K), where the classes use the canonical cycle lifts and
homology projections. -/
theorem connecting_eq (hK : ∀ n, Module.Flat R (K.X n))
    (S : ShortComplex (ModuleCat.{t} R)) (hS : S.ShortExact) (n : ℕ)
    {T : ModuleCat.{max v t} R}
    (x₃ : T ⟶ ((functor R K).obj S.X₃).X (n + 1))
    (hx₃ : x₃ ≫ ((functor R K).obj S.X₃).d (n + 1) n = 0)
    (x₂ : T ⟶ ((functor R K).obj S.X₂).X (n + 1))
    (hx₂ : x₂ ≫ ((functor R K).map S.g).f (n + 1) = x₃)
    (x₁ : T ⟶ ((functor R K).obj S.X₁).X n)
    (hx₁ : x₁ ≫ ((functor R K).map S.f).f n =
      x₂ ≫ ((functor R K).obj S.X₂).d (n + 1) n) :
    ((functor R K).obj S.X₃).liftCycles x₃ n
      ((ComplexShape.down ℕ).next_eq' (show (ComplexShape.down ℕ).Rel (n + 1) n from rfl)) hx₃ ≫
        ((functor R K).obj S.X₃).homologyπ (n + 1) ≫
          connecting R K hK S hS n =
      ((functor R K).obj S.X₁).liftCycles x₁ ((ComplexShape.down ℕ).next n) rfl
        (by
          let h := shortExact R K hK S hS
          have hDegree := (HomologicalComplex.shortExact_iff_degreewise_shortExact
            (S.map (functor R K))).mp h ((ComplexShape.down ℕ).next n)
          let : Mono (((functor R K).map S.f).f ((ComplexShape.down ℕ).next n)) := hDegree.mono_f
          rw [← cancel_mono (((functor R K).map S.f).f ((ComplexShape.down ℕ).next n)),
            Category.assoc, ← HomologicalComplex.Hom.comm, reassoc_of% hx₁,
            HomologicalComplex.d_comp_d, CategoryTheory.Limits.comp_zero,
            CategoryTheory.Limits.zero_comp]) ≫
        ((functor R K).obj S.X₁).homologyπ n :=
  (shortExact R K hK S hS).δ_eq (n + 1) n rfl x₃ hx₃ x₂ hx₂ x₁ hx₁
    ((ComplexShape.down ℕ).next n) rfl

end ChainComplex.TensorCoefficient

end
