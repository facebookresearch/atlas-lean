/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/
module

public import MathlibExt.Analysis.VonNeumannAlgebra.UltraweakDual
public import Mathlib.Analysis.CStarAlgebra.Spectrum
public import Mathlib.Analysis.Normed.Operator.Bilinear
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Restrict

/-!
# Normal star homomorphisms and predual pullback

For concrete von Neumann algebras `M,N`, a normal star homomorphism is a unital complex star
homomorphism `f : M → N` continuous for `σ(M,M_*)` and `σ(N,N_*)`. It is also a bounded linear
map for the C-star norms. Identities and composition preserve normality.

Precomposition gives the bounded linear pullback `f_* : N_* → M_*`, `f_*(φ)(x)=φ(f(x))`.
Pullback reverses composition: `(g∘f)_*=f_*∘g_*`, and the identity algebra map induces the
identity on its normal-functional Banach space. The Hilbert spaces underlying the concrete
algebras may have independent universes.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped CStarAlgebra

namespace VonNeumannAlgebra

noncomputable section

universe u v w z

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {K : Type v} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- **Ultraweakly continuous unital complex star homomorphism.** Let `M,N` be concrete von
Neumann algebras on complete complex Hilbert spaces. Their normal-functional Banach spaces
`M_*,N_*` are the norm-closed spans of vector functionals, and their ultraweak topologies
are `σ(M,M_*)`, `σ(N,N_*)`. `NormalStarAlgHom M N` contains a unital complex star
homomorphism `f : M → N` continuous for these ultraweak topologies. -/
structure NormalStarAlgHom (M : VonNeumannAlgebra H) (N : VonNeumannAlgebra K) where
  /-- **Underlying unital star map of a normal homomorphism.** Let `M,N` be concrete von
  Neumann algebras on complete complex Hilbert spaces. Their normal-functional Banach
  spaces `M_*,N_*` are the norm-closed spans of vector functionals, and their ultraweak
  topologies are `σ(M,M_*)`, `σ(N,N_*)`. the field `toStarAlgHom` is the unital complex
  star homomorphism `f : M →⋆ₐ[ℂ] N`. -/
  toStarAlgHom : M →⋆ₐ[ℂ] N
  /-- **Ultraweak continuity of a normal algebra map.** Let `M,N` be concrete von Neumann
  algebras on complete complex Hilbert spaces. Their normal-functional Banach spaces
  `M_*,N_*` are the norm-closed spans of vector functionals, and their ultraweak
  topologies are `σ(M,M_*)`, `σ(N,N_*)`. the homomorphism field satisfies continuity of `f
  : M → N` from `σ(M,M_*)` to `σ(N,N_*)`. -/
  continuous_ultraweak :
    Continuous fun x : Ultraweak M =>
      (ultraweakLinearEquiv N).symm (toStarAlgHom (ultraweakLinearEquiv M x))

namespace NormalStarAlgHom

variable {M : VonNeumannAlgebra H} {N : VonNeumannAlgebra K}

/-- **Normal homomorphism equality from its star map.** Let `M,N` be concrete von Neumann
algebras on complete complex Hilbert spaces. Their normal-functional Banach spaces
`M_*,N_*` are the norm-closed spans of vector functionals, and their ultraweak topologies
are `σ(M,M_*)`, `σ(N,N_*)`. two normal homomorphisms are equal when their underlying
unital complex star homomorphisms are equal. -/
@[ext]
theorem ext {f g : NormalStarAlgHom M N} (h : f.toStarAlgHom = g.toStarAlgHom) : f = g := by
  cases f
  cases g
  cases h
  rfl

@[macro_inline]
instance : FunLike (NormalStarAlgHom M N) M N where
  coe f := f.toStarAlgHom
  coe_injective f g h := by
    have hmap : f.toStarAlgHom = g.toStarAlgHom :=
      DFunLike.ext _ _ fun x => congrFun h x
    exact ext hmap

instance : Coe (NormalStarAlgHom M N) (M →⋆ₐ[ℂ] N) := ⟨toStarAlgHom⟩

instance : AlgHomClass (NormalStarAlgHom M N) ℂ M N where
  map_one f := map_one f.toStarAlgHom
  map_mul f := map_mul f.toStarAlgHom
  map_zero f := map_zero f.toStarAlgHom
  map_add f := map_add f.toStarAlgHom
  commutes f := AlgHomClass.commutes f.toStarAlgHom

instance : StarHomClass (NormalStarAlgHom M N) M N where
  map_star f := map_star f.toStarAlgHom

/-- **Value of the underlying normal star map.** Let `M,N` be concrete von Neumann algebras on
complete complex Hilbert spaces. Their normal-functional Banach spaces `M_*,N_*` are the
norm-closed spans of vector functionals, and their ultraweak topologies are `σ(M,M_*)`,
`σ(N,N_*)`. Let `f : M → N` be a unital complex star homomorphism that is ultraweakly
continuous. for `x ∈ M`, `f.toStarAlgHom x=f(x)`. -/
@[simp]
theorem toStarAlgHom_apply (f : NormalStarAlgHom M N) (x : M) : f.toStarAlgHom x = f x :=
  rfl

/-- **Bounded linear map underlying a normal homomorphism.** Let `M,N` be concrete von Neumann
algebras on complete complex Hilbert spaces. Their normal-functional Banach spaces
`M_*,N_*` are the norm-closed spans of vector functionals, and their ultraweak topologies
are `σ(M,M_*)`, `σ(N,N_*)`. Let `f : M → N` be a unital complex star homomorphism that is
ultraweakly continuous. `f.toContinuousLinearMap : M →L[ℂ] N` has value `x ↦ f(x)` for the
inherited C-star norm topologies. -/
def toContinuousLinearMap (f : NormalStarAlgHom M N) : M →L[ℂ] N :=
  ⟨LinearMap.ofClass f.toStarAlgHom, map_continuous f.toStarAlgHom⟩

/-- **Norm-continuous normal map on an algebra element.** Let `M,N` be concrete von Neumann
algebras on complete complex Hilbert spaces. Their normal-functional Banach spaces
`M_*,N_*` are the norm-closed spans of vector functionals, and their ultraweak topologies
are `σ(M,M_*)`, `σ(N,N_*)`. Let `f : M → N` be a unital complex star homomorphism that is
ultraweakly continuous. for `x ∈ M`, `f.toContinuousLinearMap x=f(x)`. -/
@[simp]
theorem toContinuousLinearMap_apply (f : NormalStarAlgHom M N) (x : M) :
    f.toContinuousLinearMap x = f x :=
  rfl

/-- **Continuous linear normal map between ultraweak algebras.** Let `M,N` be concrete von
Neumann algebras on complete complex Hilbert spaces. Their normal-functional Banach spaces
`M_*,N_*` are the norm-closed spans of vector functionals, and their ultraweak topologies
are `σ(M,M_*)`, `σ(N,N_*)`. Let `f : M → N` be a unital complex star homomorphism that is
ultraweakly continuous. `f.ultraweakMap : Ultraweak M →L[ℂ] Ultraweak N` is `x ↦ f(x)`
with source and target ultraweak topologies. -/
def ultraweakMap (f : NormalStarAlgHom M N) : Ultraweak M →L[ℂ] Ultraweak N where
  toLinearMap := (ultraweakLinearEquiv N).symm.toLinearMap.comp
    ((LinearMap.ofClass f.toStarAlgHom).comp (ultraweakLinearEquiv M).toLinearMap)
  cont := f.continuous_ultraweak

/-- **Element value of a normal map in ultraweak topology.** Let `M,N` be concrete von Neumann
algebras on complete complex Hilbert spaces. Their normal-functional Banach spaces
`M_*,N_*` are the norm-closed spans of vector functionals, and their ultraweak topologies
are `σ(M,M_*)`, `σ(N,N_*)`. Let `f : M → N` be a unital complex star homomorphism that is
ultraweakly continuous. for `x ∈ Ultraweak M`, `f.ultraweakMap x` corresponds to
`f(ultraweakLinearEquiv M x)` in the underlying algebra `N`. -/
@[simp]
theorem ultraweakMap_apply (f : NormalStarAlgHom M N) (x : Ultraweak M) :
    f.ultraweakMap x = (ultraweakLinearEquiv N).symm (f (ultraweakLinearEquiv M x)) :=
  rfl

/-- **Identity normal star homomorphism.** Let `H` be a complete complex Hilbert space and `M
⊆ B(H)` a concrete von Neumann algebra. Write `ω_(ξ,η)(x)=⟨ξ,xη⟩` for its vector
functionals. Let `M_*` be their norm-closed complex span in the continuous dual `M*`.
Equip `M` with the ultraweak topology `σ(M,M_*)`, induced by `x ↦ φ(x)` for `φ ∈ M_*`.
`NormalStarAlgHom.id M : M → M` is the unital complex star map `x ↦ x`, continuous for the
ultraweak topology. -/
def id (M : VonNeumannAlgebra H) : NormalStarAlgHom M M where
  toStarAlgHom := StarAlgHom.id ℂ M
  continuous_ultraweak := by
    have hfun :
        (fun x : Ultraweak M => (ultraweakLinearEquiv M).symm
          (StarAlgHom.id ℂ M (ultraweakLinearEquiv M x))) =
        (_root_.id : Ultraweak M → Ultraweak M) := by
      funext x
      change (ultraweakLinearEquiv M).symm (ultraweakLinearEquiv M x) = x
      exact (ultraweakLinearEquiv M).symm_apply_apply x
    rw [hfun]
    exact continuous_id

/-- **Identity normal map on an algebra element.** Let `H` be a complete complex Hilbert space
and `M ⊆ B(H)` a concrete von Neumann algebra. Write `ω_(ξ,η)(x)=⟨ξ,xη⟩` for its vector
functionals. Let `M_*` be their norm-closed complex span in the continuous dual `M*`.
Equip `M` with the ultraweak topology `σ(M,M_*)`, induced by `x ↦ φ(x)` for `φ ∈ M_*`. for
`x ∈ M`, `NormalStarAlgHom.id M x=x`. -/
@[simp]
theorem id_apply (x : M) : id M x = x :=
  rfl

variable {L : Type w} [NormedAddCommGroup L] [InnerProductSpace ℂ L] [CompleteSpace L]
variable {P : VonNeumannAlgebra L}

/-- **Composition of normal star homomorphisms.** Let `M,N` be concrete von Neumann algebras
on complete complex Hilbert spaces. Their normal-functional Banach spaces `M_*,N_*` are
the norm-closed spans of vector functionals, and their ultraweak topologies are
`σ(M,M_*)`, `σ(N,N_*)`. Let `f : M → N` be a unital complex star homomorphism that is
ultraweakly continuous. if `P` is another concrete von Neumann algebra and `g : N → P` a
normal unital complex star homomorphism, `g.comp f : M → P` is `x ↦ g(f(x))`. -/
def comp (g : NormalStarAlgHom N P) (f : NormalStarAlgHom M N) : NormalStarAlgHom M P where
  toStarAlgHom := g.toStarAlgHom.comp f.toStarAlgHom
  continuous_ultraweak := by
    have hfun :
        (fun x : Ultraweak M => (ultraweakLinearEquiv P).symm
          ((g.toStarAlgHom.comp f.toStarAlgHom) (ultraweakLinearEquiv M x))) =
        ((fun y : Ultraweak N => (ultraweakLinearEquiv P).symm
          (g.toStarAlgHom (ultraweakLinearEquiv N y))) ∘
          fun x : Ultraweak M => (ultraweakLinearEquiv N).symm
            (f.toStarAlgHom (ultraweakLinearEquiv M x))) := by
      funext x
      change (ultraweakLinearEquiv P).symm
          (g.toStarAlgHom (f.toStarAlgHom (ultraweakLinearEquiv M x))) =
        (ultraweakLinearEquiv P).symm (g.toStarAlgHom (ultraweakLinearEquiv N
          ((ultraweakLinearEquiv N).symm (f.toStarAlgHom (ultraweakLinearEquiv M x)))))
      exact congrArg (fun y : N => (ultraweakLinearEquiv P).symm (g.toStarAlgHom y))
        ((ultraweakLinearEquiv N).apply_symm_apply
          (f.toStarAlgHom (ultraweakLinearEquiv M x))).symm
    rw [hfun]
    exact g.continuous_ultraweak.comp f.continuous_ultraweak

/-- **Evaluation of composed normal maps.** Let `M,N` be concrete von Neumann algebras on
complete complex Hilbert spaces. Their normal-functional Banach spaces `M_*,N_*` are the
norm-closed spans of vector functionals, and their ultraweak topologies are `σ(M,M_*)`,
`σ(N,N_*)`. Let `f : M → N` be a unital complex star homomorphism that is ultraweakly
continuous. for a normal star homomorphism `g : N → P` and `x ∈ M`, `g.comp f x=g(f(x))`. -/
@[simp]
theorem comp_apply (g : NormalStarAlgHom N P) (f : NormalStarAlgHom M N) (x : M) :
    g.comp f x = g (f x) :=
  rfl

/-- **Target identity law for normal homomorphism composition.** Let `M,N` be concrete von
Neumann algebras on complete complex Hilbert spaces. Their normal-functional Banach spaces
`M_*,N_*` are the norm-closed spans of vector functionals, and their ultraweak topologies
are `σ(M,M_*)`, `σ(N,N_*)`. Let `f : M → N` be a unital complex star homomorphism that is
ultraweakly continuous. `(NormalStarAlgHom.id N).comp f=f`. -/
@[simp]
theorem id_comp (f : NormalStarAlgHom M N) : (id N).comp f = f := by
  apply ext
  ext x
  rfl

/-- **Source identity law for normal homomorphism composition.** Let `M,N` be concrete von
Neumann algebras on complete complex Hilbert spaces. Their normal-functional Banach spaces
`M_*,N_*` are the norm-closed spans of vector functionals, and their ultraweak topologies
are `σ(M,M_*)`, `σ(N,N_*)`. Let `f : M → N` be a unital complex star homomorphism that is
ultraweakly continuous. `f.comp (NormalStarAlgHom.id M)=f`. -/
@[simp]
theorem comp_id (f : NormalStarAlgHom M N) : f.comp (id M) = f := by
  apply ext
  ext x
  rfl

variable {QH : Type z} [NormedAddCommGroup QH] [InnerProductSpace ℂ QH] [CompleteSpace QH]
variable {Q : VonNeumannAlgebra QH}

/-- **Associativity of normal star-map composition.** Let `M,N` be concrete von Neumann
algebras on complete complex Hilbert spaces. Their normal-functional Banach spaces
`M_*,N_*` are the norm-closed spans of vector functionals, and their ultraweak topologies
are `σ(M,M_*)`, `σ(N,N_*)`. Let `f : M → N` be a unital complex star homomorphism that is
ultraweakly continuous. for normal homomorphisms `g : N → P` and `h : P → Q` between
concrete von Neumann algebras, `(h.comp g).comp f=h.comp (g.comp f)`. -/
theorem comp_assoc (h : NormalStarAlgHom P Q) (g : NormalStarAlgHom N P)
    (f : NormalStarAlgHom M N) : (h.comp g).comp f = h.comp (g.comp f) := by
  apply ext
  ext x
  rfl

/-- **Normal functionals preserved by pullback.** Let `M,N` be concrete von Neumann algebras
on complete complex Hilbert spaces. Their normal-functional Banach spaces `M_*,N_*` are
the norm-closed spans of vector functionals, and their ultraweak topologies are
`σ(M,M_*)`, `σ(N,N_*)`. Let `f : M → N` be a unital complex star homomorphism that is
ultraweakly continuous. for `φ ∈ N_*`, the functional `φ∘f ∈ M*` belongs to `M_*`. -/
theorem predualPullback_mem (f : NormalStarAlgHom M N) (φ : normalFunctionalSpace N) :
    (φ : StrongDual ℂ N).comp f.toContinuousLinearMap ∈ normalFunctionalSpace M := by
  apply mem_normalFunctionalSpace_of_ultraweak_continuous
  have hfun :
      (fun x : Ultraweak M => ((φ : StrongDual ℂ N).comp f.toContinuousLinearMap)
        (ultraweakLinearEquiv M x)) =
      ((fun y : Ultraweak N => (φ : StrongDual ℂ N) (ultraweakLinearEquiv N y)) ∘
        fun x : Ultraweak M => (ultraweakLinearEquiv N).symm
          (f.toStarAlgHom (ultraweakLinearEquiv M x))) := by
    funext x
    change (φ : StrongDual ℂ N) (f.toStarAlgHom (ultraweakLinearEquiv M x)) =
      (φ : StrongDual ℂ N) (ultraweakLinearEquiv N
        ((ultraweakLinearEquiv N).symm (f.toStarAlgHom (ultraweakLinearEquiv M x))))
    exact congrArg (fun y : N => (φ : StrongDual ℂ N) y)
      ((ultraweakLinearEquiv N).apply_symm_apply
        (f.toStarAlgHom (ultraweakLinearEquiv M x))).symm
  rw [hfun]
  exact (ultraweak_eval_continuous N φ).comp f.continuous_ultraweak

/-- **Bounded pullback between normal-functional Banach spaces.** Let `M,N` be concrete von
Neumann algebras on complete complex Hilbert spaces. Their normal-functional Banach spaces
`M_*,N_*` are the norm-closed spans of vector functionals, and their ultraweak topologies
are `σ(M,M_*)`, `σ(N,N_*)`. Let `f : M → N` be a unital complex star homomorphism that is
ultraweakly continuous. `f.predualPullback : N_* →L[ℂ] M_*` sends `φ` to `φ∘f`. -/
def predualPullback (f : NormalStarAlgHom M N) :
    normalFunctionalSpace N →L[ℂ] normalFunctionalSpace M :=
  let B := (ContinuousLinearMap.compL ℂ M N ℂ).flip f.toContinuousLinearMap
  let T := B.comp (normalFunctionalSpace N).subtypeL
  T.codRestrict (normalFunctionalSpace M) fun φ => f.predualPullback_mem φ

/-- **Evaluation formula of normal predual pullback.** Let `M,N` be concrete von Neumann
algebras on complete complex Hilbert spaces. Their normal-functional Banach spaces
`M_*,N_*` are the norm-closed spans of vector functionals, and their ultraweak topologies
are `σ(M,M_*)`, `σ(N,N_*)`. Let `f : M → N` be a unital complex star homomorphism that is
ultraweakly continuous. for `φ ∈ N_*` and `x ∈ M`, `(f.predualPullback φ)(x)=φ(f(x))`. -/
@[simp]
theorem predualPullback_apply (f : NormalStarAlgHom M N) (φ : normalFunctionalSpace N) (x : M) :
    (f.predualPullback φ : StrongDual ℂ M) x = (φ : StrongDual ℂ N) (f x) :=
  rfl

/-- **Identity normal map induces the identity pullback.** Let `H` be a complete complex
Hilbert space and `M ⊆ B(H)` a concrete von Neumann algebra. Write `ω_(ξ,η)(x)=⟨ξ,xη⟩` for
its vector functionals. Let `M_*` be their norm-closed complex span in the continuous dual
`M*`. Equip `M` with the ultraweak topology `σ(M,M_*)`, induced by `x ↦ φ(x)` for `φ ∈
M_*`. `(NormalStarAlgHom.id M).predualPullback=id_(M_*)`. -/
@[simp]
theorem predualPullback_id : (id M).predualPullback = ContinuousLinearMap.id ℂ _ := by
  apply ContinuousLinearMap.ext
  intro φ
  apply Subtype.ext
  apply ContinuousLinearMap.ext
  intro x
  rfl

/-- **Contravariant composition of normal predual pullbacks.** Let `M,N` be concrete von
Neumann algebras on complete complex Hilbert spaces. Their normal-functional Banach spaces
`M_*,N_*` are the norm-closed spans of vector functionals, and their ultraweak topologies
are `σ(M,M_*)`, `σ(N,N_*)`. Let `f : M → N` be a unital complex star homomorphism that is
ultraweakly continuous. for a normal homomorphism `g : N → P`, `(g.comp
f).predualPullback=f.predualPullback ∘ g.predualPullback` from `P_*` to `M_*`. -/
theorem predualPullback_comp (g : NormalStarAlgHom N P) (f : NormalStarAlgHom M N) :
    (g.comp f).predualPullback = f.predualPullback.comp g.predualPullback := by
  apply ContinuousLinearMap.ext
  intro φ
  apply Subtype.ext
  apply ContinuousLinearMap.ext
  intro x
  simp only [predualPullback_apply, ContinuousLinearMap.comp_apply, comp_apply]

end NormalStarAlgHom

end

end VonNeumannAlgebra
