/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.LinearAlgebra.TensorProduct.Balanced.RightActions

/-!
# Semilinear change of scalars for balanced tensors

Let `σ : k →+* k'` be a homomorphism of commutative ground rings and `φ : R →+* R'` a
homomorphism of balancing semirings. Suppose `f : M →ₛₗ[σ] M'` and `g : N →ₛₗ[σ] N'` satisfy
`f (op r • m) = op (φ r) • f m` and `g (r • n) = φ r • g n`.

These factor maps induce a `σ`-semilinear map of balanced quotients with `[m ⊗ n] ↦ [f m ⊗ g
n]`. A balanced pairing similarly descends to a semilinear map out of the quotient. Pure
classes determine these maps, and the constructions preserve composition and identities.

If an outer action also changes along a semiring homomorphism `τ`, compatibility of the
relevant factor map with that action gives a `τ`-semilinear map on the same quotient carriers.
Right actions act on the second factor and left actions on the first. The ground rings,
balancing semirings, outer semirings, and coefficient modules have independent universes.
-/

@[expose] public section

noncomputable section

open MulOpposite
open scoped TensorProduct

universe u u' u'' r r' r'' m m' m'' n n' n'' p s s' s'' l l' l''

namespace TensorProduct.Balanced

section SemilinearLift

variable {k : Type u} {k' : Type u'} [CommRing k] [CommRing k']
  {R : Type r} [Semiring R]
  {M : Type m} {N : Type n} {P : Type p}
  [AddCommGroup M] [AddCommGroup N] [AddCommGroup P]
  [Module k M] [Module k N] [Module k' P]
  [Module Rᵐᵒᵖ M] [Module R N] {σ : k →+* k'}

/-- Descent of a balanced semilinear pairing.

Let `σ : k →+* k'` and let `f : M →ₛₗ[σ] N →ₛₗ[σ] P` satisfy `f (op r • m) n = f m (r • n)`
for all balancing scalars `r : R`. The pairing descends to a `σ`-semilinear map `Balanced k R
M N →ₛₗ[σ] P`. -/
def liftSemilinear (f : M →ₛₗ[σ] N →ₛₗ[σ] P)
    (hf : ∀ (r : R) (m : M) (n : N), f (op r • m) n = f m (r • n)) :
    Balanced k R M N →ₛₗ[σ] P :=
  (balanceRelations k R M N).liftQ (TensorProduct.lift f) (by
    apply Submodule.span_le.mpr
    rintro x ⟨r, m, n, rfl⟩
    apply LinearMap.mem_ker.mpr
    rw [map_sub, TensorProduct.lift.tmul, TensorProduct.lift.tmul,
      hf r m n, sub_self])

/-- Semilinear pairing descent on pure balanced classes.

The descended map of a balanced semilinear pairing `f` sends `[m ⊗ n]` to `f m n`. -/
theorem liftSemilinear_mk (f : M →ₛₗ[σ] N →ₛₗ[σ] P) (hf)
    (m : M) (n : N) :
    liftSemilinear f hf (mk k R M N m n) = f m n := rfl

/-- Pure classes determine a semilinear map from a balanced quotient.

Two `σ`-semilinear maps from `Balanced k R M N` to a `k'`-module `P` are equal if they agree
on `[m ⊗ n]` for every pair `m, n`. -/
theorem semilinearHom_ext {f g : Balanced k R M N →ₛₗ[σ] P}
    (h : ∀ (m : M) (n : N), f (mk k R M N m n) = g (mk k R M N m n)) :
    f = g := by
  apply LinearMap.toAddMonoidHom_injective
  exact addHom_ext k R M N h

/-- Uniqueness of balanced semilinear pairing descent.

A `σ`-semilinear map from the balanced quotient whose value on every pure class is `f m n`
equals the descended map of the balanced pairing `f`. -/
theorem liftSemilinear_unique (f : M →ₛₗ[σ] N →ₛₗ[σ] P) (hf)
    (g : Balanced k R M N →ₛₗ[σ] P)
    (hg : ∀ (m : M) (n : N), g (mk k R M N m n) = f m n) :
    g = liftSemilinear f hf := by
  apply semilinearHom_ext
  intro m n
  exact (hg m n).trans (liftSemilinear_mk f hf m n).symm

end SemilinearLift

section ScalarChange

variable {k : Type u} {k' : Type u'} [CommRing k] [CommRing k']
  {R : Type r} {R' : Type r'} [Semiring R] [Semiring R']
  {M : Type m} {N : Type n} {M' : Type m'} {N' : Type n'}
  [AddCommGroup M] [AddCommGroup N] [AddCommGroup M'] [AddCommGroup N']
  [Module k M] [Module k N] [Module k' M'] [Module k' N']
  [Module Rᵐᵒᵖ M] [Module R N] [Module R'ᵐᵒᵖ M'] [Module R' N']
  {σ : k →+* k'}

/-- Semilinear factor maps preserve balancing relations.

For `φ : R →+* R'`, assume the `σ`-semilinear maps `f` and `g` intertwine the right and left
balancing actions through `φ`. The tensor map `TensorProduct.map f g` sends the source
balancing submodule into the target balancing submodule. -/
theorem mapSemilinear_preserves_balanceRelations (φ : R →+* R')
    (f : M →ₛₗ[σ] M') (g : N →ₛₗ[σ] N')
    (hf : ∀ (r : R) (m : M), f (op r • m) = op (φ r) • f m)
    (hg : ∀ (r : R) (n : N), g (r • n) = φ r • g n) :
    balanceRelations k R M N ≤
      Submodule.comap (TensorProduct.map f g) (balanceRelations k' R' M' N') := by
  apply Submodule.span_le.mpr
  rintro x ⟨r, m, n, rfl⟩
  change (TensorProduct.map f g)
      ((op r • m) ⊗ₜ[k] n - m ⊗ₜ[k] (r • n)) ∈
    balanceRelations k' R' M' N'
  rw [map_sub, TensorProduct.map_tmul, TensorProduct.map_tmul, hf, hg]
  exact Submodule.subset_span ⟨φ r, f m, g n, rfl⟩

/-- Semilinear map of balanced quotients under scalar change.

For a ground-ring map `σ` and a balancing-semiring map `φ`, factor maps `f` and `g` semilinear
for `σ` and intertwining the balancing actions through `φ` induce `Balanced k R M N →ₛₗ[σ]
Balanced k' R' M' N'`. -/
def mapSemilinear (φ : R →+* R') (f : M →ₛₗ[σ] M') (g : N →ₛₗ[σ] N')
    (hf : ∀ (r : R) (m : M), f (op r • m) = op (φ r) • f m)
    (hg : ∀ (r : R) (n : N), g (r • n) = φ r • g n) :
    Balanced k R M N →ₛₗ[σ] Balanced k' R' M' N' :=
  (balanceRelations k R M N).mapQ (balanceRelations k' R' M' N')
    (TensorProduct.map f g) (mapSemilinear_preserves_balanceRelations φ f g hf hg)

/-- Scalar-change map commutes with the tensor quotient projection.

For any tensor `x : M ⊗[k] N`, the scalar-change map applied to its balanced quotient class
equals the target quotient class of `TensorProduct.map f g x`. -/
theorem mapSemilinear_mkQ (φ : R →+* R') (f : M →ₛₗ[σ] M')
    (g : N →ₛₗ[σ] N') (hf hg) (x : M ⊗[k] N) :
    mapSemilinear φ f g hf hg ((balanceRelations k R M N).mkQ x) =
      (balanceRelations k' R' M' N').mkQ (TensorProduct.map f g x) :=
  LinearMap.congr_fun
    (Submodule.mapQ_mkQ (balanceRelations k R M N) (balanceRelations k' R' M' N')
      (TensorProduct.map f g)
      (h := mapSemilinear_preserves_balanceRelations φ f g hf hg)) x

/-- Pure-class formula for semilinear scalar change.

The map of balanced quotients induced by compatible semilinear factor maps `f` and `g` sends
`[m ⊗ n]` to `[f m ⊗ g n]`. -/
theorem mapSemilinear_mk (φ : R →+* R') (f : M →ₛₗ[σ] M')
    (g : N →ₛₗ[σ] N') (hf hg) (m : M) (n : N) :
    mapSemilinear φ f g hf hg (mk k R M N m n) =
      mk k' R' M' N' (f m) (g n) := by
  change (balanceRelations k' R' M' N').mkQ
    ((TensorProduct.map f g) (m ⊗ₜ[k] n)) = _
  rw [TensorProduct.map_tmul]
  rfl

/-- Uniqueness of the semilinear balanced factor map.

A `σ`-semilinear map of balanced quotients with value `[f m ⊗ g n]` on every source pure class
equals `mapSemilinear φ f g hf hg`. -/
theorem mapSemilinear_unique (φ : R →+* R') (f : M →ₛₗ[σ] M')
    (g : N →ₛₗ[σ] N') (hf hg)
    (h : Balanced k R M N →ₛₗ[σ] Balanced k' R' M' N')
    (hh : ∀ (m : M) (n : N),
      h (mk k R M N m n) = mk k' R' M' N' (f m) (g n)) :
    h = mapSemilinear φ f g hf hg := by
  apply semilinearHom_ext
  intro m n
  exact (hh m n).trans (mapSemilinear_mk φ f g hf hg m n).symm

variable {k'' : Type u''} [CommRing k'']
  {R'' : Type r''} [Semiring R'']
  {M'' : Type m''} {N'' : Type n''}
  [AddCommGroup M''] [AddCommGroup N''] [Module k'' M''] [Module k'' N'']
  [Module R''ᵐᵒᵖ M''] [Module R'' N''] {σ' : k' →+* k''}

local instance : RingHomCompTriple σ σ' (σ'.comp σ) := ⟨rfl⟩

/-- Semilinear balanced maps preserve composition.

Compose ground maps `σ : k →+* k'` and `σ' : k' →+* k''`, balancing maps `φ` and `φ'`, and
compatible factor maps `f, g` and `f', g'`. The composite quotient map is the quotient map for
`σ'.comp σ`, `φ'.comp φ`, `f' ∘ f`, and `g' ∘ g`. -/
theorem mapSemilinear_comp (φ : R →+* R') (φ' : R' →+* R'')
    (f : M →ₛₗ[σ] M') (g : N →ₛₗ[σ] N')
    (f' : M' →ₛₗ[σ'] M'') (g' : N' →ₛₗ[σ'] N'')
    (hf : ∀ (r : R) (m : M), f (op r • m) = op (φ r) • f m)
    (hg : ∀ (r : R) (n : N), g (r • n) = φ r • g n)
    (hf' : ∀ (r : R') (m : M'), f' (op r • m) = op (φ' r) • f' m)
    (hg' : ∀ (r : R') (n : N'), g' (r • n) = φ' r • g' n) :
    (mapSemilinear φ' f' g' hf' hg').comp (σ₁₃ := σ'.comp σ)
        (mapSemilinear φ f g hf hg) =
      mapSemilinear (φ'.comp φ) (f'.comp (σ₁₃ := σ'.comp σ) f)
        (g'.comp (σ₁₃ := σ'.comp σ) g)
        (fun r m => by
          change f' (f (op r • m)) = op (φ' (φ r)) • f' (f m)
          rw [hf, hf'])
        (fun r n => by
          change g' (g (r • n)) = φ' (φ r) • g' (g n)
          rw [hg, hg']) := by
  apply semilinearHom_ext
  intro m n
  simp only [LinearMap.comp_apply, mapSemilinear_mk]

variable {P : Type p} [AddCommGroup P] [Module k'' P]

/-- Semilinear descent commutes with precomposition on the factors.

Precompose a balanced pairing on `M'` and `N'` with compatible semilinear maps `f` and `g`.
Its descended map equals the descended target pairing composed with the induced source-to-
target balanced map, with composite ground-ring homomorphism. -/
theorem liftSemilinear_comp_mapSemilinear (φ : R →+* R')
    (f : M →ₛₗ[σ] M') (g : N →ₛₗ[σ] N')
    (hf : ∀ (r : R) (m : M), f (op r • m) = op (φ r) • f m)
    (hg : ∀ (r : R) (n : N), g (r • n) = φ r • g n)
    (h : M' →ₛₗ[σ'] N' →ₛₗ[σ'] P)
    (hh : ∀ (r : R') (m : M') (n : N'), h (op r • m) n = h m (r • n)) :
    (liftSemilinear h hh).comp (σ₁₃ := σ'.comp σ) (mapSemilinear φ f g hf hg) =
      liftSemilinear ((h.comp (σ₁₃ := σ'.comp σ) f).compl₂ g) (fun r m n => by
        change h (f (op r • m)) (g n) = h (f m) (g (r • n))
        rw [hf, hg]
        exact hh (φ r) (f m) (g n)) := by
  apply semilinearHom_ext
  intro m n
  rw [LinearMap.comp_apply, mapSemilinear_mk, liftSemilinear_mk,
    liftSemilinear_mk]
  rfl

end ScalarChange

section FixedScalars

variable {k : Type u} [CommRing k] {R : Type r} [Semiring R]
  {M : Type m} {N : Type n} {M' : Type m'} {N' : Type n'}
  [AddCommGroup M] [AddCommGroup N] [AddCommGroup M'] [AddCommGroup N']
  [Module k M] [Module k N] [Module k M'] [Module k N']
  [Module Rᵐᵒᵖ M] [Module R N] [Module Rᵐᵒᵖ M'] [Module R N']

/-- Fixed-scalar semilinear construction is the ground-linear balanced map.

When the ground and balancing rings remain `k` and `R`, the construction with balancing map
`RingHom.id R` and ground-linear factor maps equals `TensorProduct.Balanced.map` for those
maps. -/
theorem mapSemilinear_eq_map (f : M →ₗ[k] M') (g : N →ₗ[k] N')
    (hf : ∀ (r : R) (m : M), f (op r • m) = op r • f m)
    (hg : ∀ (r : R) (n : N), g (r • n) = r • g n) :
    mapSemilinear (RingHom.id R) f g hf hg = map f g hf hg := by
  apply hom_ext
  intro m n
  rw [mapSemilinear_mk, map_mk]

/-- Identity factors induce the identity balanced map.

Taking identity maps on the ground ring, balancing semiring, and both factors gives the
identity `k`-linear map on `Balanced k R M N`. -/
theorem mapSemilinear_id :
    mapSemilinear (RingHom.id R) (LinearMap.id : M →ₗ[k] M)
      (LinearMap.id : N →ₗ[k] N) (fun _ _ => rfl) (fun _ _ => rfl) =
      (LinearMap.id : Balanced k R M N →ₗ[k] Balanced k R M N) := by
  rw [mapSemilinear_eq_map, map_id]

end FixedScalars

section RightOuterChange

variable {k : Type u} {k' : Type u'} [CommRing k] [CommRing k']
  {R : Type r} {R' : Type r'} [Semiring R] [Semiring R']
  {S : Type s} {S' : Type s'} [Semiring S] [Semiring S']
  {M : Type m} {N : Type n} {M' : Type m'} {N' : Type n'}
  [AddCommGroup M] [AddCommGroup N] [AddCommGroup M'] [AddCommGroup N']
  [Module k M] [Module k N] [Module k' M'] [Module k' N']
  [Module Rᵐᵒᵖ M] [Module R N] [Module R'ᵐᵒᵖ M'] [Module R' N']
  [Module Sᵐᵒᵖ N] [Module S'ᵐᵒᵖ N']
  [SMulCommClass Sᵐᵒᵖ k N] [SMulCommClass R Sᵐᵒᵖ N]
  [SMulCommClass S'ᵐᵒᵖ k' N'] [SMulCommClass R' S'ᵐᵒᵖ N']
  {σ : k →+* k'}

/-- Scalar change intertwines right outer actions.

Let `τ : Sᵐᵒᵖ →+* S'ᵐᵒᵖ`. In addition to the balancing compatibility through `φ`, assume `g (t
• n) = τ t • g n`. The ground-semilinear quotient map intertwines the source right operator at
`t` and the target right operator at `τ t`, as additive maps. -/
theorem mapSemilinear_rightAction (φ : R →+* R') (τ : Sᵐᵒᵖ →+* S'ᵐᵒᵖ)
    (f : M →ₛₗ[σ] M') (g : N →ₛₗ[σ] N')
    (hf : ∀ (r : R) (m : M), f (op r • m) = op (φ r) • f m)
    (hg : ∀ (r : R) (n : N), g (r • n) = φ r • g n)
    (hgS : ∀ (t : Sᵐᵒᵖ) (n : N), g (t • n) = τ t • g n) (t : Sᵐᵒᵖ) :
    (mapSemilinear φ f g hf hg).toAddMonoidHom.comp
        (rightAction k R S M N t).toAddMonoidHom =
      (rightAction k' R' S' M' N' (τ t)).toAddMonoidHom.comp
        (mapSemilinear φ f g hf hg).toAddMonoidHom := by
  apply addHom_ext k R M N
  intro m n
  change mapSemilinear φ f g hf hg (rightAction k R S M N t (mk k R M N m n)) =
    rightAction k' R' S' M' N' (τ t) (mapSemilinear φ f g hf hg (mk k R M N m n))
  rw [rightAction_mk, mapSemilinear_mk, mapSemilinear_mk, rightAction_mk, hgS]

/-- Scalar-change map semilinear for the right outer action.

Compatible ground-semilinear factor maps, with the second factor preserving the right outer
action along `τ : Sᵐᵒᵖ →+* S'ᵐᵒᵖ`, give a `τ`-semilinear map between the balanced quotients
with their induced right module structures. -/
def mapSemilinearRight (φ : R →+* R') (τ : Sᵐᵒᵖ →+* S'ᵐᵒᵖ)
    (f : M →ₛₗ[σ] M') (g : N →ₛₗ[σ] N')
    (hf : ∀ (r : R) (m : M), f (op r • m) = op (φ r) • f m)
    (hg : ∀ (r : R) (n : N), g (r • n) = φ r • g n)
    (hgS : ∀ (t : Sᵐᵒᵖ) (n : N), g (t • n) = τ t • g n) :
    letI := rightModule k R S M N
    letI := rightModule k' R' S' M' N'
    Balanced k R M N →ₛₗ[τ] Balanced k' R' M' N' := by
  let h := mapSemilinear φ f g hf hg
  letI := rightModule k R S M N
  letI := rightModule k' R' S' M' N'
  refine { toFun := h, map_add' := h.map_add, map_smul' := ?_ }
  intro t x
  change h (rightAction k R S M N t x) = rightAction k' R' S' M' N' (τ t) (h x)
  exact DFunLike.congr_fun (mapSemilinear_rightAction φ τ f g hf hg hgS t) x

/-- Right-semilinear and ground-semilinear maps have the same values.

For every balanced class `x`, the right-outer-semilinear map induced by `φ`, `τ`, `f`, and `g`
has value `mapSemilinear φ f g hf hg x`. -/
theorem mapSemilinearRight_apply (φ : R →+* R') (τ : Sᵐᵒᵖ →+* S'ᵐᵒᵖ)
    (f : M →ₛₗ[σ] M') (g : N →ₛₗ[σ] N') (hf hg hgS)
    (x : Balanced k R M N) :
    mapSemilinearRight φ τ f g hf hg hgS x = mapSemilinear φ f g hf hg x := rfl

/-- Pure-class formula for right-outer semilinear scalar change.

The right-outer-semilinear quotient map induced by compatible factor maps sends `[m ⊗ n]` to
`[f m ⊗ g n]`. -/
theorem mapSemilinearRight_mk (φ : R →+* R') (τ : Sᵐᵒᵖ →+* S'ᵐᵒᵖ)
    (f : M →ₛₗ[σ] M') (g : N →ₛₗ[σ] N') (hf hg hgS) (m : M) (n : N) :
    mapSemilinearRight φ τ f g hf hg hgS (mk k R M N m n) =
      mk k' R' M' N' (f m) (g n) :=
  mapSemilinear_mk φ f g hf hg m n

/-- Uniqueness of the right-outer semilinear quotient map.

A `τ`-semilinear map between the induced right quotient modules whose values on pure classes
are `[f m ⊗ g n]` equals `mapSemilinearRight φ τ f g hf hg hgS`. -/
theorem mapSemilinearRight_unique (φ : R →+* R') (τ : Sᵐᵒᵖ →+* S'ᵐᵒᵖ)
    (f : M →ₛₗ[σ] M') (g : N →ₛₗ[σ] N') (hf hg hgS)
    (h : letI := rightModule k R S M N
      letI := rightModule k' R' S' M' N'
      Balanced k R M N →ₛₗ[τ] Balanced k' R' M' N')
    (hh : ∀ (m : M) (n : N),
      h (mk k R M N m n) = mk k' R' M' N' (f m) (g n)) :
    h = mapSemilinearRight φ τ f g hf hg hgS := by
  let := rightModule k R S M N
  let := rightModule k' R' S' M' N'
  apply LinearMap.toAddMonoidHom_injective
  apply addHom_ext k R M N
  intro m n
  exact (hh m n).trans (mapSemilinearRight_mk φ τ f g hf hg hgS m n).symm

variable {k'' : Type u''} [CommRing k''] {R'' : Type r''} [Semiring R'']
  {S'' : Type s''} [Semiring S''] {M'' : Type m''} {N'' : Type n''}
  [AddCommGroup M''] [AddCommGroup N''] [Module k'' M''] [Module k'' N'']
  [Module R''ᵐᵒᵖ M''] [Module R'' N''] [Module S''ᵐᵒᵖ N'']
  [SMulCommClass S''ᵐᵒᵖ k'' N''] [SMulCommClass R'' S''ᵐᵒᵖ N'']
  {σ' : k' →+* k''}

local instance : RingHomCompTriple σ σ' (σ'.comp σ) := ⟨rfl⟩

/-- Right-outer semilinear quotient maps preserve composition.

Two compatible scalar changes compose by composing the ground-ring maps, balancing-semiring
maps, right-outer maps, and factor maps. The composite quotient map is semilinear for the
composite right-outer homomorphism `τ'.comp τ`. -/
local instance (τ : Sᵐᵒᵖ →+* S'ᵐᵒᵖ) (τ' : S'ᵐᵒᵖ →+* S''ᵐᵒᵖ) :
    RingHomCompTriple τ τ' (τ'.comp τ) := ⟨rfl⟩

theorem mapSemilinearRight_comp (φ : R →+* R') (φ' : R' →+* R'')
    (τ : Sᵐᵒᵖ →+* S'ᵐᵒᵖ) (τ' : S'ᵐᵒᵖ →+* S''ᵐᵒᵖ)
    (f : M →ₛₗ[σ] M') (g : N →ₛₗ[σ] N')
    (f' : M' →ₛₗ[σ'] M'') (g' : N' →ₛₗ[σ'] N'')
    (hf : ∀ (r : R) (m : M), f (op r • m) = op (φ r) • f m)
    (hg : ∀ (r : R) (n : N), g (r • n) = φ r • g n)
    (hgS : ∀ (t : Sᵐᵒᵖ) (n : N), g (t • n) = τ t • g n)
    (hf' : ∀ (r : R') (m : M'), f' (op r • m) = op (φ' r) • f' m)
    (hg' : ∀ (r : R') (n : N'), g' (r • n) = φ' r • g' n)
    (hgS' : ∀ (t : S'ᵐᵒᵖ) (n : N'), g' (t • n) = τ' t • g' n) :
    letI := rightModule k R S M N
    letI := rightModule k' R' S' M' N'
    letI := rightModule k'' R'' S'' M'' N''
    (mapSemilinearRight φ' τ' f' g' hf' hg' hgS').comp (σ₁₃ := τ'.comp τ)
        (mapSemilinearRight φ τ f g hf hg hgS) =
      mapSemilinearRight (φ'.comp φ) (τ'.comp τ)
        (f'.comp (σ₁₃ := σ'.comp σ) f) (g'.comp (σ₁₃ := σ'.comp σ) g)
        (fun r m => by
          change f' (f (op r • m)) = op (φ' (φ r)) • f' (f m)
          rw [hf, hf'])
        (fun r n => by
          change g' (g (r • n)) = φ' (φ r) • g' (g n)
          rw [hg, hg'])
        (fun t n => by
          change g' (g (t • n)) = τ' (τ t) • g' (g n)
          rw [hgS, hgS']) := by
  let := rightModule k R S M N
  let := rightModule k' R' S' M' N'
  let := rightModule k'' R'' S'' M'' N''
  apply LinearMap.toAddMonoidHom_injective
  apply addHom_ext k R M N
  intro m n
  simp only [LinearMap.toAddMonoidHom_coe, LinearMap.comp_apply, mapSemilinearRight_mk]

end RightOuterChange

section LeftOuterChange

variable {k : Type u} {k' : Type u'} [CommRing k] [CommRing k']
  {R : Type r} {R' : Type r'} [Semiring R] [Semiring R']
  {L : Type l} {L' : Type l'} [Semiring L] [Semiring L']
  {M : Type m} {N : Type n} {M' : Type m'} {N' : Type n'}
  [AddCommGroup M] [AddCommGroup N] [AddCommGroup M'] [AddCommGroup N']
  [Module k M] [Module k N] [Module k' M'] [Module k' N']
  [Module Rᵐᵒᵖ M] [Module R N] [Module R'ᵐᵒᵖ M'] [Module R' N']
  [Module L M] [Module L' M']
  [SMulCommClass L k M] [SMulCommClass L Rᵐᵒᵖ M]
  [SMulCommClass L' k' M'] [SMulCommClass L' R'ᵐᵒᵖ M']
  {σ : k →+* k'}

/-- Scalar change intertwines left outer actions.

Let `τ : L →+* L'`. If the first factor map satisfies `f (l • m) = τ l • f m`, in addition to
balancing compatibility through `φ`, then the ground-semilinear quotient map intertwines the
left source operator at `l` and target operator at `τ l`, as additive maps. -/
theorem mapSemilinear_leftAction (φ : R →+* R') (τ : L →+* L')
    (f : M →ₛₗ[σ] M') (g : N →ₛₗ[σ] N')
    (hf : ∀ (r : R) (m : M), f (op r • m) = op (φ r) • f m)
    (hg : ∀ (r : R) (n : N), g (r • n) = φ r • g n)
    (hfL : ∀ (l : L) (m : M), f (l • m) = τ l • f m) (l : L) :
    (mapSemilinear φ f g hf hg).toAddMonoidHom.comp
        (leftAction k R L M N l).toAddMonoidHom =
      (leftAction k' R' L' M' N' (τ l)).toAddMonoidHom.comp
        (mapSemilinear φ f g hf hg).toAddMonoidHom := by
  apply addHom_ext k R M N
  intro m n
  change mapSemilinear φ f g hf hg (leftAction k R L M N l (mk k R M N m n)) =
    leftAction k' R' L' M' N' (τ l) (mapSemilinear φ f g hf hg (mk k R M N m n))
  rw [leftAction_mk, mapSemilinear_mk, mapSemilinear_mk, leftAction_mk, hfL]

/-- Scalar-change map semilinear for the left outer action.

Compatible ground-semilinear factor maps, with the first factor preserving the left outer
action along `τ : L →+* L'`, induce a `τ`-semilinear map between the balanced quotients with
their induced left module structures. -/
def mapSemilinearLeft (φ : R →+* R') (τ : L →+* L')
    (f : M →ₛₗ[σ] M') (g : N →ₛₗ[σ] N')
    (hf : ∀ (r : R) (m : M), f (op r • m) = op (φ r) • f m)
    (hg : ∀ (r : R) (n : N), g (r • n) = φ r • g n)
    (hfL : ∀ (l : L) (m : M), f (l • m) = τ l • f m) :
    letI := leftModule k R L M N
    letI := leftModule k' R' L' M' N'
    Balanced k R M N →ₛₗ[τ] Balanced k' R' M' N' := by
  let h := mapSemilinear φ f g hf hg
  letI := leftModule k R L M N
  letI := leftModule k' R' L' M' N'
  refine { toFun := h, map_add' := h.map_add, map_smul' := ?_ }
  intro l x
  change h (leftAction k R L M N l x) = leftAction k' R' L' M' N' (τ l) (h x)
  exact DFunLike.congr_fun (mapSemilinear_leftAction φ τ f g hf hg hfL l) x

/-- Pure-class formula for left-outer semilinear scalar change.

The left-outer-semilinear quotient map induced by compatible factor maps sends `[m ⊗ n]` to
`[f m ⊗ g n]`. -/
theorem mapSemilinearLeft_mk (φ : R →+* R') (τ : L →+* L')
    (f : M →ₛₗ[σ] M') (g : N →ₛₗ[σ] N') (hf hg hfL) (m : M) (n : N) :
    mapSemilinearLeft φ τ f g hf hg hfL (mk k R M N m n) =
      mk k' R' M' N' (f m) (g n) :=
  mapSemilinear_mk φ f g hf hg m n

/-- Uniqueness of the left-outer semilinear quotient map.

A `τ`-semilinear map between the induced left quotient modules whose values on pure classes
are `[f m ⊗ g n]` equals `mapSemilinearLeft φ τ f g hf hg hfL`. -/
theorem mapSemilinearLeft_unique (φ : R →+* R') (τ : L →+* L')
    (f : M →ₛₗ[σ] M') (g : N →ₛₗ[σ] N') (hf hg hfL)
    (h : letI := leftModule k R L M N
      letI := leftModule k' R' L' M' N'
      Balanced k R M N →ₛₗ[τ] Balanced k' R' M' N')
    (hh : ∀ (m : M) (n : N),
      h (mk k R M N m n) = mk k' R' M' N' (f m) (g n)) :
    h = mapSemilinearLeft φ τ f g hf hg hfL := by
  let := leftModule k R L M N
  let := leftModule k' R' L' M' N'
  apply LinearMap.toAddMonoidHom_injective
  apply addHom_ext k R M N
  intro m n
  exact (hh m n).trans (mapSemilinearLeft_mk φ τ f g hf hg hfL m n).symm

variable {k'' : Type u''} [CommRing k''] {R'' : Type r''} [Semiring R'']
  {L'' : Type l''} [Semiring L''] {M'' : Type m''} {N'' : Type n''}
  [AddCommGroup M''] [AddCommGroup N''] [Module k'' M''] [Module k'' N'']
  [Module R''ᵐᵒᵖ M''] [Module R'' N''] [Module L'' M'']
  [SMulCommClass L'' k'' M''] [SMulCommClass L'' R''ᵐᵒᵖ M'']
  {σ' : k' →+* k''}

local instance : RingHomCompTriple σ σ' (σ'.comp σ) := ⟨rfl⟩

/-- Left-outer semilinear quotient maps preserve composition.

Composing compatible scalar changes composes their ground, balancing, and left-outer
homomorphisms and both factor maps. The induced quotient map is semilinear for `τ'.comp τ`. -/
local instance (τ : L →+* L') (τ' : L' →+* L'') :
    RingHomCompTriple τ τ' (τ'.comp τ) := ⟨rfl⟩

theorem mapSemilinearLeft_comp (φ : R →+* R') (φ' : R' →+* R'')
    (τ : L →+* L') (τ' : L' →+* L'')
    (f : M →ₛₗ[σ] M') (g : N →ₛₗ[σ] N')
    (f' : M' →ₛₗ[σ'] M'') (g' : N' →ₛₗ[σ'] N'')
    (hf : ∀ (r : R) (m : M), f (op r • m) = op (φ r) • f m)
    (hg : ∀ (r : R) (n : N), g (r • n) = φ r • g n)
    (hfL : ∀ (l : L) (m : M), f (l • m) = τ l • f m)
    (hf' : ∀ (r : R') (m : M'), f' (op r • m) = op (φ' r) • f' m)
    (hg' : ∀ (r : R') (n : N'), g' (r • n) = φ' r • g' n)
    (hfL' : ∀ (l : L') (m : M'), f' (l • m) = τ' l • f' m) :
    letI := leftModule k R L M N
    letI := leftModule k' R' L' M' N'
    letI := leftModule k'' R'' L'' M'' N''
    (mapSemilinearLeft φ' τ' f' g' hf' hg' hfL').comp (σ₁₃ := τ'.comp τ)
        (mapSemilinearLeft φ τ f g hf hg hfL) =
      mapSemilinearLeft (φ'.comp φ) (τ'.comp τ)
        (f'.comp (σ₁₃ := σ'.comp σ) f) (g'.comp (σ₁₃ := σ'.comp σ) g)
        (fun r m => by
          change f' (f (op r • m)) = op (φ' (φ r)) • f' (f m)
          rw [hf, hf'])
        (fun r n => by
          change g' (g (r • n)) = φ' (φ r) • g' (g n)
          rw [hg, hg'])
        (fun l m => by
          change f' (f (l • m)) = τ' (τ l) • f' (f m)
          rw [hfL, hfL']) := by
  let := leftModule k R L M N
  let := leftModule k' R' L' M' N'
  let := leftModule k'' R'' L'' M'' N''
  apply LinearMap.toAddMonoidHom_injective
  apply addHom_ext k R M N
  intro m n
  simp only [LinearMap.toAddMonoidHom_coe, LinearMap.comp_apply, mapSemilinearLeft_mk]

end LeftOuterChange

section FixedRightOuterScalars

variable {k : Type u} [CommRing k] {R : Type r} {S : Type s}
  [Semiring R] [Semiring S]
  {M : Type m} {N : Type n} {M' : Type m'} {N' : Type n'}
  [AddCommGroup M] [AddCommGroup N] [AddCommGroup M'] [AddCommGroup N']
  [Module k M] [Module k N] [Module k M'] [Module k N']
  [Module Rᵐᵒᵖ M] [Module R N] [Module Rᵐᵒᵖ M'] [Module R N']
  [Module Sᵐᵒᵖ N] [Module Sᵐᵒᵖ N']
  [SMulCommClass Sᵐᵒᵖ k N] [SMulCommClass R Sᵐᵒᵖ N]
  [SMulCommClass Sᵐᵒᵖ k N'] [SMulCommClass R Sᵐᵒᵖ N']

/-- Fixed right outer scalars recover the right-linear balanced map.

When the ground ring, balancing semiring, and right outer semiring remain fixed, the
semilinear construction with identity scalar homomorphisms equals the right-linear map
`mapRight f g hf hg hgS`. -/
theorem mapSemilinearRight_eq_mapRight (f : M →ₗ[k] M') (g : N →ₗ[k] N')
    (hf : ∀ (r : R) (m : M), f (op r • m) = op r • f m)
    (hg : ∀ (r : R) (n : N), g (r • n) = r • g n)
    (hgS : ∀ (t : Sᵐᵒᵖ) (n : N), g (t • n) = t • g n) :
    letI := rightModule k R S M N
    letI := rightModule k R S M' N'
    mapSemilinearRight (RingHom.id R) (RingHom.id Sᵐᵒᵖ) f g hf hg hgS =
      mapRight f g hf hg hgS := by
  let := rightModule k R S M N
  let := rightModule k R S M' N'
  apply LinearMap.toAddMonoidHom_injective
  apply addHom_ext k R M N
  intro m n
  exact (mapSemilinearRight_mk (RingHom.id R) (RingHom.id Sᵐᵒᵖ) f g hf hg hgS m n).trans
    (mapRight_mk f g hf hg hgS m n).symm

/-- Identity factors induce the identity right-linear quotient map.

With the right module structure induced by `rightModule`, identity maps on the ground ring,
balancing semiring, right outer semiring, and factors give the identity `Sᵐᵒᵖ`-linear map on
the quotient. -/
theorem mapSemilinearRight_id :
    letI := rightModule k R S M N
    mapSemilinearRight (RingHom.id R) (RingHom.id Sᵐᵒᵖ)
      (LinearMap.id : M →ₗ[k] M) (LinearMap.id : N →ₗ[k] N)
      (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) =
      (LinearMap.id : Balanced k R M N →ₗ[Sᵐᵒᵖ] Balanced k R M N) := by
  let := rightModule k R S M N
  apply LinearMap.toAddMonoidHom_injective
  apply addHom_ext k R M N
  intro m n
  exact mapSemilinearRight_mk (RingHom.id R) (RingHom.id Sᵐᵒᵖ)
    (LinearMap.id : M →ₗ[k] M) (LinearMap.id : N →ₗ[k] N)
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) m n

end FixedRightOuterScalars

section FixedLeftOuterScalars

variable {k : Type u} [CommRing k] {R : Type r} {L : Type l}
  [Semiring R] [Semiring L] {M : Type m} {N : Type n}
  [AddCommGroup M] [AddCommGroup N] [Module k M] [Module k N]
  [Module Rᵐᵒᵖ M] [Module R N] [Module L M]
  [SMulCommClass L k M] [SMulCommClass L Rᵐᵒᵖ M]

/-- Identity factors induce the identity left-linear quotient map.

With the left module structure induced by `leftModule`, identity maps on the ground ring,
balancing semiring, left outer semiring, and factors give the identity `L`-linear map on the
quotient. -/
theorem mapSemilinearLeft_id :
    letI := leftModule k R L M N
    mapSemilinearLeft (RingHom.id R) (RingHom.id L)
      (LinearMap.id : M →ₗ[k] M) (LinearMap.id : N →ₗ[k] N)
      (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) =
      (LinearMap.id : Balanced k R M N →ₗ[L] Balanced k R M N) := by
  let := leftModule k R L M N
  apply LinearMap.toAddMonoidHom_injective
  apply addHom_ext k R M N
  intro m n
  exact mapSemilinearLeft_mk (RingHom.id R) (RingHom.id L)
    (LinearMap.id : M →ₗ[k] M) (LinearMap.id : N →ₗ[k] N)
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) m n

end FixedLeftOuterScalars

end TensorProduct.Balanced
