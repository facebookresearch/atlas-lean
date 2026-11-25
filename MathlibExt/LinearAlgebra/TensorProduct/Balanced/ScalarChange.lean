/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.LinearAlgebra.TensorProduct.Balanced.RightActions

/-!
# Semilinear maps of the original balanced quotients

The commutative ground ring and the possibly noncommutative balancing
semiring may both change. Semilinear maps on the factors which intertwine
the balancing actions induce a semilinear map between the balanced tensor
quotients. A source balancing relation for `r` maps to the target relation
for its image under the balancing-semiring homomorphism.

An independently changing outer action can be compatible with this map;
the induced map is then semilinear for that action. All factor universes
are independent.
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

/-- Native semilinear descent of an actually balanced semilinear pairing. -/
def liftSemilinear (f : M →ₛₗ[σ] N →ₛₗ[σ] P)
    (hf : ∀ (r : R) (m : M) (n : N), f (op r • m) n = f m (r • n)) :
    Balanced k R M N →ₛₗ[σ] P :=
  (balanceRelations k R M N).liftQ (TensorProduct.lift f) (by
    apply Submodule.span_le.mpr
    rintro x ⟨r, m, n, rfl⟩
    apply LinearMap.mem_ker.mpr
    rw [map_sub, TensorProduct.lift.tmul, TensorProduct.lift.tmul,
      hf r m n, sub_self])

/-- The descended map has the supplied pairing on every pure class. -/
theorem liftSemilinear_mk (f : M →ₛₗ[σ] N →ₛₗ[σ] P) (hf)
    (m : M) (n : N) :
    liftSemilinear f hf (mk k R M N m n) = f m n := rfl

/-- Pure balanced classes determine a semilinear map even when its ground changes. -/
theorem semilinearHom_ext {f g : Balanced k R M N →ₛₗ[σ] P}
    (h : ∀ (m : M) (n : N), f (mk k R M N m n) = g (mk k R M N m n)) :
    f = g := by
  apply LinearMap.toAddMonoidHom_injective
  exact addHom_ext k R M N h

/-- The semilinear universal property includes uniqueness of the actual quotient lift. -/
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

/-- The native tensor map sends each source relation to the target relation
with balancing scalar `φ r`; commutativity of `R` or `R'` is not used. -/
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

/-- Change the balancing ring through the original native quotient map. -/
def mapSemilinear (φ : R →+* R') (f : M →ₛₗ[σ] M') (g : N →ₛₗ[σ] N')
    (hf : ∀ (r : R) (m : M), f (op r • m) = op (φ r) • f m)
    (hg : ∀ (r : R) (n : N), g (r • n) = φ r • g n) :
    Balanced k R M N →ₛₗ[σ] Balanced k' R' M' N' :=
  (balanceRelations k R M N).mapQ (balanceRelations k' R' M' N')
    (TensorProduct.map f g) (mapSemilinear_preserves_balanceRelations φ f g hf hg)

/-- The scalar-change map commutes with projection of every original ground tensor. -/
theorem mapSemilinear_mkQ (φ : R →+* R') (f : M →ₛₗ[σ] M')
    (g : N →ₛₗ[σ] N') (hf hg) (x : M ⊗[k] N) :
    mapSemilinear φ f g hf hg ((balanceRelations k R M N).mkQ x) =
      (balanceRelations k' R' M' N').mkQ (TensorProduct.map f g x) :=
  LinearMap.congr_fun
    (Submodule.mapQ_mkQ (balanceRelations k R M N) (balanceRelations k' R' M' N')
      (TensorProduct.map f g)
      (h := mapSemilinear_preserves_balanceRelations φ f g hf hg)) x

/-- Both original factors are retained on pure representatives. -/
theorem mapSemilinear_mk (φ : R →+* R') (f : M →ₛₗ[σ] M')
    (g : N →ₛₗ[σ] N') (hf hg) (m : M) (n : N) :
    mapSemilinear φ f g hf hg (mk k R M N m n) =
      mk k' R' M' N' (f m) (g n) := by
  change (balanceRelations k' R' M' N').mkQ
    ((TensorProduct.map f g) (m ⊗ₜ[k] n)) = _
  rw [TensorProduct.map_tmul]
  rfl

/-- The scalar-change map is characterized by its original factor values. -/
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

/-- Composition changes each actual balancing scalar by the composite ring map. -/
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

/-- Descent and scalar change commute by the actual semilinear universal property. -/
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

/-- Keeping both scalar rings recovers the existing balanced map. -/
theorem mapSemilinear_eq_map (f : M →ₗ[k] M') (g : N →ₗ[k] N')
    (hf : ∀ (r : R) (m : M), f (op r • m) = op r • f m)
    (hg : ∀ (r : R) (n : N), g (r • n) = r • g n) :
    mapSemilinear (RingHom.id R) f g hf hg = map f g hf hg := by
  apply hom_ext
  intro m n
  rw [mapSemilinear_mk, map_mk]

/-- Identity scalar and factor maps give the identity on the original quotient. -/
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

/-- The same ground-semilinear quotient map intertwines the earned right actions. -/
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

/-- Earn right outer semilinearity for the original scalar-change quotient map. -/
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

/-- Earning the outer action does not change the original quotient function. -/
theorem mapSemilinearRight_apply (φ : R →+* R') (τ : Sᵐᵒᵖ →+* S'ᵐᵒᵖ)
    (f : M →ₛₗ[σ] M') (g : N →ₛₗ[σ] N') (hf hg hgS)
    (x : Balanced k R M N) :
    mapSemilinearRight φ τ f g hf hg hgS x = mapSemilinear φ f g hf hg x := rfl

/-- The outer-semilinear map has exactly the same original pure-factor values. -/
theorem mapSemilinearRight_mk (φ : R →+* R') (τ : Sᵐᵒᵖ →+* S'ᵐᵒᵖ)
    (f : M →ₛₗ[σ] M') (g : N →ₛₗ[σ] N') (hf hg hgS) (m : M) (n : N) :
    mapSemilinearRight φ τ f g hf hg hgS (mk k R M N m n) =
      mk k' R' M' N' (f m) (g n) :=
  mapSemilinear_mk φ f g hf hg m n

/-- Outer semilinearity has the same quotient uniqueness property. -/
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

/-- Both noncommutative scalar changes compose on the same original quotient maps. -/
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

/-- Scalar change also intertwines an independent left outer action. -/
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

/-- Earn left outer semilinearity without changing the ground quotient map. -/
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

/-- Its pure classes still record the original two factor maps. -/
theorem mapSemilinearLeft_mk (φ : R →+* R') (τ : L →+* L')
    (f : M →ₛₗ[σ] M') (g : N →ₛₗ[σ] N') (hf hg hfL) (m : M) (n : N) :
    mapSemilinearLeft φ τ f g hf hg hfL (mk k R M N m n) =
      mk k' R' M' N' (f m) (g n) :=
  mapSemilinear_mk φ f g hf hg m n

/-- The earned left outer map is characterized by the original two factor values. -/
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

/-- Independent left outer scalar changes compose with the native quotient maps. -/
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

/-- Keeping all scalar rings recovers the exact existing earned right-linear map. -/
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

/-- Identity scalar and factor maps act by the identity on the original right module. -/
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

/-- The independent left outer identity has the same actual quotient identity. -/
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
