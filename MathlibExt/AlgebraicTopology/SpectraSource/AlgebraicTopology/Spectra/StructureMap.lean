/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

/-
Completed Apache source port from TauCeti, commit 62bbc0596dc3539d488232e4e924a338548ea0a9.
Original copyright and authors are retained; module/namespace paths are adapted for Atlas.
Source: https://github.com/TauCetiProject/TauCeti/blob/62bbc0596dc3539d488232e4e924a338548ea0a9/TauCeti/AlgebraicTopology/Spectra/StructureMap.lean
License: https://github.com/TauCetiProject/TauCeti/blob/62bbc0596dc3539d488232e4e924a338548ea0a9/LICENSE
-/

public import MathlibExt.AlgebraicTopology.SpectraSource.AlgebraicTopology.SimplicialSet.Pointed.Suspension
public import MathlibExt.AlgebraicTopology.SpectraSource.AlgebraicTopology.Spectra.SphereMonoid

/-!
# Single structure maps of symmetric spectra

Let `K` be a pointed simplicial set. A module `X` over the commutative monoid
`SymmetricSequence.smashPow K` of smash powers `n ↦ K^∧n` has iterated structure maps
`K^∧p ∧ X_q → X_(p+q)` (`CategoryTheory.Mod.dayStructureMap`). Restricting to `p = 1` and
identifying `K^∧1` with `K` gives the single structure maps `σ_n : K ∧ X_n → X_(1+n)`, with the
`K` coordinate on the left, and their adjoints `σ'_n : X_n → Map_*(K, X_(1+n))`. For symmetric
spectra, `K` is the simplicial circle `S¹`, so these are the structure maps `S¹ ∧ X_n → X_(1+n)`
and their adjoints `X_n → Ω X_(1+n)` into the loop space `PointedSSet.loops`; for the modules
`SphereModule k` over the higher sphere monoids, `K` is the simplicial `k`-sphere.

The single structure maps determine the module structure: the iterated structure maps are their
composites, by the associativity of the action, since block concatenation `K ∧ K^∧p ≅ K^∧(1+p)` is
an isomorphism. Consequently a map of underlying symmetric sequences is a module map exactly
  when it
commutes with every `σ_n` (`CategoryTheory.Mod.isModHom_iff_smashPowStructureMap`), and a family of
`Σ_n`-equivariant based maps `X_n → Y_n` commuting with the single structure maps is a module map
(`CategoryTheory.Mod.smashPowHomMk`). This is the description of maps in Hovey, Shipley and
Smith's sequential definition of symmetric spectra, which writes the circle on the right of the
structure maps; here the suspension coordinate is on the left, as in the module action.

The adjoint structure maps are the maps that Ω-spectra require to be weak equivalences, and the
single structure maps are those along which naive homotopy groups are formed.

## Main definitions

* `CategoryTheory.Mod.smashPowStructureMap X n`: the structure map `K ∧ X_n ⟶ X_(1+n)`.
* `CategoryTheory.Mod.smashPowAdjointStructureMap X n`: its adjoint `X_n ⟶ Map_*(K, X_(1+n))`.
* `CategoryTheory.Mod.smashPowHomMk`: a module map from equivariant level maps commuting with the
  single structure maps.

## Main statements

* `CategoryTheory.Mod.smashPowStructureMap_naturality`,
  `CategoryTheory.Mod.smashPowAdjointStructureMap_naturality`: `Σ_n`-equivariance of the
  structure maps and of their adjoints.
* `CategoryTheory.Mod.smashPowStructureMap_hom`,
  `CategoryTheory.Mod.smashPowAdjointStructureMap_hom`: module maps commute with the structure
  maps and with their adjoints.
* `CategoryTheory.Mod.isModHom_iff_smashPowStructureMap`: a map of underlying symmetric sequences
  is a module map exactly when it commutes with the single structure maps.

## References

* M. Hovey, B. Shipley and J. Smith, *Symmetric spectra*, J. Amer. Math. Soc. 13 (2000),
  Definition 1.2.2.
* M. Hovey, *Spectra and symmetric spectra in general model categories*, J. Pure Appl. Algebra
  165 (2001), 63–127.
* S. Schwede, *Symmetric spectra*, book project, Chapter I, Section 1.
-/

public section

universe u

open CategoryTheory MonoidalCategory MathlibExt.SpectraSource

namespace CategoryTheory.Mod

open scoped DayFunctor

variable {K : PointedSSet.{u}} (X : Mod SymmetricSequence.{u} (SymmetricSequence.smashPow K))

/-- The structure map `σ_n : K ∧ X_n ⟶ X_(1+n)` of a module over the smash powers of `K`: the
action of level one, after identifying `K` with its one-fold smash power. For a symmetric
spectrum, `K` is the circle. -/
noncomputable def smashPowStructureMap (n : ℕ) :
    K ⊗ X.X.functor.obj (FiniteBijection.mk n) ⟶ X.X.functor.obj (FiniteBijection.mk (1 + n)) :=
  (PointedSSet.smashPowUniqueIso K (Fin 1)).inv ▷ _ ≫
    X.dayStructureMap (FiniteBijection.mk 1) (FiniteBijection.mk n)

/-- The structure map is the level-one action. -/
lemma smashPowStructureMap_def (n : ℕ) :
    X.smashPowStructureMap n = (PointedSSet.smashPowUniqueIso K (Fin 1)).inv ▷ _ ≫
      X.dayStructureMap (FiniteBijection.mk 1) (FiniteBijection.mk n) := (rfl)

/-- The level-one action is the structure map, after collapsing the one-fold smash power. -/
lemma dayStructureMap_mk_one (n : ℕ) :
    X.dayStructureMap (FiniteBijection.mk 1) (FiniteBijection.mk n) =
      (PointedSSet.smashPowUniqueIso K (Fin 1)).hom ▷ _ ≫ X.smashPowStructureMap n := by
  simp [smashPowStructureMap_def]

/-- The structure maps are `Σ_n`-equivariant, with `Σ_n` acting on the last `n` coordinates of
level `1 + n`. -/
@[reassoc]
lemma smashPowStructureMap_naturality {n : ℕ}
    (g : FiniteBijection.mk n ⟶ FiniteBijection.mk n) :
    K ◁ X.X.functor.map g ≫ X.smashPowStructureMap n =
      X.smashPowStructureMap n ≫ X.X.functor.map (FiniteBijection.mk 1 ◁ g) := by
  have h := X.dayStructureMap_naturality (𝟙 (FiniteBijection.mk 1)) g
  simp only [FiniteBijection.toEquiv_id, PointedSSet.smashPowReindex_refl, id_tensorHom] at h
  simp only [smashPowStructureMap_def, Category.assoc, ← h, whisker_exchange_assoc]

variable {X} in
/-- Module maps commute with the structure maps. -/
@[reassoc (attr := simp)]
lemma smashPowStructureMap_hom {Y : Mod SymmetricSequence.{u} (SymmetricSequence.smashPow K)}
    (f : X ⟶ Y) (n : ℕ) :
    X.smashPowStructureMap n ≫ f.hom.natTrans.app (FiniteBijection.mk (1 + n)) =
      K ◁ f.hom.natTrans.app (FiniteBijection.mk n) ≫ Y.smashPowStructureMap n := by
  rw [smashPowStructureMap_def, smashPowStructureMap_def, Category.assoc, whisker_exchange_assoc,
    ← dayStructureMap_hom f (FiniteBijection.mk 1) (FiniteBijection.mk n)]
  -- The level `mk 1 ⊗ mk n` is `mk (1 + n)` by definition of the block sum.
  rfl

/-- The adjoint structure map `σ'_n : X_n ⟶ Map_*(K, X_(1+n))`. For a symmetric spectrum it is
the map `X_n ⟶ Ω X_(1+n)` into the loop space `PointedSSet.loops`. -/
noncomputable def smashPowAdjointStructureMap (n : ℕ) :
    X.X.functor.obj (FiniteBijection.mk n) ⟶
      (CategoryTheory.ihom K).obj (X.X.functor.obj (FiniteBijection.mk (1 + n))) :=
  MonoidalClosed.curry (X.smashPowStructureMap n)

/-- The adjoint structure map is the curried structure map. -/
lemma smashPowAdjointStructureMap_def (n : ℕ) :
    X.smashPowAdjointStructureMap n = MonoidalClosed.curry (X.smashPowStructureMap n) := (rfl)

/-- The structure map is the uncurried adjoint structure map. -/
@[simp]
lemma uncurry_smashPowAdjointStructureMap (n : ℕ) :
    MonoidalClosed.uncurry (X.smashPowAdjointStructureMap n) = X.smashPowStructureMap n :=
  MonoidalClosed.uncurry_curry _

/-- The adjoint structure maps are `Σ_n`-equivariant. -/
@[reassoc]
lemma smashPowAdjointStructureMap_naturality {n : ℕ}
    (g : FiniteBijection.mk n ⟶ FiniteBijection.mk n) :
    X.X.functor.map g ≫ X.smashPowAdjointStructureMap n =
      X.smashPowAdjointStructureMap n ≫
        (CategoryTheory.ihom K).map (X.X.functor.map (FiniteBijection.mk 1 ◁ g)) := by
  rw [smashPowAdjointStructureMap_def, ← MonoidalClosed.curry_natural_left,
    smashPowStructureMap_naturality, MonoidalClosed.curry_natural_right]

variable {X} in
/-- Module maps commute with the adjoint structure maps. -/
@[reassoc (attr := simp)]
lemma smashPowAdjointStructureMap_hom
    {Y : Mod SymmetricSequence.{u} (SymmetricSequence.smashPow K)} (f : X ⟶ Y) (n : ℕ) :
    X.smashPowAdjointStructureMap n ≫
        (CategoryTheory.ihom K).map (f.hom.natTrans.app (FiniteBijection.mk (1 + n))) =
      f.hom.natTrans.app (FiniteBijection.mk n) ≫ Y.smashPowAdjointStructureMap n := by
  rw [smashPowAdjointStructureMap_def, smashPowAdjointStructureMap_def,
    ← MonoidalClosed.curry_natural_right, smashPowStructureMap_hom,
    MonoidalClosed.curry_natural_left]

variable {X} {Y : Mod SymmetricSequence.{u} (SymmetricSequence.smashPow K)}

/-- Compatibility of a map of symmetric sequences with the level-one action, read off from its
compatibility with the single structure maps. -/
@[reassoc]
private lemma dayStructureMap_mk_one_comp (f : X.X ⟶ Y.X)
    (hf : ∀ n, X.smashPowStructureMap n ≫ f.natTrans.app (FiniteBijection.mk (1 + n)) =
      K ◁ f.natTrans.app (FiniteBijection.mk n) ≫ Y.smashPowStructureMap n)
    (q : FiniteBijection) :
    X.dayStructureMap (FiniteBijection.mk 1) q ≫ f.natTrans.app (FiniteBijection.mk 1 ⊗ q) =
      (SymmetricSequence.smashPow K).functor.obj (FiniteBijection.mk 1) ◁ f.natTrans.app q ≫
        Y.dayStructureMap (FiniteBijection.mk 1) q := by
  obtain ⟨n⟩ := q
  rw [dayStructureMap_mk_one, dayStructureMap_mk_one, Category.assoc, whisker_exchange_assoc]
  exact congrArg (_ ≫ ·) (hf n)

/-- Every map of symmetric sequences is compatible with the action of the unit level, which acts
through the unit `S⁰ ≅ K^∧0`. -/
private lemma dayStructureMap_unit_comp (f : X.X ⟶ Y.X) (q : FiniteBijection) :
    X.dayStructureMap (𝟙_ _) q ≫ f.natTrans.app (𝟙_ _ ⊗ q) =
      (SymmetricSequence.smashPow K).functor.obj (𝟙_ _) ◁ f.natTrans.app q ≫
        Y.dayStructureMap (𝟙_ _) q := by
  rw [← cancel_epi (Functor.LaxMonoidal.ε (SymmetricSequence.smashPow K).functor ▷ _),
    ← whisker_exchange_assoc]
  simp

/-- Compatibility of a map of symmetric sequences with the actions of two levels gives its
compatibility with the action of their block sum, whose multiplication map is an isomorphism. -/
private lemma dayStructureMap_tensor_comp (f : X.X ⟶ Y.X) {p p' : FiniteBijection}
    (hp : ∀ q, X.dayStructureMap p q ≫ f.natTrans.app (p ⊗ q) =
      (SymmetricSequence.smashPow K).functor.obj p ◁ f.natTrans.app q ≫ Y.dayStructureMap p q)
    (hp' : ∀ q, X.dayStructureMap p' q ≫ f.natTrans.app (p' ⊗ q) =
      (SymmetricSequence.smashPow K).functor.obj p' ◁ f.natTrans.app q ≫
        Y.dayStructureMap p' q)
    (q : FiniteBijection) :
    X.dayStructureMap (p ⊗ p') q ≫ f.natTrans.app ((p ⊗ p') ⊗ q) =
      (SymmetricSequence.smashPow K).functor.obj (p ⊗ p') ◁ f.natTrans.app q ≫
        Y.dayStructureMap (p ⊗ p') q := by
  rw [← cancel_epi (Functor.LaxMonoidal.μ (SymmetricSequence.smashPow K).functor p p' ▷ _),
    dayStructureMap_assoc_assoc, ← whisker_exchange_assoc, dayStructureMap_assoc,
    NatTrans.naturality, reassoc_of% (hp (p' ⊗ q)), ← whiskerLeft_comp_assoc, hp',
    whiskerLeft_comp_assoc, associator_naturality_right_assoc]

/-- A map of underlying symmetric sequences is a module map exactly when it commutes with the
single structure maps `K ∧ X_n ⟶ X_(1+n)`: the iterated structure maps are composites of these. -/
theorem isModHom_iff_smashPowStructureMap (f : X.X ⟶ Y.X) :
    IsModHom (SymmetricSequence.smashPow K) f ↔
      ∀ n, X.smashPowStructureMap n ≫ f.natTrans.app (FiniteBijection.mk (1 + n)) =
        K ◁ f.natTrans.app (FiniteBijection.mk n) ≫ Y.smashPowStructureMap n := by
  refine ⟨fun _ n ↦ smashPowStructureMap_hom (⟨f⟩ : X ⟶ Y) n, fun hf ↦ ?_⟩
  rw [isModHom_iff_dayStructureMap]
  intro p
  obtain ⟨k⟩ := p
  induction k with
  | zero => exact dayStructureMap_unit_comp f
  | succ k ih =>
    -- The level `mk (k + 1)` is the block sum `mk 1 ⊗ mk k`.
    rw [Nat.add_comm k 1]
    exact dayStructureMap_tensor_comp f (dayStructureMap_mk_one_comp f hf) ih

/-- A module map from `Σ_n`-equivariant based maps `X_n ⟶ Y_n` commuting with the single
structure maps. -/
noncomputable def smashPowHomMk
    (f : ∀ n, X.X.functor.obj (FiniteBijection.mk n) ⟶ Y.X.functor.obj (FiniteBijection.mk n))
    (hf : ∀ n (g : FiniteBijection.mk n ⟶ FiniteBijection.mk n),
      X.X.functor.map g ≫ f n = f n ≫ Y.X.functor.map g)
    (hσ : ∀ n, X.smashPowStructureMap n ≫ f (1 + n) = K ◁ f n ≫ Y.smashPowStructureMap n) :
    X ⟶ Y :=
  letI τ : X.X ⟶ Y.X := .mk
    { app p := f p.len
      naturality p p' g := by
        obtain ⟨k⟩ := p
        obtain ⟨k'⟩ := p'
        obtain rfl : k = k' := congrArg FiniteBijection.len (FiniteBijection.eq_of_hom g)
        exact hf k g }
  letI : IsModHom (SymmetricSequence.smashPow K) τ := (isModHom_iff_smashPowStructureMap τ).2 hσ
  ⟨τ⟩

/-- The levels of `smashPowHomMk f hf hσ` are the given maps. -/
@[simp]
lemma smashPowHomMk_hom_natTrans_app
    (f : ∀ n, X.X.functor.obj (FiniteBijection.mk n) ⟶ Y.X.functor.obj (FiniteBijection.mk n))
    (hf : ∀ n (g : FiniteBijection.mk n ⟶ FiniteBijection.mk n),
      X.X.functor.map g ≫ f n = f n ≫ Y.X.functor.map g)
    (hσ : ∀ n, X.smashPowStructureMap n ≫ f (1 + n) = K ◁ f n ≫ Y.smashPowStructureMap n)
    (n : ℕ) :
    (smashPowHomMk f hf hσ).hom.natTrans.app (FiniteBijection.mk n) = f n := (rfl)

end CategoryTheory.Mod

/- For symmetric spectra, the adjoint structure maps take values in the loop spaces. -/
noncomputable example (X : SymmetricSpectrum) (n : ℕ) :
    X.X.functor.obj (FiniteBijection.mk n) ⟶
      PointedSSet.loops.obj (X.X.functor.obj (FiniteBijection.mk (1 + n))) :=
  X.smashPowAdjointStructureMap n

/- For modules over the sphere monoid `S^(k)`, the structure maps suspend by the `k`-sphere. -/
noncomputable example (k : ℕ) (X : SphereModule k) (n : ℕ) :
    PointedSSet.sphere k ⊗ X.X.functor.obj (FiniteBijection.mk n) ⟶
      X.X.functor.obj (FiniteBijection.mk (1 + n)) :=
  X.smashPowStructureMap n
