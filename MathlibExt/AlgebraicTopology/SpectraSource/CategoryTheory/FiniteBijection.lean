/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

/-
Completed Apache source port from TauCeti, commit 62bbc0596dc3539d488232e4e924a338548ea0a9.
Original copyright and authors are retained; module/namespace paths are adapted for Atlas.
Source: https://github.com/TauCetiProject/TauCeti/blob/62bbc0596dc3539d488232e4e924a338548ea0a9/TauCeti/CategoryTheory/FiniteBijection.lean
License: https://github.com/TauCetiProject/TauCeti/blob/62bbc0596dc3539d488232e4e924a338548ea0a9/LICENSE
-/

public import Mathlib.Algebra.Group.End
public import Mathlib.CategoryTheory.Endomorphism
public import Mathlib.CategoryTheory.Monoidal.Braided.Basic
public import Mathlib.CategoryTheory.Skeletal
public import Mathlib.Logic.Equiv.Fin.Basic

/-!
# The finite-bijection groupoid

The groupoid `FiniteBijection` has one object `mk n` for each natural number `n`, and its
morphisms `mk n ⟶ mk m` are the bijections `Fin n ≃ Fin m`. It is the standard skeleton of the
groupoid of finite sets and bijections, and its automorphism group at `mk n` is the symmetric
group `Equiv.Perm (Fin n)`.

Block sum makes it a symmetric monoidal category: the tensor product of `mk n` and `mk m` is
`mk (n + m)`, a pair of bijections acts on the two blocks `Fin.castAdd` and `Fin.natAdd`
separately, and the braiding is the block swap `finAddFlip`. The associator and unitors are the
casts along `Nat.add_assoc`, `Nat.zero_add` and `Nat.add_zero`.

Functors out of this symmetric monoidal groupoid are symmetric sequences, and Day convolution
along its block sum is the product of symmetric sequences used to define symmetric spectra.

## References

* M. Hovey, B. Shipley and J. Smith, *Symmetric spectra*, J. Amer. Math. Soc. 13 (2000),
  Section 2.1.
-/

public section

open CategoryTheory MonoidalCategory

namespace MathlibExt.SpectraSource

/-- The finite-bijection groupoid: an object is a natural number `n`, standing for the
standard finite set `Fin n`. -/
@[ext]
structure FiniteBijection : Type where
  /-- The object standing for `Fin n`. -/
  mk ::
  /-- The cardinality of the standard finite set an object stands for. -/
  len : ℕ

namespace FiniteBijection

@[simp]
lemma mk_len (n : FiniteBijection) : mk n.len = n := rfl

/-- A morphism of `FiniteBijection` is a bijection of the standard finite sets. -/
@[ext]
structure Hom (n m : FiniteBijection) where
  /-- The morphism given by a bijection of the standard finite sets. -/
  mk ::
  /-- The bijection underlying a morphism. -/
  toEquiv : Fin n.len ≃ Fin m.len

instance : Groupoid FiniteBijection where
  Hom := Hom
  id _ := ⟨Equiv.refl _⟩
  comp f g := ⟨f.toEquiv.trans g.toEquiv⟩
  inv f := ⟨f.toEquiv.symm⟩
  inv_comp f := Hom.ext f.toEquiv.symm_trans_self
  comp_inv f := Hom.ext f.toEquiv.self_trans_symm

variable {n m k : FiniteBijection}

@[ext]
lemma hom_ext {f g : n ⟶ m} (h : ∀ i, f.toEquiv i = g.toEquiv i) : f = g :=
  Hom.ext (Equiv.ext h)

@[simp]
lemma toEquiv_id (n : FiniteBijection) : Hom.toEquiv (𝟙 n) = Equiv.refl _ := rfl

@[simp]
lemma toEquiv_comp (f : n ⟶ m) (g : m ⟶ k) :
    (f ≫ g).toEquiv = f.toEquiv.trans g.toEquiv := rfl

@[simp]
lemma toEquiv_inv (f : n ⟶ m) : (inv f).toEquiv = f.toEquiv.symm := by
  rw [← Groupoid.inv_eq_inv]
  rfl

/-- The isomorphism of `FiniteBijection` given by a bijection of the standard finite sets. -/
@[expose, simps]
def isoMk (e : Fin n.len ≃ Fin m.len) : n ≅ m where
  hom := ⟨e⟩
  inv := ⟨e.symm⟩
  hom_inv_id := Hom.ext e.self_trans_symm
  inv_hom_id := Hom.ext e.symm_trans_self

/-- Isomorphisms of `FiniteBijection` are the bijections of the standard finite sets. -/
@[expose, simps]
def isoEquiv : (n ≅ m) ≃ (Fin n.len ≃ Fin m.len) where
  toFun e := e.hom.toEquiv
  invFun := isoMk
  left_inv _ := by ext; rfl
  right_inv _ := rfl

/-- Two objects of `FiniteBijection` are isomorphic only if they are equal. -/
lemma skeletal : Skeletal FiniteBijection := fun _ _ ⟨e⟩ ↦
  FiniteBijection.ext (Fin.equiv_iff_eq.mp ⟨isoEquiv e⟩)

/-- `FiniteBijection` has morphisms only between equal objects. -/
lemma eq_of_hom (f : n ⟶ m) : n = m :=
  skeletal ⟨Groupoid.isoEquivHom n m |>.symm f⟩

/-- The automorphism group of an object of `FiniteBijection` is the symmetric group of the
standard finite set it stands for. -/
@[expose, simps]
def autMulEquiv (n : FiniteBijection) : Aut n ≃* Equiv.Perm (Fin n.len) where
  toFun e := e.asIso.hom.toEquiv
  invFun σ := .of (isoMk σ)
  left_inv e := by ext; rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

/-! ### The block-sum symmetric monoidal structure -/

instance : MonoidalCategoryStruct FiniteBijection where
  tensorObj n m := mk (n.len + m.len)
  tensorUnit := mk 0
  tensorHom f g := ⟨finSumFinEquiv.symm.trans
    ((f.toEquiv.sumCongr g.toEquiv).trans finSumFinEquiv)⟩
  whiskerLeft n _ _ g := ⟨finSumFinEquiv.symm.trans
    (((Equiv.refl (Fin n.len)).sumCongr g.toEquiv).trans finSumFinEquiv)⟩
  whiskerRight f m := ⟨finSumFinEquiv.symm.trans
    ((f.toEquiv.sumCongr (Equiv.refl (Fin m.len))).trans finSumFinEquiv)⟩
  associator n m k := isoMk (finCongr (Nat.add_assoc n.len m.len k.len))
  leftUnitor n := isoMk (finCongr (Nat.zero_add n.len))
  rightUnitor n := isoMk (finCongr (Nat.add_zero n.len))

/- The next two lemmas are not `simp`: rewriting a length inside the type of a coerced bijection
would stop the block lemmas below from matching. -/
lemma tensorObj_len (n m : FiniteBijection) : (n ⊗ m).len = n.len + m.len := rfl

lemma tensorUnit_len : (𝟙_ FiniteBijection).len = 0 := rfl

/-- There is at most one morphism out of the tensor unit `mk 0`, the empty bijection. In
particular the only endomorphism of the tensor unit is the identity. -/
instance (n : FiniteBijection) : Subsingleton (𝟙_ FiniteBijection ⟶ n) :=
  ⟨fun _ _ ↦ hom_ext fun i ↦ Fin.elim0 i⟩

/-- There is no morphism from the tensor unit `mk 0` to a nonempty standard finite set. -/
instance (n : ℕ) : IsEmpty (𝟙_ FiniteBijection ⟶ mk (n + 1)) :=
  ⟨fun f ↦ n.succ_ne_zero (congrArg len (eq_of_hom f)).symm⟩

lemma toEquiv_tensorHom {n m n' m' : FiniteBijection} (f : n ⟶ m) (g : n' ⟶ m') :
    (f ⊗ₘ g).toEquiv =
      finSumFinEquiv.symm.trans ((f.toEquiv.sumCongr g.toEquiv).trans finSumFinEquiv) := rfl

lemma toEquiv_whiskerLeft (n : FiniteBijection) {m m' : FiniteBijection} (g : m ⟶ m') :
    (n ◁ g).toEquiv = finSumFinEquiv.symm.trans
      (((Equiv.refl (Fin n.len)).sumCongr g.toEquiv).trans finSumFinEquiv) := rfl

lemma toEquiv_whiskerRight {n n' : FiniteBijection} (f : n ⟶ n') (m : FiniteBijection) :
    (f ▷ m).toEquiv = finSumFinEquiv.symm.trans
      ((f.toEquiv.sumCongr (Equiv.refl (Fin m.len))).trans finSumFinEquiv) := rfl

/- `simp` does not rewrite `finSumFinEquiv.symm` at an index typed by `(n ⊗ n').len` on its own,
since that length only unfolds to `n.len + n'.len`; instantiating the Mathlib lemma at `i` fixes
the lengths so that it fires. -/
@[simp]
lemma toEquiv_tensorHom_castAdd {n m n' m' : FiniteBijection} (f : n ⟶ m) (g : n' ⟶ m')
    (i : Fin n.len) :
    (f ⊗ₘ g).toEquiv (Fin.castAdd n'.len i) = Fin.castAdd m'.len (f.toEquiv i) := by
  simp [toEquiv_tensorHom, finSumFinEquiv_symm_apply_castAdd i]

@[simp]
lemma toEquiv_tensorHom_natAdd {n m n' m' : FiniteBijection} (f : n ⟶ m) (g : n' ⟶ m')
    (i : Fin n'.len) :
    (f ⊗ₘ g).toEquiv (Fin.natAdd n.len i) = Fin.natAdd m.len (g.toEquiv i) := by
  simp [toEquiv_tensorHom, finSumFinEquiv_symm_apply_natAdd i]

/-- A tensor product of bijections determines its two factors. -/
@[simp]
lemma tensorHom_inj {n m n' m' : FiniteBijection} {f f' : n ⟶ m} {g g' : n' ⟶ m'} :
    f ⊗ₘ g = f' ⊗ₘ g' ↔ f = f' ∧ g = g' := by
  refine ⟨fun h ↦ ⟨hom_ext fun i ↦ ?_, hom_ext fun j ↦ ?_⟩, fun h ↦ h.1 ▸ h.2 ▸ rfl⟩
  · have := congrArg (·.toEquiv (Fin.castAdd n'.len i)) h
    simp only [toEquiv_tensorHom_castAdd] at this
    exact Fin.castAdd_injective _ _ this
  · have := congrArg (·.toEquiv (Fin.natAdd n.len j)) h
    simp only [toEquiv_tensorHom_natAdd] at this
    exact Fin.natAdd_injective _ _ this

/- Whiskering is defined as tensoring with an identity, so the whisker block lemmas are the
tensor block lemmas at `𝟙 n` and `𝟙 m`. -/
@[simp]
lemma toEquiv_whiskerLeft_castAdd (n : FiniteBijection) {m m' : FiniteBijection} (g : m ⟶ m')
    (i : Fin n.len) : (n ◁ g).toEquiv (Fin.castAdd m.len i) = Fin.castAdd m'.len i :=
  toEquiv_tensorHom_castAdd (𝟙 n) g i

@[simp]
lemma toEquiv_whiskerLeft_natAdd (n : FiniteBijection) {m m' : FiniteBijection} (g : m ⟶ m')
    (i : Fin m.len) : (n ◁ g).toEquiv (Fin.natAdd n.len i) = Fin.natAdd n.len (g.toEquiv i) :=
  toEquiv_tensorHom_natAdd (𝟙 n) g i

@[simp]
lemma toEquiv_whiskerRight_castAdd {n n' : FiniteBijection} (f : n ⟶ n') (m : FiniteBijection)
    (i : Fin n.len) :
    (f ▷ m).toEquiv (Fin.castAdd m.len i) = Fin.castAdd m.len (f.toEquiv i) :=
  toEquiv_tensorHom_castAdd f (𝟙 m) i

@[simp]
lemma toEquiv_whiskerRight_natAdd {n n' : FiniteBijection} (f : n ⟶ n') (m : FiniteBijection)
    (i : Fin m.len) : (f ▷ m).toEquiv (Fin.natAdd n.len i) = Fin.natAdd n'.len i :=
  toEquiv_tensorHom_natAdd f (𝟙 m) i

lemma toEquiv_associator_hom (n m k : FiniteBijection) :
    (α_ n m k).hom.toEquiv = finCongr (Nat.add_assoc n.len m.len k.len) := rfl

lemma toEquiv_associator_inv (n m k : FiniteBijection) :
    (α_ n m k).inv.toEquiv = finCongr (Nat.add_assoc n.len m.len k.len).symm := rfl

lemma toEquiv_leftUnitor_hom (n : FiniteBijection) :
    (λ_ n).hom.toEquiv = finCongr (Nat.zero_add n.len) := rfl

lemma toEquiv_leftUnitor_inv (n : FiniteBijection) :
    (λ_ n).inv.toEquiv = finCongr (Nat.zero_add n.len).symm := rfl

lemma toEquiv_rightUnitor_hom (n : FiniteBijection) :
    (ρ_ n).hom.toEquiv = finCongr (Nat.add_zero n.len) := rfl

lemma toEquiv_rightUnitor_inv (n : FiniteBijection) :
    (ρ_ n).inv.toEquiv = finCongr (Nat.add_zero n.len).symm := rfl

@[simp]
lemma toEquiv_associator_hom_castAdd_castAdd (n m k : FiniteBijection) (i : Fin n.len) :
    (α_ n m k).hom.toEquiv (Fin.castAdd k.len (Fin.castAdd m.len i)) =
      Fin.castAdd (m ⊗ k).len i :=
  rfl

@[simp]
lemma toEquiv_associator_hom_castAdd_natAdd (n m k : FiniteBijection) (i : Fin m.len) :
    (α_ n m k).hom.toEquiv (Fin.castAdd k.len (Fin.natAdd n.len i)) =
      Fin.natAdd n.len (Fin.castAdd k.len i) :=
  rfl

@[simp]
lemma toEquiv_associator_hom_natAdd (n m k : FiniteBijection) (i : Fin k.len) :
    (α_ n m k).hom.toEquiv (Fin.natAdd (n ⊗ m).len i) =
      Fin.natAdd n.len (Fin.natAdd m.len i) :=
  Fin.ext (Nat.add_assoc n.len m.len i)

@[simp]
lemma toEquiv_associator_inv_castAdd (n m k : FiniteBijection) (i : Fin n.len) :
    (α_ n m k).inv.toEquiv (Fin.castAdd (m ⊗ k).len i) =
      Fin.castAdd k.len (Fin.castAdd m.len i) :=
  rfl

@[simp]
lemma toEquiv_associator_inv_natAdd_castAdd (n m k : FiniteBijection) (i : Fin m.len) :
    (α_ n m k).inv.toEquiv (Fin.natAdd n.len (Fin.castAdd k.len i)) =
      Fin.castAdd k.len (Fin.natAdd n.len i) :=
  rfl

@[simp]
lemma toEquiv_associator_inv_natAdd_natAdd (n m k : FiniteBijection) (i : Fin k.len) :
    (α_ n m k).inv.toEquiv (Fin.natAdd n.len (Fin.natAdd m.len i)) =
      Fin.natAdd (n ⊗ m).len i :=
  Fin.ext (Nat.add_assoc n.len m.len i).symm

@[simp]
lemma toEquiv_leftUnitor_hom_natAdd (n : FiniteBijection) (i : Fin n.len) :
    (λ_ n).hom.toEquiv (Fin.natAdd (𝟙_ FiniteBijection).len i) = i :=
  Fin.ext (Nat.zero_add i)

@[simp]
lemma toEquiv_leftUnitor_inv_apply (n : FiniteBijection) (i : Fin n.len) :
    (λ_ n).inv.toEquiv i = Fin.natAdd (𝟙_ FiniteBijection).len i :=
  Fin.ext (Nat.zero_add i).symm

@[simp]
lemma toEquiv_rightUnitor_hom_castAdd (n : FiniteBijection) (i : Fin n.len) :
    (ρ_ n).hom.toEquiv (Fin.castAdd (𝟙_ FiniteBijection).len i) = i :=
  rfl

@[simp]
lemma toEquiv_rightUnitor_inv_apply (n : FiniteBijection) (i : Fin n.len) :
    (ρ_ n).inv.toEquiv i = Fin.castAdd (𝟙_ FiniteBijection).len i :=
  rfl

instance : MonoidalCategory FiniteBijection where
  tensorHom_def _ _ := by ext i; induction i using Fin.addCases <;> simp
  id_tensorHom_id _ _ := by ext i; induction i using Fin.addCases <;> simp
  tensorHom_comp_tensorHom _ _ _ _ := by ext i; induction i using Fin.addCases <;> simp
  whiskerLeft_id _ _ := by ext i; induction i using Fin.addCases <;> simp
  id_whiskerRight _ _ := by ext i; induction i using Fin.addCases <;> simp
  associator_naturality _ _ _ := by
    ext i
    induction i using Fin.addCases with
    | left i => induction i using Fin.addCases <;> simp
    | right i => simp
  leftUnitor_naturality _ := by
    ext i
    induction i using Fin.addCases with
    | left i => exact i.elim0
    | right i => simp
  rightUnitor_naturality _ := by
    ext i
    induction i using Fin.addCases with
    | left i => simp
    | right i => exact i.elim0
  pentagon _ _ _ _ := by
    ext i
    induction i using Fin.addCases with
    | left i =>
      induction i using Fin.addCases with
      | left i => induction i using Fin.addCases <;> simp
      | right i => simp
    | right i => simp
  triangle _ _ := by
    ext i
    induction i using Fin.addCases with
    | left i => induction i using Fin.addCases with
      | left i => simp
      | right i => exact i.elim0
    | right i => simp

/-- The block swap `finAddFlip`, as an isomorphism `n ⊗ m ≅ m ⊗ n`. This is the braiding `β_ n m`
of the symmetric monoidal structure on `FiniteBijection`. -/
def braiding (n m : FiniteBijection) : n ⊗ m ≅ m ⊗ n := isoMk finAddFlip

/- The `SymmetricCategory` instance below is built from `braiding`, so its coherence goals mention
`braiding n m` rather than `β_ n m`; `simp` needs these private copies of the public block lemmas
`toEquiv_braiding_hom_castAdd` and `toEquiv_braiding_hom_natAdd` to match them. -/
@[simp]
private lemma toEquiv_braiding_hom_castAdd' (n m : FiniteBijection) (i : Fin n.len) :
    (braiding n m).hom.toEquiv (Fin.castAdd m.len i) = Fin.natAdd m.len i :=
  finAddFlip_apply_castAdd i m.len

@[simp]
private lemma toEquiv_braiding_hom_natAdd' (n m : FiniteBijection) (i : Fin m.len) :
    (braiding n m).hom.toEquiv (Fin.natAdd n.len i) = Fin.castAdd n.len i :=
  finAddFlip_apply_natAdd i n.len

instance : SymmetricCategory FiniteBijection where
  braiding := braiding
  braiding_naturality_right _ _ _ _ := by
    ext i
    induction i using Fin.addCases <;> simp
  braiding_naturality_left _ _ := by
    ext i
    induction i using Fin.addCases <;> simp
  hexagon_forward _ _ _ := by
    ext i
    induction i using Fin.addCases with
    | left i => induction i using Fin.addCases <;> simp
    | right i => simp
  hexagon_reverse _ _ _ := by
    ext i
    induction i using Fin.addCases with
    | left i => simp
    | right i => induction i using Fin.addCases <;> simp
  symmetry _ _ := by
    ext i
    induction i using Fin.addCases <;> simp

lemma toEquiv_braiding_hom (n m : FiniteBijection) : (β_ n m).hom.toEquiv = finAddFlip := (rfl)

@[simp]
lemma toEquiv_braiding_hom_castAdd (n m : FiniteBijection) (i : Fin n.len) :
    (β_ n m).hom.toEquiv (Fin.castAdd m.len i) = Fin.natAdd m.len i :=
  toEquiv_braiding_hom_castAdd' n m i

@[simp]
lemma toEquiv_braiding_hom_natAdd (n m : FiniteBijection) (i : Fin m.len) :
    (β_ n m).hom.toEquiv (Fin.natAdd n.len i) = Fin.castAdd n.len i :=
  toEquiv_braiding_hom_natAdd' n m i

lemma toEquiv_braiding_inv (n m : FiniteBijection) :
    (β_ n m).inv.toEquiv = finAddFlip := (rfl)

@[simp]
lemma toEquiv_braiding_inv_castAdd (n m : FiniteBijection) (i : Fin m.len) :
    (β_ n m).inv.toEquiv (Fin.castAdd n.len i) = Fin.natAdd n.len i := by
  rw [toEquiv_braiding_inv, finAddFlip_apply_castAdd]

@[simp]
lemma toEquiv_braiding_inv_natAdd (n m : FiniteBijection) (i : Fin n.len) :
    (β_ n m).inv.toEquiv (Fin.natAdd m.len i) = Fin.castAdd m.len i := by
  rw [toEquiv_braiding_inv, finAddFlip_apply_natAdd]

end FiniteBijection

end MathlibExt.SpectraSource
