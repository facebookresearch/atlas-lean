/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Group.End
public import Mathlib.GroupTheory.Coprod.Basic
public import Mathlib.GroupTheory.FreeGroup.Basic
import Mathlib.Algebra.Group.Pi.Lemmas
import Mathlib.Data.Fintype.EquivFin
import Mathlib.GroupTheory.CoprodI
import Mathlib.GroupTheory.FreeGroup.Reduce

/-!
# Free products of subgroups of `Aut(Fₙ)` (Kourovka Notebook Problem 18.11)

Kourovka Notebook, Problem 18.11 (V. G. Bardakov): let `G` and `H` be subgroups of the automorphism
group `Aut(Fₙ)` of a free group `Fₙ` of rank `n ≥ 2`. Is it true that the free product `G ∗ H`
embeds in the automorphism group `Aut(Fₘ)` for some `m`?

We prove that the free product in Bardakov's question embeds in the automorphism group of a
free group of finite rank. A fixed separator makes the ordered basis of each free factor into a
word with trivial stabilizer. Twisting one further generator by the two resulting coboundaries
makes its image detect every nonempty reduced word in the subgroup free product.

Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Problem 18.11 (V. G. Bardakov). UnsolvedMath record
UM-00701440 (`KOU-18.11`), dataset ulamai/UnsolvedMath v1.8.0.

`Aut(Fₙ) = MulAut (FreeGroup (Fin n))` and the free product is Mathlib's `Monoid.Coprod`; no
finiteness assumption is made on `G` and `H`.
-/

@[expose] public section

namespace MathlibExt.GroupTheory.FreeProductAutFreeGroupEmbeddingKourovka18Problem11Wanted

/-- **Bardakov's question on free products in $\mathrm{Aut}(F_n)$ (Kourovka 18.11).** The statement
that for every natural number $n \ge 2$ and all subgroups $G$ and $H$ of the automorphism group
$\mathrm{Aut}(F_n)$ of the free group $F_n$ of rank $n$, there are a natural number $m$ and an
injective group homomorphism from the free product $G \ast H$ to $\mathrm{Aut}(F_m)$. -/
def freeProductAutFreeGroupEmbeds : Prop :=
  ∀ n : ℕ, 2 ≤ n → ∀ G H : Subgroup (MulAut (FreeGroup (Fin n))),
    ∃ (m : ℕ) (f : Monoid.Coprod G H →* MulAut (FreeGroup (Fin m))), Function.Injective f

open Monoid Monoid.CoprodI

section Indexed

variable {ι : Type*}
variable {B : ι → Type*} [∀ i, Group (B i)]

/-- The endomorphism induced by independent automorphisms of the free factors. -/
private def coprodEnd (a : ∀ i, MulAut (B i)) : CoprodI B →* CoprodI B :=
  CoprodI.lift fun i => CoprodI.of.comp (a i).toMonoidHom

@[simp]
private theorem coprodEnd_of (a : ∀ i, MulAut (B i)) (i : ι) (x : B i) :
    coprodEnd a (CoprodI.of x) = CoprodI.of (a i x) := by
  simp [coprodEnd]

private theorem coprodEnd_one : coprodEnd (1 : ∀ i, MulAut (B i)) = MonoidHom.id _ := by
  ext i x
  simp

private theorem coprodEnd_mul (a b : ∀ i, MulAut (B i)) :
    coprodEnd (a * b) = (coprodEnd a).comp (coprodEnd b) := by
  ext i x
  simp

/-- The factorwise action on the free product. -/
private def coprodAut : (∀ i, MulAut (B i)) →* MulAut (CoprodI B) where
  toFun a := (coprodEnd a).toMulEquiv (coprodEnd a⁻¹)
    (by rw [← coprodEnd_mul, inv_mul_cancel, coprodEnd_one])
    (by rw [← coprodEnd_mul, mul_inv_cancel, coprodEnd_one])
  map_one' := DFunLike.ext _ _ fun x => DFunLike.congr_fun coprodEnd_one x
  map_mul' a b := DFunLike.ext _ _ fun x => DFunLike.congr_fun (coprodEnd_mul a b) x

@[simp]
private theorem coprodAut_of (a : ∀ i, MulAut (B i)) (i : ι) (x : B i) :
    coprodAut a (CoprodI.of x) = CoprodI.of (a i x) :=
  coprodEnd_of a i x

/-- The induced automorphism acts on a reduced word letter by letter. -/
private def mapWord (a : ∀ i, MulAut (B i)) (w : Word B) : Word B where
  toList := w.toList.map fun l => ⟨l.1, a l.1 l.2⟩
  ne_one := by
    intro l hl
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hl
    exact fun h => w.ne_one x hx ((a x.1).injective (h.trans (map_one _).symm))
  chain_ne := (List.isChain_map _).2 w.chain_ne

@[simp]
private theorem mapWord_fstIdx (a : ∀ i, MulAut (B i)) (w : Word B) :
    (mapWord a w).fstIdx = w.fstIdx := by
  simp [mapWord, Word.fstIdx, List.head?_map, Function.comp_def]

private theorem mapWord_prod (a : ∀ i, MulAut (B i)) (w : Word B) :
    (mapWord a w).prod = coprodAut a w.prod := by
  simp only [mapWord, Word.prod, map_list_prod, List.map_map, Function.comp_def,
    coprodAut_of]

end Indexed

section Twist

variable {K : Type*} [Group K]

private abbrev newGenerator : Coprod K (FreeGroup Unit) :=
  Coprod.inr (FreeGroup.of ())

/-- Extend an automorphism across a new generator `t` by sending it to `t (u⁻¹ * a u)`. -/
private def twistEnd (u : K) (a : MulAut K) :
    Coprod K (FreeGroup Unit) →* Coprod K (FreeGroup Unit) :=
  Coprod.lift (Coprod.inl.comp a.toMonoidHom)
    (FreeGroup.lift fun _ : Unit => newGenerator * Coprod.inl (u⁻¹ * a u))

@[simp]
private theorem twistEnd_inl (u : K) (a : MulAut K) (x : K) :
    twistEnd u a (Coprod.inl x) = Coprod.inl (a x) := by
  simp [twistEnd]

@[simp]
private theorem twistEnd_generator (u : K) (a : MulAut K) :
    twistEnd u a newGenerator = newGenerator * Coprod.inl (u⁻¹ * a u) := by
  simp [twistEnd]

private theorem twistEnd_one (u : K) : twistEnd u 1 = MonoidHom.id _ := by
  apply Coprod.hom_ext
  · ext x
    simp
  · ext x
    cases x
    change twistEnd u 1 newGenerator = newGenerator
    simp

private theorem twistEnd_mul (u : K) (a b : MulAut K) :
    twistEnd u (a * b) = (twistEnd u a).comp (twistEnd u b) := by
  apply Coprod.hom_ext
  · ext x
    simp
  · ext x
    cases x
    change twistEnd u (a * b) newGenerator = twistEnd u a (twistEnd u b newGenerator)
    simp [mul_assoc]

/-- The coboundary identity makes the twisted extension multiplicative. -/
private def twist (u : K) : MulAut K →* MulAut (Coprod K (FreeGroup Unit)) where
  toFun a := (twistEnd u a).toMulEquiv (twistEnd u a⁻¹)
    (by rw [← twistEnd_mul, inv_mul_cancel, twistEnd_one])
    (by rw [← twistEnd_mul, mul_inv_cancel, twistEnd_one])
  map_one' := DFunLike.ext _ _ fun x => DFunLike.congr_fun (twistEnd_one u) x
  map_mul' a b := DFunLike.ext _ _ fun x => DFunLike.congr_fun (twistEnd_mul u a b) x

@[simp]
private theorem twist_inl (u : K) (a : MulAut K) (x : K) :
    twist u a (Coprod.inl x) = Coprod.inl (a x) :=
  twistEnd_inl u a x

@[simp]
private theorem twist_generator (u : K) (a : MulAut K) :
    twist u a newGenerator = newGenerator * Coprod.inl (u⁻¹ * a u) :=
  twistEnd_generator u a

end Twist

section Embedding

variable {ι : Type*} [DecidableEq ι]
variable {A B : ι → Type*} [∀ i, Group (A i)] [∀ i, Group (B i)]

/-- Extend the action of each factor, twisting the new generator using its own basepoint. -/
private def factorTwist (f : ∀ i, A i →* MulAut (B i)) (u : ∀ i, B i) (i : ι) :
    A i →* MulAut (Coprod (CoprodI B) (FreeGroup Unit)) :=
  (twist (CoprodI.of (u i))).comp
    (coprodAut.comp ((MonoidHom.mulSingle (fun j => MulAut (B j)) i).comp (f i)))

/-- The image of the new generator records the sequence of factors of the original word. -/
private theorem factorTwist_word (f : ∀ i, A i →* MulAut (B i)) (u : ∀ i, B i)
    (hu : ∀ i (a : A i), f i a (u i) = u i → a = 1) (w : Word A) :
    ∃ v : Word B, v.fstIdx = w.fstIdx ∧
      CoprodI.lift (factorTwist f u) w.prod newGenerator = newGenerator * Coprod.inl v.prod := by
  induction w using Word.consRecOn with
  | empty =>
    exact ⟨Word.empty, rfl, by simp⟩
  | cons i a w hidx ha ih =>
    obtain ⟨v, hv, heval⟩ := ih
    let b : ∀ j, MulAut (B j) := Pi.mulSingle i (f i a)
    let c := (u i)⁻¹ * f i a (u i)
    have hc : c ≠ 1 := fun h => ha (hu i a (inv_mul_eq_one.mp h).symm)
    have hidx' : (mapWord b v).fstIdx ≠ some i := by simpa [hv] using hidx
    refine ⟨Word.cons c (mapWord b v) hidx' hc, by simp, ?_⟩
    rw [Word.prod_cons, map_mul, MulAut.mul_apply, heval, Word.prod_cons, mapWord_prod]
    change twist (CoprodI.of (u i)) (coprodAut b) (newGenerator * Coprod.inl v.prod) =
      newGenerator * Coprod.inl (CoprodI.of c * coprodAut b v.prod)
    have hcoc : (CoprodI.of (u i))⁻¹ * coprodAut b (CoprodI.of (u i)) = CoprodI.of c := by
      simp [b, c]
    rw [map_mul, twist_generator, twist_inl, hcoc, mul_assoc]
    simp only [map_mul]

private theorem factorTwist_injective (f : ∀ i, A i →* MulAut (B i)) (u : ∀ i, B i)
    (hu : ∀ i (a : A i), f i a (u i) = u i → a = 1) :
    Function.Injective (CoprodI.lift (factorTwist f u)) := by
  classical
  apply (injective_iff_map_eq_one _).2
  intro x hx
  let w := (Word.equiv (M := A)) x
  have hxw : w.prod = x := (Word.equiv (M := A)).symm_apply_apply x
  obtain ⟨v, hv, heval⟩ := factorTwist_word f u hu w
  rw [hxw, hx, MulAut.one_apply, left_eq_mul] at heval
  have hvProd : v.prod = 1 :=
    Coprod.inl_injective (heval.trans (map_one Coprod.inl).symm)
  have hvEmpty : v = Word.empty :=
    (Word.equiv (M := B)).symm.injective (hvProd.trans Word.prod_empty.symm)
  have hwIdx : w.fstIdx = none := hv.symm.trans (congrArg Word.fstIdx hvEmpty)
  have hwEmpty : w = Word.empty := by
    apply Word.ext
    cases hw : w.toList with
    | nil => rfl
    | cons a as => simp [Word.fstIdx, hw] at hwIdx
  rw [← hxw, hwEmpty, Word.prod_empty]

end Embedding

universe u

/-- A two-element indexed family, with the left factor at `false`. -/
private abbrev Two (L R : Type u) : Bool → Type _ := fun i => Bool.rec L R i

private instance twoGroup (L R : Type u) [Group L] [Group R] (i : Bool) : Group (Two L R i) := by
  cases i
  · exact ‹Group L›
  · exact ‹Group R›

private instance twoFintype (L R : Type u) [Fintype L] [Fintype R] (i : Bool) :
    Fintype (Two L R i) := by
  cases i
  · exact ‹Fintype L›
  · exact ‹Fintype R›

/-- Identify the binary coproduct with the indexed model used for normal forms. -/
private def twoCoprod (L R : Type u) [Group L] [Group R] : Coprod L R ≃* CoprodI (Two L R) :=
  let f : ∀ i, Two L R i →* Coprod L R
    | false => Coprod.inl
    | true => Coprod.inr
  (Coprod.lift (CoprodI.of (i := false)) (CoprodI.of (i := true))).toMulEquiv (CoprodI.lift f)
    (by apply Coprod.hom_ext <;> ext x <;> simp [f])
    (by ext i x; cases i <;> simp [f])

private abbrev MarkedFactor (n : ℕ) (i : Bool) := FreeGroup (Two (Fin n) Unit i)

/-- Insert a fixed separator after each member of the list of generators. -/
private def markedLetters {n : ℕ} (xs : List (Fin n)) : List (Σ i, MarkedFactor n i) :=
  xs.flatMap fun x => [⟨false, FreeGroup.of x⟩, ⟨true, FreeGroup.of ()⟩]

private theorem markedLetters_chain {n : ℕ} (xs : List (Fin n)) :
    (markedLetters xs).IsChain fun l l' => l.1 ≠ l'.1 := by
  induction xs with
  | nil => simp [markedLetters]
  | cons x xs ih => cases xs <;> simp_all [markedLetters, List.isChain_cons]

/-- The marker word is reduced because successive letters are in different factors. -/
private def markedWord (n : ℕ) : Word (MarkedFactor n) where
  toList := markedLetters (List.finRange n)
  ne_one := by
    intro l hl
    obtain ⟨x, _, hx⟩ := List.mem_flatMap.mp hl
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl <;> exact FreeGroup.of_ne_one _
  chain_ne := markedLetters_chain _

/-- Extend the original automorphism to fix the separator. -/
private def markedAut (n : ℕ) : MulAut (FreeGroup (Fin n)) →* MulAut (CoprodI (MarkedFactor n)) :=
  coprodAut.comp (MonoidHom.mulSingle (fun i => MulAut (MarkedFactor n i)) false)

private theorem markedAut_eq_one (n : ℕ) (a : MulAut (FreeGroup (Fin n)))
    (ha : markedAut n a (markedWord n).prod = (markedWord n).prod) : a = 1 := by
  classical
  let b : ∀ i, MulAut (MarkedFactor n i) := Pi.mulSingle false a
  have hw : mapWord b (markedWord n) = markedWord n :=
    (Word.equiv (M := MarkedFactor n)).symm.injective ((mapWord_prod b _).trans ha)
  have hl := congrArg Word.toList hw
  change (markedWord n).toList.map (fun l => ⟨l.1, b l.1 l.2⟩) = (markedWord n).toList at hl
  conv_rhs at hl => rw [← List.map_id (markedWord n).toList]
  apply DFunLike.ext
  intro x
  suffices he : (a.toMonoidHom : FreeGroup (Fin n) →* FreeGroup (Fin n)) = MonoidHom.id _ by
    exact DFunLike.congr_fun he x
  ext i
  have hi : (⟨false, FreeGroup.of i⟩ : Σ j, MarkedFactor n j) ∈ (markedWord n).toList :=
    List.mem_flatMap.mpr ⟨i, List.mem_finRange i, by simp⟩
  have h := List.map_inj_left.mp hl _ hi
  simpa [b] using h

/-- The two marked free factors and the last generator give a finite free basis. -/
private def ambientBasis (n : ℕ) :
    FreeGroupBasis (Σ i, Two (Σ _ : Bool, Σ j, Two (Fin n) Unit j) Unit i)
      (Coprod (CoprodI fun _ : Bool => CoprodI (MarkedFactor n)) (FreeGroup Unit)) :=
  let marked : FreeGroupBasis (Σ j, Two (Fin n) Unit j) (CoprodI (MarkedFactor n)) :=
    FreeGroupBasis.coprodI fun j => FreeGroupBasis.ofFreeGroup (Two (Fin n) Unit j)
  let base := FreeGroupBasis.coprodI (fun _ : Bool => marked)
  let parts : ∀ i, FreeGroupBasis (Two (Σ _ : Bool, Σ j, Two (Fin n) Unit j) Unit i)
      (Two (CoprodI fun _ : Bool => CoprodI (MarkedFactor n)) (FreeGroup Unit) i)
    | false => base
    | true => FreeGroupBasis.ofFreeGroup Unit
  (FreeGroupBasis.coprodI parts).map (twoCoprod _ _).symm

/--
**Free products of subgroups of $\mathrm{Aut}(F_n)$ embed in some $\mathrm{Aut}(F_m)$.** For
every natural number $n \ge 2$ and all subgroups $G$ and $H$ of the automorphism group
$\mathrm{Aut}(F_n)$ of the free group $F_n$ of rank $n$, there are a natural number $m$ and an
injective group homomorphism from the free product $G \ast H$ to $\mathrm{Aut}(F_m)$.

Jayadevan constructs, for subgroups $G \le \mathrm{Aut}(F_n)$ and $H \le \mathrm{Aut}(F_k)$ with
no finite-generation hypothesis, an embedding of $G \ast H$ in $\mathrm{Aut}(F_{n+k+3})$; the
Kourovka Notebook (21st issue) answers 18.11 "Yes, it is true" (AI solution confirmed by V. G.
Bardakov).

Source: E.
I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka Notebook, 21st
issue, arXiv:1401.0300v49 (2026), Problem 18.11 (V. G. Bardakov); resolution: A. Jayadevan, Free
products of free-group automorphism groups: a finite-rank embedding by separating cocycles,
preprint, Zenodo record 22722085 (2026), abstract (for G ≤ Aut(F_n), H ≤ Aut(F_m), G ∗ H embeds in
Aut(F_{n+m+3}); no finite-generation hypothesis); the Kourovka Notebook (21st issue) marks 18.11
solved (Yes, it is true; AI solution confirmed by V. G. Bardakov),
https://zenodo.org/records/22722085.
-/
public theorem freeProductAutFreeGroupEmbeds_holds : freeProductAutFreeGroupEmbeds := by
  classical
  intro n _ G H
  let f : ∀ i, Two G H i →* MulAut (CoprodI (MarkedFactor n))
    | false => (markedAut n).comp G.subtype
    | true => (markedAut n).comp H.subtype
  let u : Bool → CoprodI (MarkedFactor n) := fun _ => (markedWord n).prod
  have hu : ∀ i (a : Two G H i), f i a (u i) = u i → a = 1 := by
    intro i
    cases i
    · intro a ha
      exact Subtype.ext (markedAut_eq_one n a.val ha)
    · intro a ha
      exact Subtype.ext (markedAut_eq_one n a.val ha)
  let e := ((ambientBasis n).reindex (Fintype.equivFin _)).repr
  exact ⟨_, (MulAut.congr e).toMonoidHom.comp
    ((CoprodI.lift (factorTwist f u)).comp (twoCoprod G H).toMonoidHom),
    (MulAut.congr e).injective.comp <|
      (factorTwist_injective f u hu).comp (twoCoprod G H).injective⟩

end MathlibExt.GroupTheory.FreeProductAutFreeGroupEmbeddingKourovka18Problem11Wanted
