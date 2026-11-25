/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.ModelTheory.ZeroOneLaw
public import Mathlib.ModelTheory.Graph

/-!
# Tests for the zero-one law for first-order logic

The language of graphs (one binary relation symbol) satisfies the hypotheses of the law, which
then applies to every sentence. In general the law says that the proportion of structures
satisfying a sentence converges, that its limit is never `1/2`, and that exactly one of `φ` and
`∼φ` has limit `1`. For a language with one nullary relation symbol `P`, which the hypotheses
exclude, the proportion of structures satisfying `P` is `1/2` on every domain, so the conclusion
fails there.
-/

@[expose] public section

namespace MathlibExtTest.ModelTheory.ZeroOneLaw

open FirstOrder FirstOrder.Language Filter Topology MathlibExt.ModelTheory.ZeroOneLawWanted

/-- The language of graphs has finitely many symbols. -/
instance finite_graph_symbols : Finite Language.graph.Symbols := by
  refine Finite.of_injective (β := Unit) (fun _ => ()) ?_
  rintro (⟨_, ⟨⟩⟩ | ⟨_, ⟨⟩⟩) (⟨_, ⟨⟩⟩ | ⟨_, ⟨⟩⟩) _
  rfl

/-- The language of graphs has no nullary relation symbol. -/
instance isEmpty_graph_relations_zero : IsEmpty (Language.graph.Relations 0) :=
  ⟨fun r => nomatch r⟩

-- The law for the language of graphs.
example (φ : Language.graph.Sentence) :
    Tendsto (Language.graph.satFraction φ) atTop (𝓝 0) ∨
      Tendsto (Language.graph.satFraction φ) atTop (𝓝 1) :=
  zero_one_law Language.graph φ

/-- The proportion of structures satisfying a sentence converges. -/
theorem exists_tendsto (L : Language) [L.IsRelational] [IsEmpty (L.Relations 0)]
    [Finite L.Symbols] (φ : L.Sentence) : ∃ c, Tendsto (L.satFraction φ) atTop (𝓝 c) :=
  (zero_one_law L φ).elim (fun h => ⟨0, h⟩) fun h => ⟨1, h⟩

/-- No sentence has limiting proportion `1/2`. -/
theorem not_tendsto_half (L : Language) [L.IsRelational] [IsEmpty (L.Relations 0)]
    [Finite L.Symbols] (φ : L.Sentence) : ¬Tendsto (L.satFraction φ) atTop (𝓝 (1 / 2)) := by
  intro h
  rcases zero_one_law L φ with h' | h' <;> have := tendsto_nhds_unique h h' <;> norm_num at this

/-- Exactly one of `φ` and `∼φ` has limiting proportion `1`. -/
theorem tendsto_one_iff_not_tendsto_one_not (L : Language) [L.IsRelational]
    [IsEmpty (L.Relations 0)] [Finite L.Symbols] (φ : L.Sentence) :
    Tendsto (L.satFraction φ) atTop (𝓝 1) ↔ ¬Tendsto (L.satFraction (∼φ)) atTop (𝓝 1) := by
  have hnot : Tendsto (L.satFraction (∼φ)) atTop (𝓝 1) ↔
      Tendsto (L.satFraction φ) atTop (𝓝 0) := by
    rw [show L.satFraction (∼φ) = fun n => 1 - L.satFraction φ n from
      funext (L.satFraction_not φ)]
    constructor
    · intro h
      simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub h
    · intro h
      simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub h
  rw [hnot]
  constructor
  · intro h1 h0
    have := tendsto_nhds_unique h0 h1
    norm_num at this
  · intro h0
    exact (zero_one_law L φ).resolve_left h0

-- A language with a nullary relation symbol, excluded by the hypotheses.

/-- The relation symbols of `nullaryLang`: one symbol of arity `0`. -/
def nullaryRel : ℕ → Type
  | 0 => Unit
  | _ + 1 => Empty

/-- A language with a single nullary relation symbol and no function symbols. -/
def nullaryLang : Language := ⟨fun _ => Empty, nullaryRel⟩

instance nullaryLang_isRelational : nullaryLang.IsRelational :=
  fun _ => (inferInstance : IsEmpty Empty)

instance nullaryLang_finite : Finite nullaryLang.Symbols := by
  refine Finite.of_injective (β := Unit) (fun _ => ()) ?_
  rintro (⟨_, ⟨⟩⟩ | ⟨_ | _, r⟩) (⟨_, ⟨⟩⟩ | ⟨_ | _, r'⟩) _ <;>
    first | rfl | exact r.elim | exact r'.elim

/-- The nullary relation symbol of `nullaryLang`. -/
def pSym : nullaryLang.Relations 0 := ()

/-- The propositional constant `P` of `nullaryLang`, as a sentence. -/
def nullaryP : nullaryLang.Sentence := Relations.formula pSym Fin.elim0

/-- A structure for `nullaryLang` is determined by the truth value of `P`. -/
theorem relMap_injective (M : Type) :
    Function.Injective fun S : nullaryLang.Structure M => S.RelMap pSym Fin.elim0 := by
  rintro ⟨f₁, r₁⟩ ⟨f₂, r₂⟩ h
  have hf : @f₁ = @f₂ := by
    funext n f
    exact isEmptyElim f
  have hr : @r₁ = @r₂ := by
    funext n R xs
    match n, R with
    | 0, () =>
      obtain rfl : xs = Fin.elim0 := Subsingleton.elim _ _
      exact h
    | _ + 1, R => exact R.elim
  subst hf
  subst hr
  rfl

/-- Structures for `nullaryLang` are truth values of `P`. -/
noncomputable def structureEquivProp (M : Type) : nullaryLang.Structure M ≃ Prop :=
  Equiv.ofBijective _ ⟨relMap_injective M, fun p =>
    ⟨⟨fun f => isEmptyElim f, fun {n} R _ => match n, R with | 0, () => p⟩, rfl⟩⟩

/-- On every domain, `P` holds in exactly half of the structures. -/
theorem satFraction_nullaryP (n : ℕ) : nullaryLang.satFraction nullaryP n = 1 / 2 := by
  have hset : {S : nullaryLang.Structure (Fin n) |
      @Sentence.Realize nullaryLang (Fin n) S nullaryP} =
      structureEquivProp (Fin n) ⁻¹' {True} := by
    ext S
    simp only [Set.mem_preimage, Set.mem_singleton_iff, eq_iff_iff, iff_true]
    exact iff_of_eq (congrArg (@Structure.RelMap nullaryLang (Fin n) S 0 pSym)
      (Subsingleton.elim _ _))
  unfold satFraction
  rw [hset, Set.ncard_preimage_of_injective_subset_range (structureEquivProp (Fin n)).injective
    (by simp), Set.ncard_singleton, Nat.card_congr (structureEquivProp (Fin n)),
    Nat.card_eq_fintype_card, Fintype.card_prop]
  norm_num

/-- The hypothesis that no relation symbol is nullary cannot be dropped: the proportion of
structures satisfying `P` is `1/2` on every domain, so it tends neither to `0` nor to `1`. -/
theorem not_zero_one_nullaryP :
    ¬(Tendsto (nullaryLang.satFraction nullaryP) atTop (𝓝 0) ∨
      Tendsto (nullaryLang.satFraction nullaryP) atTop (𝓝 1)) := by
  have h : Tendsto (nullaryLang.satFraction nullaryP) atTop (𝓝 (1 / 2)) := by
    rw [show nullaryLang.satFraction nullaryP = fun _ => 1 / 2 from
      funext satFraction_nullaryP]
    exact tendsto_const_nhds
  rintro (h' | h') <;> have := tendsto_nhds_unique h h' <;> norm_num at this

end MathlibExtTest.ModelTheory.ZeroOneLaw
