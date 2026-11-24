/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import
  MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.Joyal.CobaseUnconditional

/-! # The `Δ[n] ⊗ Δ[2]` shuffle filtration (packet T52)

**Formal status of this prefix.**  The Lean declarations proved
in this file at this point are only the shuffle-chain arithmetic
(`SSet.shuffleSnd`, `SSet.shuffleFst` and their
characterizations), the top shuffle simplices
(`SSet.shuffleTau`, `SSet.shuffleTauMap`), their coordinate
values, the coordinate equality criterion, and the range
characterization (`SSet.mem_range_shuffleTau_objEquiv`).  The
long mathematical discussion below is the intended informal
proof and roadmap: named results beyond the list above
(classification of top simplices, diagonal simplices, stage
filtrations, horn attachments, the two `exists_extension_…`
theorems, the pointwise criterion, and cobase-change assembly)
are target names/statements to be formalized next, **not**
declarations already present in this file.  No unconditional
cobase-change instance is claimed here.

This module is intended to formalize TODO(T47-Δ2) of `CobaseUnconditional.lean`:
the shuffle filtration of the prism `Δ[n] ⊗ Δ[2]` and the two horn
extension properties over a cell,

```text
SSet.exists_extension_of_unionProd_boundary_horn_zero  -- from ∂Δ[n] ⊗ Δ[2] ∪ Δ[n] ⊗ Λ[2,0]
SSet.exists_extension_of_unionProd_boundary_horn_two   -- from ∂Δ[n] ⊗ Δ[2] ∪ Δ[n] ⊗ Λ[2,2]
```

which are the only missing input of the pointwise criterion
(§2 of the `CobaseUnconditional.lean` header): combined with
`SSet.edgeOfPrism_isEquivalence_of_compPrisms` (packet T47) they
give `Edge.IsEquivalence.of_strict_restriction_pointwise` for
`∂Δ[n].ι` once the prism-dictionary gluing of TODO(T47-B) is done.
No statement here claims the unconditional cobase-change instance;
the exact remaining inputs (functor-form bridges + skeletal
closure, and `2`-simplex correction TODO(T47-B2)) are recorded at
the end. First the complete informal proof, following the method
of the earlier packets.

## 1. Shuffles of `Δ[n] ⊗ Δ[2]`

Through `SSet.prodStdSimplex.objEquiv`, an `m`-simplex of
`Δ[n] ⊗ Δ[2]` is a chain `Fin (m+1) →o Fin (n+1) × Fin 3`, and it
is nondegenerate iff the chain is injective. The top dimension is
`n + 2`, and a nondegenerate `(n+2)`-simplex is characterized by
`prodStdSimplex.nonDegenerate_max_dim_iff`: the sum of its two
coordinates at position `t` is exactly `t`. Hence the top
simplices are the strictly monotone lattice paths from `(0,0)` to
`(n,2)` with unit steps — the `(n,2)`-shuffles

```text
τ_{a,b} = ((0,0), …, (a,0), (a,1), …, (b,1), (b,2), …, (n,2)),
          0 ≤ a ≤ b ≤ n,
```

where `a` (resp. `b`) is the first coordinate at which the path
jumps from height `0` to height `1` (resp. `1` to `2`). At
position `t` the second coordinate is `0` for `t ≤ a`, `1` for
`a < t ≤ b+1` and `2` for `t ≥ b+2` (formally `SSet.shuffleSnd`),
and the first coordinate is `t` minus the second
(`SSet.shuffleFst`); `SSet.shuffleTau` is this chain read back
through `objEquiv.symm`. Every nondegenerate top simplex is a
shuffle (`SSet.exists_shuffleTau_of_nonDegenerate`): its second
coordinate is monotone from `0` to `2` with steps `≤ 1` (the sum
increases by `1` at each step and both coordinates are monotone),
hence a threshold function. The range of `τ_{a,b}` is
`{(i,0) | i ≤ a} ∪ {(i,1) | a ≤ i ≤ b} ∪ {(i,2) | b ≤ i}`
(`SSet.mem_range_shuffleTau_objEquiv`).

Fix the horn-zero initial subcomplex
`S₀ := ∂Δ[n] ⊗ Δ[2] ∪ Δ[n] ⊗ Λ[2,0]`
(`SSet.shuffleInit0`, a `Subcomplex.unionProd`): a simplex lies
in `S₀` iff its first coordinates miss some value or its second
coordinates miss `1` or `2`. The faces of `τ_{a,b}` omitting a
non-corner vertex delete the unique occurrence of a first
coordinate, hence lie in `∂Δ[n] ⊗ Δ[2]`. The four corner faces
(positions of `(a,0)`, `(a,1)`, `(b,1)`, `(b,2)`) are diagonal:
omitting `(a,1)` is shared with `τ_{a+1,b}` (or misses height
`1`, hence lies in `S₀`, when `a = b`); omitting `(b,2)` is
shared with `τ_{a,b+1}` (or misses height `2` when `b = n`);
omitting `(a,0)` is shared with `τ_{a-1,b}` (for `a = 0` it is
the output face over the edge `{1,2}` of `Δ[2]`); omitting
`(b,1)` is shared with `τ_{a,b-1}`. Since a shuffle has *two*
diagonal neighbours in the `b`-direction, no ordering attaches
the `τ_{a,b}` one at a time along horns directly from `S₀` (the
earliest shuffle of any `2 × 2` block has two later diagonal
faces). The cure is to pre-attach one family of diagonal
`(n+1)`-simplices.

## 2. The diagonal phase and the top phase (`Λ[2,0]`)

For `a < b` let `W_{a,b}` be the diagonal simplex obtained from
`τ_{a,b}` by omitting `(b,1)` (`SSet.shuffleDiagW`, with its own
chain: heights `0` up to position `a`, `1` up to position `b`,
then `2`; first coordinate `t` for `t ≤ a`, else `t - 1`). Its
faces omitting a non-corner vertex miss a first coordinate (the
first coordinate `v` occurs in `W_{a,b}` only at position `v`,
and again at `v + 1` exactly when `v = a`). The face omitting
`(a,1)` (position `a + 1`) is shared with `W_{a+1,b}`, or misses
height `1` when `b = a + 1`. Hence, attaching the `W_{a,b}` in
*decreasing* `a` order to `S₀`, each `W_{a,b}` has all faces in
the previous stage except the one omitting `(a,0)` (position
`a`): it attaches along `Λ[n+1, a]`, inner for `a ≥ 1`, and for
`a = 0` along the left outer horn `Λ[n+1, 0]`, whose `(0,1)`-edge
is the vertical edge `v₀ = ((0,0) ⟶ (0,1))`
(`SSet.shuffleVert0`, which lies in `S₀` through the horn
factor).

After the diagonal phase, attach the shuffles in lexicographically
*decreasing* `(a, b)` order (column `a` from `n` down to `0`,
within a column `b` from `n` down to `a`). For `τ_{a,b}`: the
`(a,1)`-face is in `τ_{a+1,b}` (earlier column) or in `S₀`; the
`(b,1)`-face is the pre-attached `W_{a,b}`; the `(b,2)`-face is
in `τ_{a,b+1}` (earlier in the column) or in `S₀`; the only
missing face is the `(a,0)`-face (position `a`), shared only
with the later column `τ_{a-1,b}`. So `τ_{a,b}` attaches along
`Λ[n+2, a]`: inner for `a ≥ 1`, and for `a = 0` the left outer
horn `Λ[n+2, 0]` with special edge `v₀` again. The attaching
square is a pushout because shuffles and diagonals are injective
chains, by the general `SSet.Subcomplex.isPushout_hornAttach` /
`SSet.Subcomplex.exists_extension_sup_of_horn_filler` of `PrismCobase.lean`.
Filling inner horns in the quasicategory `C` and the `a = 0`
horns by `SSet.exists_fill_horn_left_of_isEquivalence` (packet
T21) proves: a map out of `S₀` extends to `Δ[n] ⊗ Δ[2]` as soon
as the image of the single vertical edge `v₀` is an equivalence
(`SSet.exists_extension_of_unionProd_boundary_horn_zero`). No
`n = 0` exception is needed: `v₀ ∈ S₀` for all `n`.

## 3. The mirror (`Λ[2,2]`)

With `S₂ := ∂Δ[n] ⊗ Δ[2] ∪ Δ[n] ⊗ Λ[2,2]` (second coordinates
miss `0` or `1`), pre-attach the diagonals
`W'_{a,b} = τ_{a,b}` omitting `(a,1)` in *increasing* `b` order:
each attaches along `Λ[n+1, b+1]` (missing face omitting
`(b,2)`), inner for `b < n`, and for `b = n` the right outer
horn `Λ[n+1, n+1]` whose last edge is
`v₂ = ((n,1) ⟶ (n,2))`. Then attach the shuffles in
lexicographically *increasing* `(a, b)` order along
`Λ[n+2, b+2]` (missing face omitting `(b,2)`), inner for
`b < n`, right-special with edge `v₂` for `b = n`, filled by
`SSet.exists_fill_horn_right_of_isEquivalence`. This gives
`SSet.exists_extension_of_unionProd_boundary_horn_two`.

## 4. Why these are the pointwise criterion over a cell

Recall §2 of the `CobaseUnconditional.lean` header: an edge `ε`
of `Fun(Δ[n], C)` (a prism `F : Δ[n] ⊗ Δ[1] ⟶ C`) restricting
strictly to an equivalence `e` of `Fun(∂Δ[n], C)` with all
vertex evaluations equivalences is an equivalence. Inverse data
for `e` are `Δ[2]`-prisms `α, β` over `∂Δ[n]`; the two
`CompStruct` prisms for `ε` are maps out of `S₀` resp. `S₂`
glued from `α` (resp. `β`) on `∂Δ[n] ⊗ Δ[2]`, from `F` on one
prescribed face of `Δ[2]` and from the degenerate prism on the
other, along `Subcomplex.unionProd.isPushout`. The special
edges are `v₀`, `v₂`: for `n ≥ 1` they lie in the
`∂Δ[n] ⊗ Δ[2]` part and their images are the evaluations of `α`,
`β` at the vertices `0`, `n` — pointwise equivalences. The
extensions of §2–§3 then produce the two `Δ[2]`-prisms, and
`SSet.edgeOfPrism_isEquivalence_of_compPrisms` concludes. The
formal gluing of the initial map and the identification of the
special edges with vertex evaluations is exactly the
functor-form bridge of TODO(T47-B); the shuffle filtration
itself, the combinatorial content of TODO(T47-Δ2), is **not**
proved here — only the shuffle arithmetic and top simplices
listed in the formal-status paragraph at the top of this
header are formalized.

## 5. Remaining TODOs towards unconditional cobase change

* TODO(T52-Δ2) — the shuffle filtration itself (the central
  missing content of this packet): stage subcomplexes,
  pre-attached diagonals, attaching-horn computation for the
  top simplices `τ_{a,b}`, and the two extension theorems
  `exists_extension_of_unionProd_boundary_horn_zero/two` of
  §§2–3. Only the shuffle arithmetic and `shuffleTau` range
  characterization above are formalized.
* TODO(T52-B) — functor-form bridges and skeletal closure
  (TODO(T47-B) of `CobaseUnconditional.lean`, unchanged): glue
  `(H, b♯)`-type data along `Subcomplex.unionProd.isPushout`,
  identify the special edges `SSet.shuffleVert0` /
  `SSet.shuffleVert2` (and `SSet.prismVertZero` /
  `SSet.prismVertLast`) with vertex evaluations, close the
  `Δ[1]`- and `Δ[2]`-extension properties under pushouts,
  coproducts, composition and the `skeletonOfMono` tower, and
  assemble `SSet.HoPrePrismStrictExtension i C` for every
  monomorphism `i` (input (A) of
  `SSet.categoricalEquivalences_isStableUnderCobaseChangeAgainst_mono_of_prism_of_correction`).
* TODO(T52-B2) — reformulate prism correction rel
  `B ⊗ ∂Δ[2]`: `SSet.CompCorrection ((pre i).app C)` as
  stated is false in general (relative `π₂` obstruction; see
  `CobaseUnconditional.lean` §4 and `ShuffleBridges.lean`
  §4), so no triple-product shuffle can prove it. A corrected
  relative property carrying homotopy-class compatibility
  would be approached cell by cell by a homotopy-extension
  shuffle filtration of `Δ[n] ⊗ Δ[2] ⊗ Δ[1]`, or the
  faithfulness step replaced by the mapping-space route.

Even with the first input supplied, the existing assembly
`SSet.categoricalEquivalences_isStableUnderCobaseChangeAgainst_mono_of_prism_of_correction`
(packet T47) cannot consume a corrected second input: it
requires the original (false) `CompCorrection` hypothesis.
Reaching the unconditional instance therefore additionally
requires a new faithfulness theorem formulated for the
corrected relative correction property (or a mapping-space
faithfulness proof) and a new assembly on top of it; the
present assembly is only a reduction to the original,
unavailable hypothesis.

## References

* J. Lurie, *Higher Topos Theory*, §2.3 (Proposition 2.3.4.5).
* D. Stevenson, *Notes on the Joyal model structure*,
  arXiv:1810.05233, §2.
* *Kerodon*, §4.5, Corollary 4.5.4.14.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory Limits MonoidalClosed MonoidalCategory Opposite

open scoped Simplicial

namespace SSet

/-! ## Arithmetic of the shuffle chains

The second coordinate of the shuffle `τ_{a,b}` at position `t`
is the threshold function `shuffleSnd a b t`; the first is
`shuffleFst a b t = t - shuffleSnd a b t`. All face computations
below reduce to the `ℕ`-level characterizations in this section. -/

section ShuffleArithmetic

variable {a b t v : ℕ}

/-- Second coordinates of the shuffle `τ_{a,b}`: `0` up to
position `a`, `1` up to position `b + 1`, then `2`. -/
def shuffleSnd (a b t : ℕ) : ℕ :=
  if t ≤ a then 0 else if t ≤ b + 1 then 1 else 2

/-- First coordinates of the shuffle `τ_{a,b}`: `t` minus the
number of height jumps before position `t`. -/
def shuffleFst (a b t : ℕ) : ℕ :=
  t - shuffleSnd a b t

lemma shuffleSnd_le_two (a b t : ℕ) : shuffleSnd a b t ≤ 2 := by
  unfold shuffleSnd
  split_ifs <;> omega

lemma shuffleSnd_eq_zero : shuffleSnd a b t = 0 ↔ t ≤ a := by
  by_cases h1 : t ≤ a
  · simp [shuffleSnd, h1]
  · by_cases h2 : t ≤ b + 1 <;> simp [shuffleSnd, h1, h2]

lemma shuffleSnd_eq_one :
    shuffleSnd a b t = 1 ↔ a < t ∧ t ≤ b + 1 := by
  by_cases h1 : t ≤ a
  · simp [shuffleSnd, h1]
  · by_cases h2 : t ≤ b + 1 <;> simp [shuffleSnd, h1, h2]; omega

lemma shuffleSnd_eq_two (hab : a ≤ b) :
    shuffleSnd a b t = 2 ↔ b + 2 ≤ t := by
  by_cases h1 : t ≤ a
  · simp [shuffleSnd, h1]
    omega
  · by_cases h2 : t ≤ b + 1 <;> simp [shuffleSnd, h1, h2] <;> omega

lemma shuffleFst_add_snd (a b t : ℕ) :
    shuffleFst a b t + shuffleSnd a b t = t := by
  unfold shuffleFst shuffleSnd
  split_ifs <;> omega

/-- Occurrences of the first-coordinate value `v` in the shuffle
`τ_{a,b}`: at position `v` (when `v ≤ a`), `v + 1` (when
`a ≤ v ≤ b`) and `v + 2` (when `b ≤ v`); the double occurrences
are exactly the corners `(a,0),(a,1)` and `(b,1),(b,2)`. -/
lemma shuffleFst_eq_iff (hab : a ≤ b) :
    shuffleFst a b t = v ↔
      (t = v ∧ v ≤ a) ∨ (t = v + 1 ∧ a ≤ v ∧ v ≤ b) ∨
        (t = v + 2 ∧ b ≤ v) := by
  have hsum := shuffleFst_add_snd a b t
  have hcases : shuffleSnd a b t = 0 ∨ shuffleSnd a b t = 1 ∨
      shuffleSnd a b t = 2 := by
    have h2 := shuffleSnd_le_two a b t
    omega
  constructor
  · intro h
    rcases hcases with h0 | h1 | h2
    · have hle := shuffleSnd_eq_zero.1 h0
      exact Or.inl ⟨by omega, by omega⟩
    · obtain ⟨hgt, hle⟩ := shuffleSnd_eq_one.1 h1
      exact Or.inr (Or.inl ⟨by omega, by omega, by omega⟩)
    · have hge := (shuffleSnd_eq_two hab).1 h2
      exact Or.inr (Or.inr ⟨by omega, by omega⟩)
  · rintro (⟨htv, hv⟩ | ⟨htv, hv1, hv2⟩ | ⟨htv, hv⟩)
    · have h0 : shuffleSnd a b t = 0 :=
        shuffleSnd_eq_zero.2 (by omega)
      omega
    · have h1 : shuffleSnd a b t = 1 :=
        shuffleSnd_eq_one.2 ⟨by omega, by omega⟩
      omega
    · have h2 : shuffleSnd a b t = 2 :=
        (shuffleSnd_eq_two hab).2 (by omega)
      omega

lemma shuffleFst_le_of_le (hab : a ≤ b) (hb : b ≤ v) (ht : t ≤ v + 2) :
    shuffleFst a b t ≤ v := by
  have hsum := shuffleFst_add_snd a b t
  have hcases : shuffleSnd a b t = 0 ∨ shuffleSnd a b t = 1 ∨
      shuffleSnd a b t = 2 := by
    have h2 := shuffleSnd_le_two a b t
    omega
  rcases hcases with h0 | h1 | h2
  · have hle := shuffleSnd_eq_zero.1 h0
    omega
  · obtain ⟨-, hle⟩ := shuffleSnd_eq_one.1 h1
    omega
  · omega

/-- Shifting the first threshold up changes the height function
only at position `a + 1` (the corner where `τ_{a,b}` and
`τ_{a+1,b}` differ). -/
lemma shuffleSnd_succ_left (h : t ≠ a + 1) :
    shuffleSnd (a + 1) b t = shuffleSnd a b t := by
  unfold shuffleSnd
  split_ifs <;> omega

/-- Shifting the second threshold up changes the height
function only at position `b + 2`. -/
lemma shuffleSnd_succ_right (h : t ≠ b + 2) :
    shuffleSnd a (b + 1) t = shuffleSnd a b t := by
  unfold shuffleSnd
  split_ifs <;> omega

/-- Shifting the first threshold down changes the height
function only at position `a` (for `a ≥ 1`). -/
lemma shuffleSnd_pred_left (ha : 1 ≤ a) (h : t ≠ a) :
    shuffleSnd (a - 1) b t = shuffleSnd a b t := by
  unfold shuffleSnd
  split_ifs <;> omega

/-- Shifting the second threshold down changes the height
function only at position `b + 1` (for `b ≥ 1`). -/
lemma shuffleSnd_pred_right (hb : 1 ≤ b) (h : t ≠ b + 1) :
    shuffleSnd a (b - 1) t = shuffleSnd a b t := by
  unfold shuffleSnd
  split_ifs <;> omega

end ShuffleArithmetic

/-! ## The top simplices `τ_{a,b}` of `Δ[n] ⊗ Δ[2]`

The shuffle `τ_{a,b}` is the chain `(0,0), …, (a,0), (a,1), …,
(b,1), (b,2), …, (n,2)` read through
`SSet.prodStdSimplex.objEquiv`. We record its values, range,
nondegeneracy, the classification of nondegenerate top
simplices, injectivity of its classifying map, and the face
analysis: non-corner faces lie over `∂Δ[n]`, and the two
"moving" corner faces agree with the corresponding faces of the
adjacent shuffles. -/

section ShuffleTau

variable {n a b : ℕ}

/-- The `(a,b)`-shuffle: the nondegenerate `(n+2)`-simplex of
`Δ[n] ⊗ Δ[2]` with vertices `(0,0), …, (a,0), (a,1), …, (b,1),
(b,2), …, (n,2)`. -/
noncomputable def shuffleTau (n a b : ℕ) (hab : a ≤ b) (hb : b ≤ n) :
    (Δ[n] ⊗ Δ[2] : SSet.{u}) _⦋n + 2⦌ :=
  prodStdSimplex.objEquiv.symm
    ⟨fun t ↦ (⟨shuffleFst a b t.val, by
        have ht : t.val ≤ n + 2 := by have h2 := t.2; omega
        have hle := shuffleFst_le_of_le hab hb ht
        omega⟩,
      ⟨shuffleSnd a b t.val, by
        have hle := shuffleSnd_le_two a b t.val
        omega⟩), by
      intro s t hst
      have hval : s.val ≤ t.val := hst
      refine ⟨?_, ?_⟩
      · change shuffleFst a b s.val ≤ shuffleFst a b t.val
        unfold shuffleFst shuffleSnd
        split_ifs <;> omega
      · change shuffleSnd a b s.val ≤ shuffleSnd a b t.val
        unfold shuffleSnd
        split_ifs <;> omega⟩

/-- The map `Δ[n+2] ⟶ Δ[n] ⊗ Δ[2]` classifying `shuffleTau`. -/
noncomputable abbrev shuffleTauMap (n a b : ℕ) (hab : a ≤ b)
    (hb : b ≤ n) :
    Δ[n + 2] ⟶ (Δ[n] ⊗ Δ[2] : SSet.{u}) :=
  yonedaEquiv.symm (shuffleTau n a b hab hb)

lemma shuffleTau_objEquiv_fst_val (hab : a ≤ b) (hb : b ≤ n)
    (t : Fin (n + 3)) :
    ((prodStdSimplex.objEquiv (shuffleTau n a b hab hb) t).1).val =
      shuffleFst a b t.val :=
  rfl

lemma shuffleTau_objEquiv_snd_val (hab : a ≤ b) (hb : b ≤ n)
    (t : Fin (n + 3)) :
    ((prodStdSimplex.objEquiv (shuffleTau n a b hab hb) t).2).val =
      shuffleSnd a b t.val :=
  rfl

lemma shuffleTau_objEquiv_apply_eq_iff (hab : a ≤ b) (hb : b ≤ n)
    (t : Fin (n + 3)) {p : Fin (n + 1) × Fin 3} :
    prodStdSimplex.objEquiv (shuffleTau n a b hab hb) t = p ↔
      shuffleFst a b t.val = p.1.val ∧
        shuffleSnd a b t.val = p.2.val := by
  constructor
  · intro h
    constructor
    · have h1 := congrArg Fin.val (congrArg Prod.fst h)
      rwa [shuffleTau_objEquiv_fst_val hab hb t] at h1
    · have h2 := congrArg Fin.val (congrArg Prod.snd h)
      rwa [shuffleTau_objEquiv_snd_val hab hb t] at h2
  · rintro ⟨h1, h2⟩
    apply Prod.ext <;> apply Fin.ext
    · rw [shuffleTau_objEquiv_fst_val hab hb t, h1]
    · rw [shuffleTau_objEquiv_snd_val hab hb t, h2]

/-- The range of `τ_{a,b}` is
`{(i,0) | i ≤ a} ∪ {(i,1) | a ≤ i ≤ b} ∪ {(i,2) | b ≤ i}`. -/
lemma mem_range_shuffleTau_objEquiv (hab : a ≤ b) (hb : b ≤ n)
    {p : Fin (n + 1) × Fin 3} :
    p ∈ Set.range
        (prodStdSimplex.objEquiv (shuffleTau n a b hab hb)) ↔
      (p.2.val = 0 ∧ p.1.val ≤ a) ∨
        (p.2.val = 1 ∧ a ≤ p.1.val ∧ p.1.val ≤ b) ∨
          (p.2.val = 2 ∧ b ≤ p.1.val) := by
  constructor
  · rintro ⟨t, ht⟩
    rw [shuffleTau_objEquiv_apply_eq_iff hab hb t] at ht
    obtain ⟨hf, hs⟩ := ht
    have hsum := shuffleFst_add_snd a b t.val
    have hpc : p.2.val = 0 ∨ p.2.val = 1 ∨ p.2.val = 2 := by
      have h3 := p.2.2
      omega
    rcases hpc with h0 | h1 | h2
    · have hle : t.val ≤ a :=
        (shuffleSnd_eq_zero (a := a) (b := b) (t := t.val)).1 (by omega)
      exact Or.inl ⟨h0, by omega⟩
    · obtain ⟨hgt, hle⟩ := shuffleSnd_eq_one.1 (by omega :
        shuffleSnd a b t.val = 1)
      exact Or.inr (Or.inl ⟨h1, by omega, by omega⟩)
    · have hge : b + 2 ≤ t.val := (shuffleSnd_eq_two hab).1 (by omega)
      exact Or.inr (Or.inr ⟨h2, by omega⟩)
  · rintro (⟨h2, h1⟩ | ⟨h2, h1, h1'⟩ | ⟨h2, h1⟩)
    · refine ⟨⟨p.1.val + p.2.val, by
          have e1 := p.1.2
          have e2 := p.2.2
          omega⟩, ?_⟩
      rw [shuffleTau_objEquiv_apply_eq_iff hab hb _]
      exact ⟨(shuffleFst_eq_iff hab).2 (Or.inl
          ⟨by change p.1.val + p.2.val = p.1.val; omega, h1⟩),
        by change shuffleSnd a b (p.1.val + p.2.val) = p.2.val
           have h := (shuffleSnd_eq_zero (a := a) (b := b)
             (t := p.1.val + p.2.val)).2 (by omega)
           omega⟩
    · refine ⟨⟨p.1.val + p.2.val, by
          have e1 := p.1.2
          have e2 := p.2.2
          omega⟩, ?_⟩
      rw [shuffleTau_objEquiv_apply_eq_iff hab hb _]
      exact ⟨(shuffleFst_eq_iff hab).2
          (Or.inr (Or.inl
            ⟨by change p.1.val + p.2.val = p.1.val + 1; omega, h1, h1'⟩)),
        by change shuffleSnd a b (p.1.val + p.2.val) = p.2.val
           have h := (shuffleSnd_eq_one (a := a) (b := b)
             (t := p.1.val + p.2.val)).2 ⟨by omega, by omega⟩
           omega⟩
    · refine ⟨⟨p.1.val + p.2.val, by
          have e1 := p.1.2
          have e2 := p.2.2
          omega⟩, ?_⟩
      rw [shuffleTau_objEquiv_apply_eq_iff hab hb _]
      exact ⟨(shuffleFst_eq_iff hab).2 (Or.inr (Or.inr
          ⟨by change p.1.val + p.2.val = p.1.val + 2; omega, h1⟩)),
        by change shuffleSnd a b (p.1.val + p.2.val) = p.2.val
           have h := (shuffleSnd_eq_two (a := a) (b := b)
             (t := p.1.val + p.2.val) hab).2 (by omega)
           omega⟩

end ShuffleTau

end SSet

end
