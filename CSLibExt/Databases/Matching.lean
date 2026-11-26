/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Cslib.Probability.PMF
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Fintype.Perm

/-!
# Matching databases

Beame, Koutris and Suciu, *Communication Steps for Parallel Query Processing* (PODS 2013),
§2.5, take a uniform matching database on a fixed nonempty domain. Each column of each relation
contains every value exactly once. We label the domain by `Fin n` (zero-based rather than
one-based) and write each arity as `k + 1`. Rows form a finite set, not an ordered list or bag.

Indexing rows by column zero gives the permutation representation below. This derives an
independent sampler for the paper's uniform law; §3.2.1 also states the single-relation count.
-/

public section

namespace Cslib.Databases.Matching

open Cslib.Probability.PMF
open scoped ENNReal

/-- **Matching condition on a relation.** A finite set of tuples of positive arity on a nonempty
domain is a matching if evaluation at each column bijects its rows with the domain. In other
words, every domain value occurs in exactly one row at that column.

Source: Beame, Koutris and Suciu, *Communication Steps for Parallel Query Processing* (PODS 2013),
§2.5, “Input Distribution”. -/
@[expose] def IsMatching {n k : ℕ} [NeZero n] (R : Finset (Fin (k + 1) → Fin n)) : Prop :=
  ∀ c, Function.Bijective fun t : R => t.1 c

/-- **Space of matching relations.** For $n>0$ and $k\ge 0$, take all finite sets of tuples of
arity $k+1$ over a domain of size $n$ satisfying the matching condition. Two relations are the
same if and only if they contain the same tuples. -/
abbrev MatchingRelation (n k : ℕ) [NeZero n] :=
  {R : Finset (Fin (k + 1) → Fin n) // IsMatching R}

/-- **Matching databases.** A matching database assigns a matching relation to each name $i$,
with $k_i+1$ columns and the same nonempty domain of size $n$. There may be no names, but no
relation is nullary.

Source: Beame, Koutris and Suciu, *Communication Steps for Parallel Query Processing* (PODS 2013),
§2.5, “Input Distribution”. -/
abbrev MatchingDatabase {ι : Type*} (n : ℕ) [NeZero n] (k : ι → ℕ) :=
  (i : ι) → MatchingRelation n (k i)

section Relation

variable {n k : ℕ} [NeZero n]

private noncomputable def column (R : MatchingRelation n k) (c : Fin (k + 1)) : R.1 ≃ Fin n :=
  Equiv.ofBijective (fun t => t.1 c) (R.2 c)

/-- **Size of a matching relation.** A matching relation of positive arity on a domain of size
$n>0$ has exactly $n$ distinct rows. Projection onto the first column exhibits the bijection. -/
theorem IsMatching.card_eq {R : Finset (Fin (k + 1) → Fin n)} (h : IsMatching R) :
    R.card = n := by
  simpa using Fintype.card_congr (column ⟨R, h⟩ 0)

private def withFirst (σ : Fin k → Equiv.Perm (Fin n)) : Fin (k + 1) → Equiv.Perm (Fin n) :=
  Fin.cons (Equiv.refl _) σ

private def row (σ : Fin k → Equiv.Perm (Fin n)) (x : Fin n) (c : Fin (k + 1)) : Fin n :=
  withFirst σ c x

private def rows (σ : Fin k → Equiv.Perm (Fin n)) := Finset.univ.image (row σ)

omit [NeZero n] in
private theorem row_mem (σ : Fin k → Equiv.Perm (Fin n)) (x : Fin n) : row σ x ∈ rows σ :=
  Finset.mem_image_of_mem _ (Finset.mem_univ x)

private def index (σ : Fin k → Equiv.Perm (Fin n)) : Fin n ≃ ↥(rows σ) where
  toFun x := ⟨row σ x, row_mem σ x⟩
  invFun t := t.1 0
  left_inv _ := rfl
  right_inv t := by
    obtain ⟨x, -, hx⟩ := Finset.mem_image.mp t.2
    apply Subtype.ext
    change row σ (t.1 0) = t.1
    rw [← hx]
    rfl

private def ofPerms (σ : Fin k → Equiv.Perm (Fin n)) : MatchingRelation n k := by
  refine ⟨rows σ, fun c => ?_⟩
  have h : (fun t : rows σ => t.1 c) = (withFirst σ c) ∘ (index σ).symm :=
    funext fun t => congrArg (fun u : rows σ => u.1 c) ((index σ).apply_symm_apply t).symm
  rw [h]
  exact (withFirst σ c).bijective.comp (index σ).symm.bijective

private noncomputable def perms (R : MatchingRelation n k) (j : Fin k) : Equiv.Perm (Fin n) :=
  (column R 0).symm.trans (column R j.succ)

private theorem perms_apply (R : MatchingRelation n k) (t : R.1) (j : Fin k) :
    perms R j (t.1 0) = t.1 j.succ :=
  congrArg (column R j.succ) ((column R 0).symm_apply_apply t)

private theorem row_perms (R : MatchingRelation n k) (x : Fin n) :
    row (perms R) x = ((column R 0).symm x).1 := by
  funext c
  refine Fin.cases ?_ (fun _ => rfl) c
  exact ((column R 0).apply_symm_apply x).symm

/-- **Permutation representation of a matching relation.** On a domain of size $n>0$, families
of $k$ permutations correspond bijectively to matching relations of arity $k+1$. Fixing the
first column as the index removes the freedom to reorder the rows: each other column's
permutation sends $x$ to its value in the unique row whose first value is $x$.

Source: Derived from the matching condition in Beame, Koutris and Suciu, *Communication Steps
for Parallel Query Processing* (PODS 2013), §2.5, which mentions the binary case explicitly. -/
noncomputable def permutationEquiv (n k : ℕ) [NeZero n] :
    (Fin k → Equiv.Perm (Fin n)) ≃ MatchingRelation n k where
  toFun := ofPerms
  invFun := perms
  left_inv σ := by
    funext j
    apply Equiv.ext
    intro x
    exact perms_apply (ofPerms σ) ⟨row σ x, row_mem σ x⟩ j
  right_inv R := by
    apply Subtype.ext
    ext t
    change t ∈ Finset.univ.image (row (perms R)) ↔ t ∈ R.1
    constructor
    · intro ht
      obtain ⟨x, -, rfl⟩ := Finset.mem_image.mp ht
      rw [row_perms]
      exact ((column R 0).symm x).2
    · intro ht
      apply Finset.mem_image.mpr
      refine ⟨t 0, Finset.mem_univ _, ?_⟩
      rw [row_perms]
      exact congrArg Subtype.val ((column R 0).symm_apply_apply ⟨t, ht⟩)

/-- **Rows of a permutation-encoded relation.** For $k$ permutations of a nonempty finite domain,
a tuple $(x,y_1,\ldots,y_k)$ is in the associated relation exactly when $y_j=\sigma_j(x)$ for
every $j$. When $k=0$, this condition admits every unary tuple. -/
theorem mem_permutationEquiv_iff (σ : Fin k → Equiv.Perm (Fin n)) (t : Fin (k + 1) → Fin n) :
    t ∈ ((permutationEquiv n k) σ).1 ↔ ∀ j, t j.succ = σ j (t 0) := by
  change t ∈ Finset.univ.image (row σ) ↔ _
  constructor
  · intro ht
    obtain ⟨x, -, rfl⟩ := Finset.mem_image.mp ht
    exact fun _ => rfl
  · intro h
    refine Finset.mem_image.mpr ⟨t 0, Finset.mem_univ _, ?_⟩
    exact funext (Fin.cases rfl (fun j => (h j).symm))

noncomputable instance (n k : ℕ) [NeZero n] : Fintype (MatchingRelation n k) :=
  Fintype.ofEquiv _ (permutationEquiv n k)

instance (n k : ℕ) [NeZero n] : Nonempty (MatchingRelation n k) :=
  ⟨permutationEquiv n k fun _ => Equiv.refl _⟩

/-- **Counting matching relations.** On a domain of size $n>0$, there are $(n!)^k$ matching
relations of arity $k+1$: there is one arbitrary permutation per non-first column.

Source: Beame, Koutris and Suciu, *Communication Steps for Parallel Query Processing* (PODS 2013),
§3.2.1, paragraph beginning “Observe that for a randomly chosen matching database”. -/
theorem card_matchingRelation (n k : ℕ) [NeZero n] :
    Fintype.card (MatchingRelation n k) = n.factorial ^ k := by
  rw [← Fintype.card_congr (permutationEquiv n k)]
  simp [Fintype.card_perm]

end Relation

variable {ι : Type*} (n : ℕ) [NeZero n] (k : ι → ℕ)

/-- **Permutation representation of a matching database.** On a fixed nonempty finite domain,
encode the non-first columns separately for each relation name. This bijects permutation families
with matching databases, even when the arities vary among the names. -/
@[expose] noncomputable def databaseEquiv :
    ((i : ι) → Fin (k i) → Equiv.Perm (Fin n)) ≃ MatchingDatabase n k :=
  Equiv.piCongrRight fun i => permutationEquiv n (k i)

variable [Fintype ι] [DecidableEq ι]

/-- **Independent column permutations.** For a finite schema on a fixed nonempty finite domain,
choose a uniform permutation independently for each non-first column of each named relation.
The mass of a complete family is the product of the individual permutation masses. -/
@[expose] noncomputable def independentPermutations :
    PMF ((i : ι) → Fin (k i) → Equiv.Perm (Fin n)) :=
  PMF.ofFintype (fun σ => ∏ i, ∏ j, uniformOfFintype (Equiv.Perm (Fin n)) (σ i j)) (by
    let p := uniformOfFintype (Equiv.Perm (Fin n))
    have h (i : ι) : ∑ v : Fin (k i) → Equiv.Perm (Fin n), ∏ j, p (v j) = 1 := by
      rw [← Fintype.prod_sum (fun (_ : Fin (k i)) s => p s)]
      have hp : ∑ s, p s = 1 := by simpa only [tsum_fintype] using p.tsum_coe
      simp [hp]
    rw [← Fintype.prod_sum (fun i (v : Fin (k i) → Equiv.Perm (Fin n)) => ∏ j, p (v j))]
    simp [h])

/-- **Uniform sampling of matching databases.** Fix a nonempty finite domain and finitely many
named relations of positive, possibly different arities. Choose a uniform domain permutation
independently for every non-first column of each relation. Form the rows by applying all the
permutations of a relation to its first-column index. The resulting distribution is uniform on
all matching databases of this schema.

Source: Derived sampler for the uniform input law specified in Beame, Koutris and Suciu,
*Communication Steps for Parallel Query Processing* (PODS 2013), §2.5, “Input Distribution”. -/
theorem map_independentPermutations :
    (independentPermutations n k).map (databaseEquiv n k) =
      uniformOfFintype (MatchingDatabase n k) := by
  rw [← uniformOfFintype_map_equiv (databaseEquiv n k)]
  congr 1
  ext σ
  change ∏ i, ∏ j, uniformOfFintype (Equiv.Perm (Fin n)) (σ i j) = _
  simp only [uniformOfFintype_apply, Fintype.card_pi, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin, Nat.cast_prod, Nat.cast_pow]
  rw [ENNReal.prod_inv_distrib (fun _ _ _ _ _ => Or.inr (by finiteness))]
  simp only [ENNReal.inv_pow]

/-- **Probability of one matching database.** Fix a domain of size $n>0$ and a finite schema
with $k_i+1$ columns at name $i$. Under the uniform matching-database law, the mass of each
individual database is $1/\prod_i(n!)^{k_i}$. The empty product gives probability one. -/
theorem uniform_matchingDatabase_apply (D : MatchingDatabase n k) :
    uniformOfFintype (MatchingDatabase n k) D = ((∏ i, n.factorial ^ k i : ℕ) : ℝ≥0∞)⁻¹ := by
  simp [MatchingDatabase, Fintype.card_pi, card_matchingRelation]

end Cslib.Databases.Matching
