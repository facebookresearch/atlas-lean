---
article_id: af_4fc5a6a02519e0868ba6648b
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MetaMathlibExt.c_recursive_exponential_growth_bound
---

# C recursive exponential growth bound

Every C-recursive complex sequence is exponentially bounded: there is an
integer `g ≥ 1` with `‖t n‖ < g ^ (n + 1)` for all `n`.

The hypothesis unfolds C-recursiveness: some order `k ≥ 1` with
`t (n + k) = ∑ i, c i * t (n + i.val)` for all `n`. It follows from
`exists_norm_lt_pow_of_isSolution`; the source's `1 ≤ k` is unused.
Proves `Wanted` entry `c_recursive_exponential_growth_bound`.

## Depends on

This node has no prerequisites.

## Proof depends on

- [Exists norm lt pow of is Solution](exists-norm-lt-pow-of-is-solution.md)

## Sources

- [MathlibExt, MathlibExt.NumberTheory.Recurrences.CRecursiveExponentialGrowth](../../../../../../../sources/v2/MathlibExt.md)
- M. Prunescu and J. M. Shunia, "On Modular Representations of C-Recursive Integer Sequences," Journal of Integer Sequences 28 (2025), Article 25.5.3, Lemma (label LemmaGeneralInequality, quoting Prunescu and Sauras-Altuzarra, Lemma 4), lines 166–167, https://cs.uwaterloo.ca/journals/JIS/VOL28/Prunescu/prunescu3.tex
