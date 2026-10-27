---
article_id: af_b13fee4ead58a59e54d58aab
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MetaMathlibExt.thue_lemma
---

# Thue lemma

Thue's lemma: coprime integers `a`, `n > 1` have nonzero bounded `x`, `y`
with `x ≡ a * y [ZMOD n]`.

Both representatives are
nonzero with `|x|, |y| < √n`, matching the source bounds exactly.
It follows from `thue_lemma_general`; the hypothesis `ha` is unused and keeps the source's
shape.
Proves `Wanted` entry `thue_lemma`.

## Depends on

This node has no prerequisites.

## Proof depends on

- [Thue lemma general](thue-lemma-general.md)

## Sources

- [MathlibExt, MathlibExt.NumberTheory.ThueLemma](../../../../../sources/v2/MathlibExt.md)
- Bencheng Li, Steven J. Miller, Tudor Popescu, Daniel Sarnecki, and Nawapan Wattanawanichkul, "Modeling Random Walks to Infinity on Primes in Z[√2]", Journal of Integer Sequences 25 (2022), Article 22.6.1, Lemma [Thue's lemma] (label `lem:thue's`), lines 217–218, <https://cs.uwaterloo.ca/journals/JIS/VOL25/Miller/miller11.tex>. Original: V. Shoup, "A Computational Introduction to Number Theory and Algebra", Cambridge University Press, 2005, p. 43.
