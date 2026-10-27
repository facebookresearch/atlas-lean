---
article_id: af_bb992b0d0db8f1e8f53f4919
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MetaMathlibExt.isolation_lemma
---

# Isolation Lemma

Isolation lemma (stable source: https://en.wikipedia.org/wiki/Isolation_lemma):
a nonempty family `F` of subsets of `Fin n` with independent uniform weights in
`{1, …, 2 * n}`, realized as `(w i).val + 1` for functions `Fin n → Fin (2 * n)`,
has a unique minimum-weight member for at least half of all weight assignments;
probability is the uniform counting (PMF) ratio over `Fin n → Fin (2 * n)`, and
uniqueness is `Finset.card` of the argmin filter equal to `1`.

## Depends on

This node has no prerequisites.

## Sources

- [MathlibExt, MathlibExt.Combinatorics.IsolationLemma](../../../../sources/v2/MathlibExt.md)
