---
article_id: af_7eb62e83fda0a30654ed2073
declaration: def
origin: cited
statement: formalized
lean: MetaMathlibExt.IsFormalSequence
---

# Is Formal Sequence

A formal sequence extended from a seed triplet `(a, b, c)`.

The middle seed is nonzero, the first three terms are `a`, `b`, and `c`, and
the sequence satisfies `u (n + 2) = α * u (n + 1) - u n + β` for every `n`.
This is statement `jis_50a05fd3a5b6b4a1865a61bb`, concept
`jis_sem_1ce947826a0dceb6fde5b7f2`, in
<https://cs.uwaterloo.ca/journals/JIS/VOL23/Kocik/kocik5.tex>, lines 482–499.
Source SHA-256: `f216e1e1606af32792c37505ee832c53db0244b0c93f934f34619996b1aa1746`;
raw block SHA-256: `9665499a711e4ccc50f15a8b66c8cc5e643123774d2a19478a2e7605e8d72a4d`.

## Depends on

This node has no prerequisites.

## Proof depends on

- [Formal Alpha](formal-alpha.md)
- [Formal Beta](formal-beta.md)

## Sources

- [MathlibExt, MathlibExt.NumberTheory.FormalSequence](../../../../../sources/v2/MathlibExt.md)
