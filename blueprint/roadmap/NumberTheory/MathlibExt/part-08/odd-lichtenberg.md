---
article_id: af_6409cb20d9942f4370d022b7
declaration: def
origin: cited
statement: formalized
lean: MetaMathlibExt.oddLichtenberg
---

# Odd Lichtenberg Numbers

Odd Lichtenberg numbers (OEIS A002450): the sequence of positive `3`-key
distances `(1 / 3) * M_{2 * k} = ℓ_{2 * k - 1} = 1, 5, 21, 85, …`, described as
the self-generating sequence for seed `1` with generating function set
`{k ↦ 4 * k + 1}`, so `a 0 = 1` and `a (n + 1) = 4 * a n + 1`.

Concept `jis_sem_21a46571c2d8f3f53edb5728` (`odd Lichtenberg numbers`);
required clause from stable statement `jis_e2a7cb75f919d56e388fa0b1` in
`https://cs.uwaterloo.ca/journals/JIS/VOL25/Hinz/hinz5.tex`.

## Depends on

This node has no prerequisites.

## Sources

- [MathlibExt, MathlibExt.NumberTheory.OddLichtenbergNumbers](../../../../sources/v2/MathlibExt.md)
