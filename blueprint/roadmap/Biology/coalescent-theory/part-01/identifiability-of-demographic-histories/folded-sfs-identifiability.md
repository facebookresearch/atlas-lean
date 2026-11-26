# Identifiability from the folded site-frequency spectrum

When the ancestral state of each site is unknown, only the folded spectrum is observed: for a sample of size $n$, $\chi_{n,i} = (\xi_{n,i} + \xi_{n,n-i})/(1 + \delta_{i,n-i})$ for $1 \le i \le \lfloor n/2 \rfloor$. Bhaskar and Song (2014, Theorem 12) prove that if $S(F) < \infty$ and $n \ge 2(2K - 1)(1 + S(F))$, then each expected folded spectrum is consistent with a unique equivalence class of $K$-piece models from $F$ (models equal up to the time rescaling that leaves the spectrum unchanged); the proof rests on a symmetry of the matrix relating branch lengths to first-coalescence means (their Lemma 13). The target is this statement, with the folded bound kept separate from the unfolded one.

## Depends on

- [Folded site frequency spectrum](../../expected-site-frequency-spectrum/folded-count.md)

## Expansion

1. The [folded spectrum](../../expected-site-frequency-spectrum/folded-count.md) and its expectation.
2. The linear map from expected epoch lengths to the expected folded spectrum, and its rank.
3. Theorem 12 for $K$-piece families of finite sign-change complexity, via the symmetry of Lemma 13.
4. Whether the folded bound is tight, as a separate question.

## Sources

- A. Bhaskar and Y. S. Song, Descartes' rule of signs and the identifiability of population demographic models from genomic variation data, Ann. Statist. 42 (2014), 2469–2493. <https://arxiv.org/abs/1309.5056>
