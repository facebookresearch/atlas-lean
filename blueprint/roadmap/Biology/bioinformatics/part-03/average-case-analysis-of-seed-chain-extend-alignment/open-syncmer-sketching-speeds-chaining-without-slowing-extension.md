# Open syncmer sketching speeds chaining without slowing extension

**Setting.** In the random-string model of [expected runtime and recoverability of k-mer seed-chain-extend](expected-runtime-and-recoverability-of-k-mer-seed-chain-extend.md), seeds are now restricted to a *sketch*: a context-independent subsample of $k$-mers selected by an *open syncmer* rule (a $k$-mer is selected according to the position of its smallest $s$-mer, independently of its neighbours), with density $1/c$, so the same $k$-mer is selected in $S$ and $S'$ whenever it is present in both.

**Theorem.** Under the hypotheses of the unsketched theorem, let $c = O(\log n) < k$ and adjust the chaining gap parameter as specified in the source. For open-syncmer-sketched seed-chain-extend:

- the expected extension time is $O\bigl(\min\bigl(\tfrac{1}{c^2}\, m\, n^{C\alpha}\log^3 n,\; c\, m\, n^{C\alpha}\log n\bigr)\bigr)$;
- the expected chaining time is $O\bigl(\tfrac1c\, m\, n^{-C\alpha}\log m\bigr)$;
- the expected recoverability of any optimal chain is still at least $1 - O(1/\sqrt m)$.

Thus even with $c = \Theta(\log n)$ the asymptotic extension bound is unchanged up to polylogarithmic factors, while chaining speeds up by a factor $c$: sketching can reduce chaining time without increasing extension time much.

## Depends on

- [Expected runtime and recoverability of k-mer seed-chain-extend](expected-runtime-and-recoverability-of-k-mer-seed-chain-extend.md)

## Expansion

Context independence (a $k$-mer's selection depends only on the $k$-mer itself) makes sketched anchors a thinning of unsketched ones, so the analysis of homologous and spurious anchors carries over. Open syncmers additionally guarantee spacing: once the smallest $s$-mer of a selected $k$-mer shifts, the positions where the next selected $k$-mer can occur are restricted, which bounds the gaps sketching introduces between surviving anchors and hence the extra extension cost. Other schemes such as minimizers or FracMinHash are not context independent or lack this spacing property and behave differently.

## Sources

- J. Shaw and Y. W. Yu, "Proving sequence aligners can guarantee accuracy in almost O(m log n) time through an average-case analysis of the seed-chain-extend heuristic", *Genome Research* (2023), Results, "Sketching and local k-mer selection", Theorem 2, Theorem 7 and Lemma 10. <https://doi.org/10.1101/gr.277637.122> (PMC10538486)
