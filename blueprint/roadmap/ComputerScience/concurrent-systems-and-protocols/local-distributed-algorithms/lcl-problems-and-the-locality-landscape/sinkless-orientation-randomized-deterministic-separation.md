# Sinkless orientation and Delta-colouring of trees separate randomness from determinism

Sinkless orientation asks to orient the edges of a graph with minimum degree at least $3$ so that every vertex has an outgoing edge. On bounded-degree graphs its randomized LOCAL complexity is $\Theta(\log\log n)$ and its deterministic complexity is $\Theta(\log n)$. Likewise $\Delta$-colouring trees of maximum degree $\Delta \ge 55$ has randomized complexity $\Theta(\log_\Delta \log n)$ and deterministic complexity $\Theta(\log_\Delta n)$; the same separation holds for the distributed Lovász local lemma, which requires $\Omega(\log\log n)$ randomized rounds.

## Proof sketch

Lower bounds come from round elimination on high-girth regular graphs: a $t$-round algorithm for sinkless orientation yields a $(t-1)$-round algorithm for a related problem which is again equivalent to sinkless orientation, with a controlled loss in failure probability, so $t = \Omega(\log\log n)$ randomized, and the deterministic gap theorem turns this into $\Omega(\log n)$ deterministic. Upper bounds use graph shattering: a randomized $O(\log\log n)$-round step leaves components of size $\mathrm{poly}\log n$, solved deterministically in $O(\log\log n)$ rounds.

## Depends on

- [Locally checkable labeling problem](locally-checkable-labeling-problem.md)
- [Symmetric Lovász Local Lemma](../../../../Combinatorics/probabilistic-combinatorics/lovasz-local-lemma-symmetric-finite.md)

## Proof depends on

- [Deterministic LCL complexities between log-star and log n collapse](lcl-deterministic-gap-log-star-log-n.md)

## Sources

- S. Brandt, O. Fischer, J. Hirvonen, B. Keller, T. Lempiäinen, J. Rybicki, J. Suomela, J. Uitto, "A Lower Bound for the Distributed Lovász Local Lemma", STOC 2016, arXiv:1511.00900.
- Y.-J. Chang, T. Kopelowitz, S. Pettie, "An Exponential Separation between Randomized and Deterministic Complexity in the LOCAL Model", FOCS 2016; SIAM Journal on Computing 48(1) (2019), arXiv:1602.08166.
