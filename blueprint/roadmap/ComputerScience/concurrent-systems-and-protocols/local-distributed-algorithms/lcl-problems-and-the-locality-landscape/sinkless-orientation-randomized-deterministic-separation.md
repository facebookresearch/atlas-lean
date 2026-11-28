# Sinkless orientation and Delta-colouring of trees separate randomness from determinism

Sinkless orientation asks to orient the edges of a graph with minimum degree at least $3$ so that every vertex has an outgoing edge. On bounded-degree graphs its randomized LOCAL complexity (with high probability of success) is $\Theta(\log\log n)$ and its deterministic complexity is $\Theta(\log n)$; on $\Delta$-regular graphs the upper bounds are $O(\log_\Delta \log n)$ randomized and $O(\log_\Delta n)$ deterministic. Likewise, for $\Delta$-colouring trees of maximum degree $\Delta$, the randomized complexity is $\Omega(\log_\Delta \log n)$ and, for $\Delta \ge 55$, $O(\log_\Delta \log n + \log^* n)$, and the deterministic complexity is $\Omega(\log_\Delta n)$ and, for $\Delta \ge 3$, $O(\log_\Delta n + \log^* n)$; for fixed $\Delta \ge 55$ these are $\Theta(\log\log n)$ and $\Theta(\log n)$, and for fixed $\Delta \ge 3$ the deterministic complexity is $\Theta(\log n)$. As a corollary of the sinkless orientation lower bound, every Monte Carlo algorithm for the distributed Lovász local lemma that succeeds with high probability under a criterion $p f(d) \le 1$ with $f(4) \le 16$ (bad-event probability at most $p$, dependency degree at most $d$) needs $\Omega(\log\log n)$ rounds; the reduction runs from sinkless orientation to the local lemma and transfers this lower bound only, not the upper bounds.

## Proof sketch

Lower bounds come from round elimination on high-girth regular graphs: a $t$-round algorithm for sinkless orientation yields a $(t-1)$-round algorithm for a related problem which is again equivalent to sinkless orientation, with a controlled loss in failure probability, so $t = \Omega(\log\log n)$ randomized on $3$-regular graphs, and the deterministic gap theorem turns this into $\Omega(\log n)$ deterministic. For the local lemma corollary, in a $4$-regular graph each vertex's bad event is that all four incident edges, oriented uniformly at random, point inward, which has probability $1/16$ and shares variables with $4$ other events; any local lemma algorithm under such a criterion therefore finds a sinkless orientation, and $3$-regular graphs reduce to $4$-regular ones. The upper bounds for sinkless orientation come from degree-splitting algorithms (randomized $O(\log_\Delta \log n)$ and deterministic $O(\log_\Delta n)$ on $\Delta$-regular graphs), and those for $\Delta$-colouring trees from graph shattering: a randomized step leaves components of size $\mathrm{poly}\log n$, solved deterministically in $O(\log_\Delta \log n + \log^* n)$ rounds.

## Depends on

- [Deterministic and randomized LOCAL complexity of an LCL problem](lcl-deterministic-randomized-complexity.md)

## Proof depends on

- [Deterministic LCL complexities between log-star and log n collapse](lcl-deterministic-gap-log-star-log-n.md)
- [Automatic speedup theorem for round elimination](automatic-speedup-theorem.md)
- [Graph shattering after a randomized pre-shattering phase](../deterministic-colouring-and-mis-in-local-and-congest/graph-shattering-lemma.md)

## Sources

- S. Brandt, O. Fischer, J. Hirvonen, B. Keller, T. Lempiäinen, J. Rybicki, J. Suomela, J. Uitto, "A Lower Bound for the Distributed Lovász Local Lemma", STOC 2016, arXiv:1511.00900, Theorem 5 and Corollary 24.
- Y.-J. Chang, T. Kopelowitz, S. Pettie, "An Exponential Separation between Randomized and Deterministic Complexity in the LOCAL Model", FOCS 2016; SIAM Journal on Computing 48(1) (2019), arXiv:1602.08166, abstract and Theorems 5 and 9–11.
- M. Ghaffari, H.-H. Su, "Distributed Degree Splitting, Edge Coloring, and Orientations", SODA 2017, arXiv:1608.03220, abstract.
