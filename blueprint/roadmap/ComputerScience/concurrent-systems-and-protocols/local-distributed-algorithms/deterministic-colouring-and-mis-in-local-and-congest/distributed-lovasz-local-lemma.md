# Distributed algorithms for the Lovász local lemma

Let $\mathcal{A}$ be a family of bad events determined by independent random variables, each event depending on at most $d$ others (in the dependency graph) and having probability at most $p$. If $e p (d + 1) \le 1 - \epsilon$ for a constant $\epsilon > 0$, a parallel version of the Moser–Tardos resampling algorithm finds, in the LOCAL model on the dependency graph, an assignment avoiding all events in $O(\log^2 n / \epsilon)$ rounds with high probability; under the stronger condition $e p d^2 < 1$ there is a randomized algorithm using $O(\log_{1/(e p d^2)} n)$ rounds. Every randomized distributed algorithm for the Lovász local lemma requires $\Omega(\log\log n)$ rounds, even for $p \le 2^{-d}$.

## Proof sketch

Moser–Tardos resamples, in each round, a maximal independent set (in the dependency graph) of currently violated events; the witness-tree argument shows that a witness tree of size $s$ appears with probability at most $(e p (d+1))^s \le (1-\epsilon)^s$ bounds, so after $O(\log n / \epsilon)$ rounds of resampling no long witness trees remain, and each round costs $O(\log n)$ for the MIS computation. The faster algorithm resamples events that are local minima of random priorities, avoiding the MIS computation. The lower bound is the sinkless orientation lower bound, since sinkless orientation is an instance of the local lemma.

## Depends on

- [The LOCAL model](../../distributed-execution-models/the-local-model.md)

## Proof depends on

- [Sinkless orientation and Delta-colouring of trees separate randomness from determinism](../lcl-problems-and-the-locality-landscape/sinkless-orientation-randomized-deterministic-separation.md)
- [Luby's maximal independent set algorithm](../luby-s-maximal-independent-set-algorithm.md)

## Sources

- R. A. Moser, G. Tardos, "A constructive proof of the general Lovász Local Lemma", Journal of the ACM 57(2) (2010).
- K.-M. Chung, S. Pettie, H.-H. Su, "Distributed algorithms for the Lovász local lemma and graph coloring", Distributed Computing 30 (2017); PODC 2014.
- S. Brandt, O. Fischer, J. Hirvonen, B. Keller, T. Lempiäinen, J. Rybicki, J. Suomela, J. Uitto, "A Lower Bound for the Distributed Lovász Local Lemma", STOC 2016, arXiv:1511.00900.
