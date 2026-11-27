# Distributed algorithms for the Lovász local lemma

Let $\mathcal{X}$ be a finite set of mutually independent random variables with finite ranges and $\mathcal{A}$ a family of $n = \lvert \mathcal{A} \rvert$ bad events, each $A \in \mathcal{A}$ determined by a set $\mathrm{vbl}(A) \subseteq \mathcal{X}$ of variables. The dependency graph $G_{\mathcal{A}}$ joins two distinct events exactly when they share a variable; this variable-overlap graph, not an arbitrary graph recording probabilistic dependence, is required, since events resampled in parallel must have disjoint variable sets. Suppose every event has at most $d$ neighbours in $G_{\mathcal{A}}$ and probability at most $p$. In the LOCAL model on $G_{\mathcal{A}}$, each node knows $\mathrm{vbl}(A)$ for its event and must output values of these variables, consistent between neighbours, under which its event does not occur. If $e p (d + 1) \le 1 - \epsilon$ for a constant $\epsilon > 0$, the parallel Moser–Tardos resampling algorithm finds such an assignment in $O(\log n/\epsilon)$ resampling rounds with high probability; with an $O(\log n)$-round MIS computation per round this takes $O(\log^2 n / \epsilon)$ rounds. Chung, Pettie and Su give $O(\log^2 d \cdot \log_{1/(e p (d+1))} n)$ rounds when $e p (d+1) < 1$, and under the stronger condition $e p d^2 < 1$ a randomized algorithm using $O(\log_{1/(e p d^2)} n)$ rounds. Conversely, every Monte Carlo distributed algorithm that finds a correct assignment with high probability needs $\Omega(\log\log n)$ rounds, already on instances with $d = 4$ and $p = 1/16$; more precisely, this holds for any algorithm that works under a criterion $p f(d) \le 1$ with $f(4) \le 16$.

## Proof sketch

Moser–Tardos resamples, in each round, the variables of a maximal independent set of $G_{\mathcal{A}}$ among the currently violated events; independence guarantees that the resampled variable sets are disjoint. The witness-tree argument shows that a fixed witness tree of size $s$ occurs with probability at most $(e p (d+1))^s \le (1-\epsilon)^s$, so after $O(\log n/\epsilon)$ resampling rounds no long witness trees remain with high probability, and each round costs $O(\log n)$ rounds for the MIS computation. The faster algorithm avoids the MIS: in each round a violated event resamples its variables exactly when its identifier is the minimum among the identifiers of the violated events in its inclusive neighbourhood, a local minimum of the fixed ID order; a witness-tree argument with $x(A) = 1/d^2$ bounds its number of rounds. The lower bound reduces sinkless orientation in $4$-regular graphs to the local lemma (each vertex's bad event is that all its edges point inward, with $d = 4$ and $p = 1/16$) and applies the randomized lower bound for sinkless orientation.

## Depends on

- [The LOCAL model](../../distributed-execution-models/the-local-model.md)
- [Symmetric Lovász Local Lemma](../../../../Combinatorics/probabilistic-combinatorics/lovasz-local-lemma-symmetric-finite.md)

## Proof depends on

- [Sinkless orientation and Delta-colouring of trees separate randomness from determinism](../lcl-problems-and-the-locality-landscape/sinkless-orientation-randomized-deterministic-separation.md)
- [Luby's maximal independent set algorithm](../luby-s-maximal-independent-set-algorithm.md)

## Sources

- R. A. Moser, G. Tardos, "A constructive proof of the general Lovász Local Lemma", Journal of the ACM 57(2) (2010).
- K.-M. Chung, S. Pettie, H.-H. Su, "Distributed algorithms for the Lovász local lemma and graph coloring", Distributed Computing 30 (2017); PODC 2014, Algorithm 2 and its analysis.
- S. Brandt, O. Fischer, J. Hirvonen, B. Keller, T. Lempiäinen, J. Rybicki, J. Suomela, J. Uitto, "A Lower Bound for the Distributed Lovász Local Lemma", STOC 2016, arXiv:1511.00900, Sections 2.5 and 3 (Theorem 5, Corollary 24).
