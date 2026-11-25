# Parallel bandwidth lower bound

Let $I$, $J$, $L$ be sets with decidable equality. For a set of triples $(i, j, k)$, its three projections are its images on the pairs $(i, k)$, $(j, k)$ and $(i, j)$. Let $G \subseteq I \times J \times L$ be finite and $P > 0$. For each processor $q \in \{1, \dots, P\}$ let $G_q$ be a finite set of triples, with $G \subseteq G_1 \cup \dots \cup G_P$, and let $s_q$ and $W_q$ be natural numbers and $\Sigma_{q,1}, \dots, \Sigma_{q,s_q}$ finite sets of triples covering $G_q$. Let $M$ be a natural number such that every $\Sigma_{q,t}$ has three projections of at most $4M$ elements each, and $M(s_q - 1) \le W_q$ for every $q$ (truncated subtraction). Then there is a processor $q$ with

$$\frac{|G|}{8 P \sqrt{M}} - M \le W_q,$$

the quotient being $0$ when $M = 0$.

Read $G$ as the evaluations of a computation of matrix-multiplication form, shared among $P$ processors with local memories of $M$ words, processor $q$ evaluating $G_q$ with an execution satisfying the segment hypotheses of the [bandwidth lower bound](card-div-sub-le-words.md) for $W_q$ words moved: some processor performs at least $|G|/P$ evaluations, and hence moves at least the stated number of words. As in the sequential case the bound is vacuous (nonpositive) unless $|G|/P \gg M^{3/2}$. This is the argument of Corollary 5 of G. Ballard, J. Demmel, O. Holtz and O. Schwartz, *Minimizing communication in linear algebra*, arXiv:0905.2485, which assumes memory balance, $M = O(\mathrm{NNZ}/P)$ for $\mathrm{NNZ}$ nonzero entries, and states the bound as $\Omega(|G|/\sqrt{P \cdot \mathrm{NNZ}} - \mathrm{NNZ}/P)$; for dense $n \times n$ matrices with $M = \Theta(n^2/P)$ it is $\Omega(n^2/\sqrt{P})$ words, which Cannon's algorithm attains.

## Informally uses

- [Bandwidth lower bound, segment-counting form](card-div-sub-le-words.md): applied to a processor with at least $|G|/P$ evaluations.
