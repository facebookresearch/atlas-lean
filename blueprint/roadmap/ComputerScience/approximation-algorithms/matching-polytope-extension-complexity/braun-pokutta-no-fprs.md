# Braun-Pokutta and Rothvoss: approximate matching relaxations need 2^Omega(min(n, 1/eps)) size

There is an absolute constant $c > 0$ such that for every even $n$, with $\mathrm{xc}$ the extension complexity over $\mathbb{R}$:

(i) every polytope $K$ with $P_{\mathrm{M}}(n) \subseteq K \subseteq (1+\tfrac{1}{2n})P_{\mathrm{M}}(n)$ has $\mathrm{xc}(K) \ge 2^{cn}$ (Braun-Pokutta);

(ii) for every $\varepsilon > 0$, every $(1+\varepsilon)$-approximate relaxation $K$ of $P_{\mathrm{M}}(n)$ has $\mathrm{xc}(K) \ge 2^{c\min\{n,\,1/\varepsilon\}}$ (Rothvoss).

In particular the matching polytope admits no fully-polynomial size relaxation scheme.

## Proof sketch

For (i), Braun and Pokutta restrict to objectives indexed by odd sets $U$ and to perfect matchings $M$, and relax the guarantee for $U$ to $(|U|-1+\varepsilon)/2$ with a constant $\varepsilon \in (0,1)$, which is implied by the approximation factor in (i). The resulting shifted slack matrix has entries $(|\delta(U) \cap M|-1+\varepsilon)/2$, so the entries that are exactly $0$ in the odd-cut slack matrix (one crossing edge) become $\varepsilon/2$; no bound on individual rectangles is used. Instead, viewing the normalized matrix as a distribution of $(M,U)$ and conditioning on a random partition of the vertices into chunks (a simplified version of Rothvoss' partition) and on independent coins, a direct-sum argument over the $m = \Theta(n)$ chunks shows that the common information of $M$ and $U$ is at least $c_{k,\varepsilon}\, m$. Since the logarithm of the nonnegative rank is at least the common information, the nonnegative rank is $2^{\Omega(n)}$, and the factorization lemma turns this into the bound on $\mathrm{xc}(K)$.

For (ii), Rothvoss uses a coordinate restriction instead of a new slack-matrix argument. Assume $\varepsilon \ge \tfrac{1}{2n}$ (otherwise (i) applies), take a set $V'$ of an even number $k=\Theta(1/\varepsilon) \le n$ of vertices with $\tfrac{1}{2k} \ge \varepsilon$ (for $\varepsilon$ bounded below by a constant the bound is trivial after shrinking $c$), and let $K'$ be the set of $x' \in \mathbb{R}^{E(V')}$ such that $(x',0) \in K$. Setting the coordinates outside $E(V')$ to $0$ and projecting does not increase extension complexity, and checking nonnegative objectives supported on $E(V')$ shows $P_{\mathrm{M}}(K_{V'}) \subseteq K' \subseteq (1+\tfrac{1}{2k})P_{\mathrm{M}}(K_{V'})$; now (i) on $k$ vertices gives $\mathrm{xc}(K) \ge \mathrm{xc}(K') \ge 2^{\Omega(k)}$.

## Depends on

- [Multiplicatively approximate relaxations of the matching polytope](approximate-polytope-relaxation.md)
- [Extended formulations and extension complexity](../extended-formulations-and-extension-complexity/extended-formulation.md)
- [Matching polytope](../../../GraphTheory/matchings-and-flows/matching-polytope/matching-polytope.md)

## Proof depends on

- [Nonnegative factorizations of nested-pair slack matrices and sandwiched extensions](nested-pair-factorization.md)
- [Slack matrix of a nested pair of polytopes](slack-matrix-nested-pair.md)
- [Odd-cut slack matrix of the perfect matching polytope](odd-cut-matching-slack.md)
- [Nonnegative rank of a matrix](../../machine-learning/unsupervised-learning/non-negative-matrix-factorization/nonneg-rank.md)
- [Faces and projections do not increase extension complexity](../extended-formulations-and-extension-complexity/extension-complexity-faces-and-projections.md)

## Sources

- Gabor Braun, Sebastian Pokutta, "The Matching Polytope Does Not Admit Fully-Polynomial Size Relaxation Schemes", SODA (2015); journal version "The Matching Problem Has No Fully Polynomial Size Linear Programming Relaxation Schemes", IEEE Transactions on Information Theory 61 (2015), arXiv:1403.6710, Sections 1.3, 2.2–2.3 and 3 (Theorem 3.1, Proposition 3.2).
- Thomas Rothvoss, "The Matching Polytope has Exponential Extension Complexity", STOC (2014) and Journal of the ACM (2017), arXiv:1311.2369, Section 4 (Theorem 16, Corollary 17).
