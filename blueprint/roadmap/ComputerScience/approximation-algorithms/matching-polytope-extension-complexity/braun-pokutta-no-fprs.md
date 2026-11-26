# Braun-Pokutta and Rothvoss: approximate matching relaxations need 2^Omega(min(n, 1/eps)) size

There is an absolute constant $c > 0$ such that for every even $n$:

(i) every polytope $K$ with $P_{\mathrm{M}}(n) \subseteq K \subseteq (1+\tfrac{1}{2n})P_{\mathrm{M}}(n)$ has $\mathrm{xc}(K) \ge 2^{cn}$ (Braun-Pokutta);

(ii) for every $\varepsilon > 0$, every $(1+\varepsilon)$-approximate relaxation $K$ of $P_{\mathrm{M}}(n)$ has $\mathrm{xc}(K) \ge 2^{c\min\{n,\,1/\varepsilon\}}$ (Rothvoss).

In particular the matching polytope admits no fully-polynomial size relaxation scheme.

## Proof sketch

For (i), work with the nested slack matrix of the pair $(P_{\mathrm{M}}(n),(1+\tfrac{1}{2n})P_{\mathrm{M}}(n))$, whose odd-cut entries are those of the exact slack matrix shifted up by a term of order $\Theta(1)$ relative to the entries in $Q_1$; Braun and Pokutta show Rothvoss' rectangle bound survives this shift, so the hyperplane separation bound still gives nonnegative rank $2^{\Omega(n)}$, and the factorization lemma converts it into extension complexity. For (ii), embed $P_{\mathrm{M}}(n')$ with $n'=\Theta(\min\{n,1/\varepsilon\})$ as a face, so a $(1+\varepsilon)$ relaxation induces a $(1+\tfrac{1}{2n'})$ relaxation of the smaller polytope.

## Depends on

- [Multiplicatively approximate relaxations of the matching polytope](approximate-polytope-relaxation.md)
- [Linear extensions of a polytope and their inequality count](linear-extension-size.md)
- [Matching polytope](../../../GraphTheory/matchings-and-flows/matching-polytope/matching-polytope.md)

## Proof depends on

- [Rothvoss: the perfect matching polytope of K_n has extension complexity 2^Omega(n)](rothvoss-perfect-matching-xc.md)
- [Nonnegative factorizations of nested-pair slack matrices and sandwiched extensions](nested-pair-factorization.md)
- [Fiorini's hyperplane separation lower bound on nonnegative rank](hyperplane-separation-bound.md)
- [Slack matrix of a nested pair of polytopes](slack-matrix-nested-pair.md)
- [Odd-cut slack matrix of the perfect matching polytope](odd-cut-matching-slack.md)
- [Nonnegative rank of a matrix](../../machine-learning/unsupervised-learning/non-negative-matrix-factorization/nonneg-rank.md)

## Sources

- Gabor Braun, Sebastian Pokutta, "The Matching Polytope Does Not Admit Fully-Polynomial Size Relaxation Schemes", SODA (2015) and IEEE Transactions on Information Theory (2015), arXiv:1403.6710.
- Thomas Rothvoss, "The Matching Polytope has Exponential Extension Complexity", STOC (2014) and Journal of the ACM (2017), arXiv:1311.2369.
