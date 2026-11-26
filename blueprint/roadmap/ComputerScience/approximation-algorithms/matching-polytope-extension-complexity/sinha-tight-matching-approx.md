# Sinha: (1+eps)-approximate matching relaxations need binom(n, alpha/eps) inequalities

There is an absolute constant $\alpha \in (0,1)$ such that for every even $n$ and every $\varepsilon$ with $\tfrac2n \le \varepsilon \le 1$, every linear extension of every $(1+\varepsilon)$-approximate relaxation of $P_{\mathrm{M}}(n)$ has at least

$$
\binom{n}{\alpha/\varepsilon}
$$

inequalities. This is tight up to the constant $\alpha$: the relaxation $K_\varepsilon$ that keeps the nonnegativity and degree constraints and only the odd-set constraints $x(E(U)) \le \tfrac{|U|-1}{2}$ with $|U| \le 1+\tfrac1\varepsilon$ uses $n^{O(1/\varepsilon)}$ inequalities.

## Proof sketch

Restrict the nested slack matrix to odd cuts of size about $1/\varepsilon$ and matchings, and relate its nonnegative rank to that of a lopsided version of the unique disjointness matrix, in which one party holds a small set of size $\Theta(1/\varepsilon)$. A hyperplane separation argument with a lopsided corruption bound shows every rectangle carries weight at most $\binom{n}{\alpha/\varepsilon}^{-1}$ relative to the total, which lower-bounds the nonnegative rank and hence the extension complexity.

## Depends on

- [Multiplicatively approximate relaxations of the matching polytope](approximate-polytope-relaxation.md)
- [Linear extensions of a polytope and their inequality count](linear-extension-size.md)
- [Matching polytope](../../../GraphTheory/matchings-and-flows/matching-polytope/matching-polytope.md)

## Proof depends on

- [Dropping large odd-set constraints gives a (1+eps)-approximate matching relaxation](truncated-odd-set-relaxation.md)
- [Fiorini's hyperplane separation lower bound on nonnegative rank](hyperplane-separation-bound.md)
- [Slack matrix of a nested pair of polytopes](slack-matrix-nested-pair.md)
- [Nonnegative factorizations of nested-pair slack matrices and sandwiched extensions](nested-pair-factorization.md)
- [Nonnegative rank of a matrix](../../machine-learning/unsupervised-learning/non-negative-matrix-factorization/nonneg-rank.md)

## Sources

- Makrand Sinha, "Lower Bounds for Approximating the Matching Polytope", SODA (2018), ECCC TR17-185.
- Thomas Rothvoss, "The Matching Polytope has Exponential Extension Complexity", STOC (2014) and Journal of the ACM (2017), arXiv:1311.2369.
