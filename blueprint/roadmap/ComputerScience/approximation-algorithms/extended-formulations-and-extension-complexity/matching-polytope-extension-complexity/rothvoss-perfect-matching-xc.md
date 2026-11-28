# Rothvoss: the perfect matching polytope of K_n has extension complexity 2^Omega(n)

There are absolute constants $c > 0$ and $n_0$ such that for every even $n \ge n_0$,

$$
\mathrm{xc}(P_{\mathrm{PM}}(n)) \ge 2^{cn},
$$

where $P_{\mathrm{PM}}(n)$ is the perfect matching polytope of $K_n$ and $\mathrm{xc}$ is extension complexity over $\mathbb{R}$; equivalently, as Rothvoss phrases it, the least number of facets of a polyhedron with a linear projection onto $P_{\mathrm{PM}}(n)$, after removing any lineality space and counting facets relative to its affine hull. The same bound holds for the matching polytope of $K_n$, which has $P_{\mathrm{PM}}(n)$ as a face. Since Edmonds' description has $2^{O(n)}$ inequalities, the bound is tight up to the constant in the exponent, although maximum-weight matching is solvable in polynomial time.

## Proof sketch

Fix $k=501$ and the parameters of the measure-increase lemma, and choose $W_{U,M}=-\infty$ on $Q_1$, $1/|Q_3|$ on $Q_3$, $-\tfrac{1}{k-1}\cdot\tfrac{1}{|Q_k|}$ on $Q_k$ and $0$ elsewhere. Then $\langle W,S\rangle=2-1=1$, and the lemma gives $\langle W,\mathbf{1}_{\mathcal{R}}\rangle=\mu_3(\mathcal{R})-\tfrac{1}{k-1}\mu_k(\mathcal{R}) \le 2^{-\delta m}$ for every rectangle with $\mu_1(\mathcal{R})=0$. The hyperplane separation bound with $\|S\|_\infty \le n$ yields $\mathrm{rk}_+ \ge 2^{\delta m}/n=2^{\Omega(n)}$, which transfers to $\mathrm{xc}$ by the factorization lemma; intermediate even $n \ge n_0$ follow, after shrinking $c$, because $P_{\mathrm{PM}}(n)$ is a face of $P_{\mathrm{PM}}(n')$ for $n \le n'$.

## Depends on

- [Extended formulations and extension complexity](../extended-formulation.md)
- [Perfect matching polytope](../../../../GraphTheory/matchings-and-flows/matching-polytope/perfect-matching-polytope.md)
- [Matching polytope](../../../../GraphTheory/matchings-and-flows/matching-polytope/matching-polytope.md)

## Proof depends on

- [Nonnegative factorizations of nested-pair slack matrices and sandwiched extensions](nested-pair-factorization.md)
- [Fiorini's hyperplane separation lower bound on nonnegative rank](hyperplane-separation-bound.md)
- [Rothvoss' quadratic measure increase for cut-matching rectangles](rothvoss-quadratic-measure-increase.md)
- [Odd-cut slack matrix of the perfect matching polytope](odd-cut-matching-slack.md)
- [Faces and projections do not increase extension complexity](../extension-complexity-faces-and-projections.md)

## Sources

- Thomas Rothvoss, "The Matching Polytope has Exponential Extension Complexity", STOC (2014) and Journal of the ACM (2017), arXiv:1311.2369, Theorem 1, Lemmas 5–7 and Section 2.
