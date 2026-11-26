# Short quartet methods reconstruct almost all trees from polylogarithmically many sites

For an internal edge $e$ of a binary tree $T$, let $d_1(e)$ and $d_2(e)$ be the topological distances from the endpoints of $e$ to the nearest leaf in each of the two rooted subtrees obtained by deleting $e$; the depth of $T$ is $\max_e\max(d_1(e), d_2(e))$ over internal edges, and a quartet is short if it induces a subtree consisting of one edge joined to four disjoint paths of topological length at most $\mathrm{depth}(T) + 1$ (Section 2). Suppose $k$ sites evolve independently under the Neyman two-state model on a binary tree $T$ with $n$ leaves, with all edge substitution probabilities $p(e) \in [f, g]$, where $0 < f \le g < \tfrac12$ and $f$ and $g$ may depend on $n$ (so that the denominator below is positive). Erdős, Steel, Székely and Warnow (1999, Theorem 9) prove that their dyadic closure method reconstructs $T$ with probability $1 - o(1)$ if

$$k > \frac{c\,\log n}{(1 - \sqrt{1 - 2f})^2\,(1 - 2g)^{4\,\mathrm{depth}(T) + 6}}$$

for a fixed constant $c$. By their Theorem 10, $\mathrm{depth}(T) \le (2 + o(1))\log_2\log_2(2n)$ with probability $1 - o(1)$ for a uniformly random semilabelled binary tree, and $\mathrm{depth}(T) = (1 + o(1))\log_2\log_2 n$ with probability $1 - o(1)$ under the Yule–Harding distribution after suppressing the root; so for fixed $f, g$ a number of sites polylogarithmic in $n$ suffices for almost all trees, that is, for a set of trees of probability $1 - o(1)$ under each of these two distributions. This is not a claim for every topology: for a tree whose depth is of order $\log n$, such as a balanced tree, the bound of Theorem 9 is polynomial in $n$.

## Expansion

1. The model: the Neyman two-state model on a binary tree, the edge-probability bounds $0 < f \le g < \tfrac12$, and the depth and short quartets of a tree.
2. Estimation of quartet splits by the four-point method from estimated distances, with exponential concentration bounds (the estimates (22)–(24)).
3. The dyadic closure of a set of quartet splits, the widths of quartets, and the search over widths satisfying hypothesis (14).
4. Theorem 9: the sample-size bound (25), by showing that hypothesis (14) holds with probability $1 - o(1)$.
5. Theorem 10: the depth of random trees under the uniform and Yule–Harding models, via edi-subtrees, and the resulting polylogarithmic bound for almost all trees under each model.

## Sources

- P. L. Erdős, M. A. Steel, L. A. Székely and T. J. Warnow, A few logs suffice to build (almost) all trees (I), Random Struct. Algorithms 14 (1999), 153–184, Section 2 and Theorems 9 and 10. <https://doi.org/10.1002/(sici)1098-2418(199903)14:2%3C153::aid-rsa3%3E3.0.co;2-r>
