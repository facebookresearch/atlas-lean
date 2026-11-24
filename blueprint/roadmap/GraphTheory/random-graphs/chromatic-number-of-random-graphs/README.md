# Chromatic number of random graphs

For constant edge probability $p$, Bollobás (1988) proved that $\chi(G(n, p)) = (1 + o(1))\, n/(2\log_b n)$ with high probability, where $b = 1/(1-p)$; for $G(n, 1/2)$ this is $n/(2\log_2 n)$. The lower bound comes from the independence number $\alpha(G(n, p)) \sim 2\log_b n$. The upper bound needs large independent sets inside every set of $n/(\log_b n)^2$ vertices, with exponentially small failure probability. Erdős Problem 625 compares $\chi$ with the cochromatic number of $G(n, 1/2)$.

- [Probability of a large chromatic–cochromatic gap](prob-diff-gt.md)
- [Erdős Problem 625](conjecture.md)
- [Chromatic minus cochromatic number of a random graph tends to infinity](conjecture-holds.md)
- [Chromatic number of dense random graphs (Bollobás)](tendsto-measure-real-chromatic-number-ne.md)

## Related topics

- [Connectivity threshold of random graphs](../connectivity-threshold-of-random-graphs/README.md): the sparse end of the evolution of $G(n, p)$, at $p = (\log n + c)/n$.
- [Janson's inequalities](../../../Combinatorics/probabilistic-combinatorics/janson-s-inequalities/README.md): exponentially small bounds on the probability that $G(n, p)$ contains no copy of a fixed structure, the tool of later proofs of Bollobás's upper bound.
- [Symmetric Lovász Local Lemma](../../../Combinatorics/probabilistic-combinatorics/lovasz-local-lemma-symmetric-finite.md): positive-probability existence when bad events have bounded dependence, the complement of the high-probability statements here.
- [Graph Ramsey numbers](../../graph-ramsey-theory/graph-ramsey-numbers/README.md): Kim's lower bound for $R(3, t)$, triangle-free graphs whose independence number is small, so whose chromatic number is large.
