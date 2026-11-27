# Chromatic number of dense random graphs (Bollobás)

Let $0 < p < 1$ be constant and $b = 1/(1-p)$. For every $\varepsilon > 0$,

$$\Pr\Big[\,\Big|\frac{\chi(G(n, p))}{n / (2\log_b n)} - 1\Big| \le \varepsilon\Big] \to 1,$$

that is, $\chi(G(n, p)) = (1 + o(1))\, n/(2 \log_b n)$ with high probability. For $p = 1/2$, $b = 2$ and $\chi(G(n, 1/2)) \sim n/(2\log_2 n)$.

The lower bound follows from $\chi \ge n/\alpha$ and the independence number $\alpha(G(n,p)) \sim 2\log_b n$. For the upper bound, Bollobás showed that with high probability every set of $n/(\log_b n)^2$ vertices contains an independent set of size about $2\log_b n - 4\log_b\log_b n$; colouring greedily by such sets uses $(1 + o(1))\, n/(2\log_b n)$ colours. Bollobás obtained the required exponentially small failure probability with a martingale inequality, applied to the maximum number of edge-disjoint independent sets of that size. Later proofs use Janson's inequality. An earlier result of Matula had the constant $3/2$ in place of $2$.

## Background

- [Janson's inequalities](../../../Combinatorics/probabilistic-combinatorics/janson-s-inequalities/README.md): the tool used in later proofs of the upper bound.
- [Kim's lower bound for R(3, t)](../../graph-ramsey-theory/graph-ramsey-numbers/graph-ramsey-three-lower.md): a semi-random construction of triangle-free graphs with small independence number, a sparse counterpart of the dense colouring problem.

## Sources

- B. Bollobás, "The chromatic number of random graphs", *Combinatorica* 8 (1988), 49–55 (not consulted directly).
- A. Frieze and M. Karoński, *Introduction to Random Graphs*, Cambridge University Press (2016), Theorem 7.7, its proof and the remarks after it.
