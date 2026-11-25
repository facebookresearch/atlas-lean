# Connectivity threshold of random graphs

In the binomial random graph $G(n, p)$, take $p = (\log n + c)/n$ with $c$ a fixed real number. Then

$$\Pr[G(n, p) \text{ is connected}] \to e^{-e^{-c}} \qquad (n \to \infty),$$

as proved by Erdős and Rényi (1959). The proof has two parts. First, the number $X$ of isolated vertices has mean $n(1-p)^{n-1} \to e^{-c}$ and is asymptotically Poisson; this holds whenever $np - \log n \to c$, so $\Pr[X = 0] \to e^{-e^{-c}}$. Second, with high probability $G(n, p)$ has no component with between $2$ and $n/2$ vertices, so it is connected exactly when $X = 0$. As $c$ runs over $\mathbb{R}$ this describes the whole window. For $p = (\log n + \omega(n))/n$ with $\omega(n) \to \infty$ the graph is connected with high probability; for $\omega(n) \to -\infty$ it is disconnected with high probability.

$G(n, p)$ is the [graph of a random set of pairs](../../graph-ramsey-theory/graph-ramsey-numbers/pair-graph.md), each pair kept independently with probability $p$, as in the [threshold for triangles](../threshold-for-triangles/README.md). The hypotheses used, $p_n = (\log n + c)/n$ for all large $n$ or more generally $n p_n - \log n \to c$, are satisfiable for every $c$.

- [Connectivity threshold of $G(n, p)$ (Erdős–Rényi)](tendsto-measure-real-connected.md)
- [No isolated vertex at the connectivity threshold (Erdős–Rényi)](tendsto-measure-real-no-isolated.md)
- [First moment of isolated vertices at the connectivity threshold](tendsto-mul-one-sub-pow.md)
- [Isolated vertices are rare beyond $e^{-c}$](eventually-measure-real-exists-isolated.md)
- [First moment bound for isolated vertices of $G(n, p)$](measure-real-exists-isolated-le.md)
- [Probability that a vertex of $G(n, p)$ is isolated](measure-real-isolated.md)
- [Isolation is avoidance of the pairs at a vertex](set-of-isolated-eq-avoid-event.md)
- [Pairs at a vertex](pairs-at.md)
- [The threshold probabilities exist](exists-prob-eventually-eq.md)
- [The exact threshold sequence satisfies $n p_n - \log n \to c$](tendsto-mul-sub-log-of-eventually-eq.md)

## Related topics

- [Threshold for triangles](../threshold-for-triangles/README.md): the first- and second-moment analysis of another threshold in the same model.
- [Connectivity of random k-out graphs](../connectivity-of-random-k-out-graphs/README.md): connectivity in a different random graph model.
- [First and second moment methods](../../../Combinatorics/probabilistic-combinatorics/first-and-second-moment-methods/README.md): the general tools; the bound $\Pr[X > 0] \le \mathbb{E} X$ is used here.
- [Kim–Vu polynomial concentration](../../../Probability/concentration-inequalities/kim-vu-polynomial-concentration/README.md): concentration of subgraph counts in $G(n, p)$, used when the expectation alone does not control the count.
