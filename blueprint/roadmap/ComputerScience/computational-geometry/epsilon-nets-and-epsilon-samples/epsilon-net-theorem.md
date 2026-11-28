# ε-net theorem

Let $(X, R)$ be a range space of finite VC dimension $\delta$, let $x$ be a finite nonempty subset of $X$, and let $0 < \varepsilon \le 1$ and $0 < \varphi < 1$. Let $N$ be the multiset of $m$ independent draws from the uniform distribution on $x$, for an integer $m$ with

$$m \ge \max\left( \frac{4}{\varepsilon} \log_2 \frac{4}{\varphi}, \; \frac{8\delta}{\varepsilon} \log_2 \frac{16}{\varepsilon} \right).$$

Then $N$ is an $\varepsilon$-net for $x$ with probability at least $1 - \varphi$ (Haussler and Welzl).

## Depends on

- [ε-net and ε-sample of a range space](epsilon-net.md)

## Proof depends on

- [Chebyshev's inequality](../../../Probability/moments/chebyshev-s-inequality/meas-ge-le-variance-div-sq.md)
- [Sauer-Shelah bound on traces](../../machine-learning/pac-learning/sample-complexity-and-combinatorial-dimensions/finite-traces-of-a-concept-class/card-trace-family-le-sum-vc-dim.md)

## Related topics

- [The epsilon-net theorem](../../machine-learning/pac-learning/sample-complexity-and-combinatorial-dimensions/vc-sample-complexity-and-epsilon-nets/epsilon-net-theorem.md): the version for function classes and an arbitrary probability measure, with other constants.

## Sources

- S. Har-Peled, *Geometric Approximation Algorithms*, revised online chapter "On complexity, sampling, ε-nets and ε-samples" (Chapter 7), <https://sarielhp.org/book/chapters/vc_dim.pdf>: Theorem 7.3.4 (ε-net theorem) and its proof in Section 7.5, Claims 7.5.1–7.5.2 (Chebyshev's inequality for the second sample and the bound on the number of traces)
- D. Haussler and E. Welzl, "ε-nets and simplex range queries", *Discrete & Computational Geometry* 2 (1987), 127–151, <https://doi.org/10.1007/BF02187876>: the source to which Har-Peled credits Theorem 7.3.4; the displayed constants are Har-Peled's
