# Pure weighted simplicial complexes and their face distributions

Let $X$ be a finite simplicial complex on vertex set $X(0)$ and write $X(i)$ for its set of $i$-dimensional faces (faces of size $i+1$). The complex is **pure of dimension $d$** if every face is contained in some face of $X(d)$.

A **weighting** of a pure $d$-dimensional complex is a probability distribution $\Pi_d$ on $X(d)$ with full support. It induces distributions $\Pi_i$ on $X(i)$ for $-1 \le i \le d$ by the downward rule: sample $\sigma \sim \Pi_d$ and output a uniformly random $i$-face of $\sigma$. Explicitly,

$$
\Pi_i(\tau) = \frac{1}{\binom{d+1}{i+1}} \sum_{\sigma \in X(d),\, \sigma \supseteq \tau} \Pi_d(\sigma).
$$

When unspecified, $\Pi_d$ is uniform on $X(d)$.

## Depends on

- [Finite abstract simplicial complex](../rational-homology-of-simplicial-complexes/is-simplicial-complex.md)

## Sources

- I. Oppenheim, "Local spectral expansion approach to high dimensional expanders Part I: Descent of spectral gaps", Discrete & Computational Geometry 59 (2018) 293-330, arXiv:1709.04431.
- I. Dinur, T. Kaufman, "High dimensional expanders imply agreement expanders", FOCS (2017), ECCC TR17-089.
- A. Lubotzky, "High dimensional expanders", Proceedings of the ICM (2018), arXiv:1712.02526.
