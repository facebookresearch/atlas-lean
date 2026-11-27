# Local spectral expanders (one-sided and two-sided)

Let $\lambda \in [0, 1)$. A pure $d$-dimensional weighted complex $X$ is a **one-sided $\lambda$-local spectral expander** if for every face $\tau \in X(i)$ with $-1 \le i \le d-2$, the underlying graph of the link $X_\tau$ is connected and the second largest eigenvalue of its random-walk operator satisfies $\lambda_2(M_\tau) \le \lambda$. It is a **two-sided $\lambda$-local spectral expander** if moreover every nontrivial eigenvalue $\mu$ of every $M_\tau$ satisfies $|\mu| \le \lambda$.

A family of $d$-dimensional complexes $\{X_n\}$ with $|X_n(0)| \to \infty$ is a family of **bounded-degree high-dimensional expanders** if all $X_n$ are $\lambda$-local spectral expanders for a fixed $\lambda < 1$ and every vertex lies in at most $C$ top faces for a constant $C$ independent of $n$.

## Depends on

- [Link of a face in a weighted complex](link-of-face.md)
- [Spectral expander](../../../GraphTheory/graph-families-and-operations/expander-graphs/is-spectral-expander.md)

## Sources

- I. Oppenheim, "Local spectral expansion approach to high dimensional expanders Part I: Descent of spectral gaps", Discrete & Computational Geometry 59 (2018) 293-330, arXiv:1709.04431.
- I. Dinur, T. Kaufman, "High dimensional expanders imply agreement expanders", FOCS (2017), ECCC TR17-089.
- T. Kaufman, D. Mass, "High dimensional random walks and colorful expansion", ITCS (2017), arXiv:1604.02947.
- A. Lubotzky, "High dimensional expanders", Proceedings of the ICM (2018), arXiv:1712.02526.
