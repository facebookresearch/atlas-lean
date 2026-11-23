# Sampling expectation is an expectation of independent indicators

Let $\nu$ be a probability measure on a measurable space $\Omega$, let $n$ be a natural number, and let $X_1, \dots, X_n : \Omega \to \{0, 1\}$ be measurable and mutually independent under $\nu$ with $\nu(X_i = 1) = q_i$ for each $i$. Then for every $g : \{0, 1\}^n \to \mathbb{R}$,

$$\int g(X_1, \dots, X_n) \, d\nu = \mathbb{E}_q[g],$$

where $\mathbb{E}_q$ is the [sampling expectation](sample-expect.md).
