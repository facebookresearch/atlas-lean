# The matrix mechanism is differentially private

Let $\varepsilon > 0$ and $n \ge 1$. Let $A$ be an $m \times n$ strategy matrix of rank $n$ (so $m \ge n$) with sensitivity $\Delta_A > 0$, let $A^{+} = (A^{\mathsf T}A)^{-1}A^{\mathsf T}$ be its pseudo-inverse, and let $W$ be any $p \times n$ workload matrix. Count vectors $x \in \mathbb{N}^n$ are neighbouring when they differ by the addition or removal of one record. Let $\tilde b$ be a vector of $m$ independent Laplace samples of scale $1$. The *matrix mechanism*

$$
M_A(W, x) \;=\; Wx + \frac{\Delta_A}{\varepsilon}\, W A^{+} \tilde b
$$

is $\varepsilon$-differentially private.

Because $A$ has rank $n$, $A^{+}A$ is the identity, so the mechanism is the post-processing $M_A(W, x) = W A^{+} L(A, x)$ of the Laplace mechanism $L(A, x) = Ax + (\Delta_A/\varepsilon)\,\tilde b$ applied to the strategy queries. Privacy does not depend on the choice of $A$. The choice of $A$ only affects the error of the workload answers.

## Proof sketch

The Laplace mechanism with independent Laplace noise of scale $\Delta_A/\varepsilon$ in each coordinate is $\varepsilon$-differentially private for the vector-valued query $x \mapsto Ax$, whose $\ell_1$ sensitivity is $\Delta_A$. The map $y \mapsto W A^{+} y$ is linear, hence measurable, and post-processing preserves differential privacy.

## Depends on

- [Differential privacy](../differential-privacy/differentially-private.md)
- [Neighbouring histograms](../differential-privacy/histogram-adj.md)
- [Sensitivity of a query matrix](query-matrix-sensitivity.md)

## Proof depends on

- [The Laplace mechanism for vector-valued queries](../laplace-and-exponential-mechanisms/laplace-mechanism-pi-differentially-priv.md)
- [Post-processing by a measurable map](../differential-privacy/map.md)

## Sources

- C. Li, M. Hay, V. Rastogi, G. Miklau and A. McGregor, "Optimizing Linear Counting Queries Under Differential Privacy", PODS 2010, arXiv:0912.4742v2, Proposition 2 (Laplace mechanism for a query matrix) and Definition 3.2 (pseudo-inverse estimate) and Proposition 3 (matrix mechanism) with its proof; journal version in The VLDB Journal 24 (2015) 757–781.
