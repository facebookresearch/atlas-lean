# The matrix mechanism is differentially private

Let $\varepsilon > 0$ and $n \ge 1$. Let $A$ be an $m \times n$ strategy matrix of rank $n$ (so $m \ge n$) with sensitivity $\Delta_A > 0$, let $A^{+}$ be its pseudoinverse, viewing $A$ as a linear map $\mathbb{R}^n \to \mathbb{R}^m$ for the standard inner products, and let $W$ be any $p \times n$ workload matrix. Count vectors $x \in \mathbb{N}^n$ are neighbouring when they differ by the addition or removal of one record. Let $\tilde b$ be a vector of $m$ independent samples from the Laplace law $\mathrm{Lap}(0, 1)$. The *matrix mechanism*

$$
M_A(W, x) \;=\; Wx + \frac{\Delta_A}{\varepsilon}\, W A^{+} \tilde b
$$

is $\varepsilon$-differentially private.

Because $A$ has rank $n$, its null space is $\{0\}$, so $A^{+}A$ is the identity; the source writes $A^{+} = (A^{\mathsf T}A)^{-1}A^{\mathsf T}$ in this case. Hence the mechanism is the post-processing $M_A(W, x) = W A^{+} L(A, x)$ of the Laplace mechanism $L(A, x) = Ax + (\Delta_A/\varepsilon)\,\tilde b$ applied to the strategy queries. Privacy does not depend on the choice of $A$. The choice of $A$ only affects the error of the workload answers.

## Proof sketch

Since $\Delta_A/\varepsilon > 0$, scaling each independent $\mathrm{Lap}(0,1)$ sample by $\Delta_A/\varepsilon$ gives independent noise with law $\mathrm{Lap}(0,\Delta_A/\varepsilon)$. The Laplace mechanism with this noise in each coordinate is $\varepsilon$-differentially private for the vector-valued query $x \mapsto Ax$, whose $\ell_1$ sensitivity is $\Delta_A$. The map $y \mapsto W A^{+} y$ is linear, hence measurable, and post-processing preserves differential privacy.

## Depends on

- [Differential privacy](../differential-privacy/differentially-private.md)
- [Neighbouring histograms](../differential-privacy/histogram-adj.md)
- [Sensitivity of a query matrix](query-matrix-sensitivity.md)
- [Pseudoinverse of a linear map](../../../LinearAlgebra/matrix-decompositions/pseudoinverse/moore-penrose-pseudoinverse.md)
- [Laplace distribution](../../../Probability/distributions/continuous/laplace-distribution/laplace-measure.md)

## Proof depends on

- [The Laplace mechanism for vector-valued queries](../laplace-and-exponential-mechanisms/laplace-mechanism-pi-differentially-priv.md)
- [Post-processing by a measurable map](../differential-privacy/map.md)

## Sources

- C. Li, M. Hay, V. Rastogi, G. Miklau and A. McGregor, "Optimizing Linear Counting Queries Under Differential Privacy", PODS 2010, arXiv:0912.4742v2, Proposition 2 (Laplace mechanism for a query matrix) and Definition 3.2 (pseudo-inverse estimate) and Proposition 3 (matrix mechanism) with its proof.
- C. Li, G. Miklau, M. Hay, A. McGregor and V. Rastogi, "The matrix mechanism: optimizing linear counting queries under differential privacy", The VLDB Journal 24 (2015) 757–781: Proposition 4 (Laplace mechanism), Definition 8 (derivation through the Moore–Penrose pseudoinverse), Definition 9 and Proposition 6 (the matrix mechanism inherits the privacy guarantee of the mechanism answering the strategy).
