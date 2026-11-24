# The predictive rule of the urn

Let $X$ be a measurable space, $\alpha \in \mathbb{R}$, $H$ an s-finite measure on $X$, $n \in \mathbb{N}$ and $A_0, \dots, A_n \subseteq X$ measurable. Under the [Blackwell–MacQueen urn law](blackwell-mac-queen.md) $P_{n+1}$ of $n + 1$ draws,

$$P_{n+1}(X_0 \in A_0, \dots, X_n \in A_n) = \int_{A_0 \times \dots \times A_{n-1}} Q_{x_0, \dots, x_{n-1}}(A_n)\, P_n(dx_0 \cdots dx_{n-1}),$$

where $Q_{x_0, \dots, x_{n-1}}$ is the [Pólya urn predictive law](../dirichlet-process/polya-urn-predictive.md) given the previous draws; for $\alpha > 0$, $Q_{x_0, \dots, x_{n-1}}(A_n) = \big(\alpha H(A_n) + \#\{i < n : x_i \in A_n\}\big)/(\alpha + n)$.
