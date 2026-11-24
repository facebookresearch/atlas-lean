# Joint distribution of a chain

For a chain of conditional distributions with values in
a type $\alpha$, write $p_k(\cdot \mid x_0, \dots, x_{k-1})$ for the conditional distribution of
variable $k$ given the earlier ones. The joint distribution $P_n : \alpha^n \to \mathbb{R}$ of
the first $n$ variables is defined by the chain rule: $P_0 = 1$ and
$P_{n+1}(x_0, \dots, x_n) = P_n(x_0, \dots, x_{n-1}) \, p_n(x_n \mid x_0, \dots, x_{n-1})$.
