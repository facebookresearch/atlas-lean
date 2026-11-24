# Expectation of a function of a history with the random-joining law

Let $\mu$ be a probability measure on a measurable space $(\Omega, \mathcal{A})$, $m$ a natural
number, $b$ a list of natural numbers, and $\tau$ a map from $\Omega$ to lists of block-size lists
such that $\tau^{-1}(A) \in \mathcal{A}$ for every set $A$ of such lists, with law given by the
[random-joining law](random-joining.md):

$$\mu(\tau = \mathbf{p}) = R_m(b, \mathbf{p}) \quad \text{for every } \mathbf{p}.$$

Let $F$ be a finite set of lists of block-size lists with $R_m(b, \mathbf{p}) = 0$ for every
$\mathbf{p} \notin F$. Then for every real function $g$ on lists of block-size lists, $g \circ \tau$
is $\mu$-integrable and

$$\int g(\tau)\, d\mu = \sum_{\mathbf{p} \in F} R_m(b, \mathbf{p})\, g(\mathbf{p}).$$
