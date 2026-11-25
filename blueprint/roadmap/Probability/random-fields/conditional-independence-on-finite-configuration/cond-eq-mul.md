# Conditional independence in ratio form

Let $V$ and $\alpha$ be finite types, let $p$ be a
real-valued weight on the configurations $x : V \to \alpha$, and for $U \subseteq V$ write
$p(x_U)$ for the marginal of $p$ on $U$ at $x$. If, for $A, B, S \subseteq V$, the variables in
$A$ and in $B$ are conditionally independent given those in $S$ under $p$, then every
configuration $x$ with $p(x_S) \ne 0$ satisfies

$$\frac{p(x_{A\cup B\cup S})}{p(x_S)} = \frac{p(x_{A\cup S})}{p(x_S)}\frac{p(x_{B\cup S})}{p(x_S)}$$

For a nonnegative weight of positive total mass these ratios are the conditional probabilities of
the normalized distribution, so this is $P(x_A, x_B \mid x_S) = P(x_A \mid x_S)\, P(x_B \mid x_S)$.
