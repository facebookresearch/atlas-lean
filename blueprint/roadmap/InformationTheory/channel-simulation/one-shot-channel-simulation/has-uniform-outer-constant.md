# Uniform outer constant for channel simulation

A real number $\alpha$ is a uniform
outer constant when there is a real $\beta > 0$ such that for every finite joint law $p$ of
$(X, Y)$ there is a finite extension of $p$ by an auxiliary variable $S$ with $I(X; S) = 0$
and $H(Y \mid X, S) = 0$ and

$$H(Y \mid S) \le I(X; Y) + \log_2\bigl(I(X; Y) + \beta\bigr) + \alpha,$$

where all entropies and mutual informations are in bits and are computed from the law of
$(X, Y, S)$ in the extension.
