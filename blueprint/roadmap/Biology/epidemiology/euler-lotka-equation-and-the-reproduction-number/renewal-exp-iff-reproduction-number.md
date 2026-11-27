# Euler–Lotka equation for the reproductive number

Let $g$ be a probability measure on $\mathbb{R}$ (the law of the generation interval), let
$r, c, R \in \mathbb{R}$ with $c \ne 0$, and suppose $a \mapsto e^{-ra}$ is $g$-integrable. Then the
exponential $b(t) = c\,e^{rt}$ satisfies the renewal equation

$$b(t) = R \int b(t - a) \, g(da) \quad \text{for every } t \in \mathbb{R}$$

if and only if $R = 1 / M_g(-r)$, the [reproductive number](reproduction-number.md) of $g$ at growth
rate $r$, where $M_g(-r) = \int e^{-ra} \, g(da)$.
