# Survival function of the chi-square distribution

For $p \in \mathbb{N}$, let $\chi^2_p$ be the gamma law on $\mathbb{R}$ with shape $p/2$ and rate $1/2$, the measure with Lebesgue density $x \mapsto \frac{(1/2)^{p/2}}{\Gamma(p/2)} x^{p/2 - 1} e^{-x/2}$ for $x > 0$ and $0$ for $x < 0$ (for $p = 0$ this is the zero measure, with the conventions $\Gamma(0) = 0$ and division by $0$ giving $0$). The chi-square survival function is

$$S_p(c) = \chi^2_p\bigl((c, \infty)\bigr) \in [0, \infty], \qquad c \in \mathbb{R},$$

which for $p \ge 1$ is $P(\chi^2_p > c)$.
