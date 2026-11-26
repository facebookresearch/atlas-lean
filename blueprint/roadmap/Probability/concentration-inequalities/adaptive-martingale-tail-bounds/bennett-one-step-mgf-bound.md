# Bennett's one-step moment generating function bound

For every $b > 0$ and every real $u \le b$,

$$
e^{u} - 1 - u \le \frac{u^2}{b^2}\big(e^{b} - 1 - b\big),
$$

because $u \mapsto (e^u - 1 - u)/u^2$ is nondecreasing on $\mathbb{R}$. Consequently, if $X$ is a real random variable on a probability space with $\mathbb{E}[X] \le 0$, $X \le b$ almost surely for some $b > 0$, and $\mathbb{E}[X^2] \le v$, then for every $t \ge 0$

$$
\mathbb{E}\big[e^{tX}\big] \le \exp\Big(\frac{v}{b^2}\big(e^{tb} - 1 - tb\big)\Big).
$$

The same bound holds for a discrete distribution on an arbitrary countable or uncountable outcome set, with the hypotheses imposed on its support.

## Proof sketch

Apply the scalar inequality to $u = tX \le tb$: $e^{tX} \le 1 + tX + X^2 (e^{tb} - 1 - tb)/b^2$. Taking expectations and using $\mathbb{E}[X] \le 0$, $t \ge 0$ and $\mathbb{E}[X^2] \le v$ bounds the moment by $1 + \frac{v}{b^2}(e^{tb} - 1 - tb)$, and $1 + y \le e^y$ finishes.

## Sources

- G. Bennett, "Probability Inequalities for the Sum of Independent Random Variables", Journal of the American Statistical Association 57, 1962.
- D. A. Freedman, "On Tail Probabilities for Martingales", The Annals of Probability 3(1), 1975.
