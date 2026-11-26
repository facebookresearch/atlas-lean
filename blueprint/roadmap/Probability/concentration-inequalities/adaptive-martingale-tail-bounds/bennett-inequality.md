# Bennett's inequality and its Bernstein relaxation

Let $h(u) = (1 + u)\ln(1 + u) - u$ for $u \ge 0$ (natural logarithm). Let $X$ be a real random variable with $X \le b$ almost surely for some $b > 0$ and suppose that for every $t \ge 0$, $\mathbb{E}[e^{tX}] \le \exp\big(\frac{v}{b^2}(e^{tb} - 1 - tb)\big)$ for some $v > 0$ (for instance, $\mathbb{E}[X] \le 0$ and $\mathbb{E}[X^2] \le v$). Then for every $\varepsilon \ge 0$,

$$
\Pr[X \ge \varepsilon] \le \exp\Big(-\frac{v}{b^2}\, h\Big(\frac{b\varepsilon}{v}\Big)\Big) \le \exp\Big(-\frac{\varepsilon^2}{2(v + b\varepsilon/3)}\Big).
$$

The second inequality uses $h(u) \ge \frac{u^2}{2(1 + u/3)}$ for all $u \ge 0$. Moreover, for $v, b \ge 0$ not both zero and $\delta \in (0, 1)$, the deviation $\varepsilon = \sqrt{2 v \ln(1/\delta)} + \frac{2}{3} b \ln(1/\delta)$ satisfies $\exp(-\varepsilon^2/(2(v + b\varepsilon/3))) \le \delta$.

## Proof sketch

By Markov's inequality, $\Pr[X \ge \varepsilon] \le \exp(\frac{v}{b^2}(e^{sb} - 1 - sb) - s\varepsilon)$ for all $s \ge 0$; the choice $s = \frac{1}{b}\ln(1 + b\varepsilon/v)$ evaluates the exponent exactly to $-\frac{v}{b^2} h(b\varepsilon/v)$. The lower bound on $h$ follows from comparing derivatives at $0$, giving Bernstein's rational tail. The inversion is the quadratic formula for the Bernstein exponent.

## Depends on

- [Bennett's one-step moment generating function bound](bennett-one-step-mgf-bound.md)

## Proof depends on

- [Bennett's one-step moment generating function bound](bennett-one-step-mgf-bound.md)

## Sources

- G. Bennett, "Probability Inequalities for the Sum of Independent Random Variables", Journal of the American Statistical Association 57, 1962.
- D. A. Freedman, "On Tail Probabilities for Martingales", The Annals of Probability 3(1), 1975.
