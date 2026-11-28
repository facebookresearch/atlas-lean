# Smith–Fretwell optimal offspring size

A parent with reproductive budget $R > 0$ makes $N = R/s$ offspring of size $s > 0$ (treating $N$ as continuous), and an offspring that receives parental investment $s$ has fitness $f(s) \ge 0$. Assume there is a minimum size $s_0 > 0$ such that $f$ is continuous on $[0, \infty)$, $f = 0$ on $[0, s_0]$, $f$ is differentiable, increasing and strictly concave on $(s_0, \infty)$, and $f$ is bounded or $f(s)/s \to 0$ as $s \to \infty$. Parental fitness is $W(s) = R f(s)/s$, which vanishes on $(0, s_0]$ and is positive beyond, and $W'(s) = R\,(s f'(s) - f(s))/s^2$ for $s > s_0$. Hence every maximizer $s^*$ lies in $(s_0, \infty)$ and satisfies

$$f'(s^*) = \frac{f(s^*)}{s^*},$$

that is, the straight line through the origin with slope $f(s^*)/s^*$ is tangent to the offspring fitness curve at $s^*$, and $s^*$ maximizes $f(s)/s$; it does not depend on the budget $R$. This is the graphical model of Smith and Fretwell (1974): offspring fitness increases with parental effort per offspring, and "a straight line through the origin is tangent to the curve at the optimum effort per offspring", so that for any given environment there is one optimal amount of resource for a parent to spend on each offspring (Smith's Citation Classic commentary). Under these hypotheses the maximizer of $f(s)/s$ exists, because $f(s)/s$ is continuous on $[s_0, \infty)$, zero at $s_0$, positive beyond and tends to $0$ at infinity; and it is unique, because if the line $y = cs$ through the origin touched the graph of $f$ at two maximizers $s_1 < s_2$ while lying above it, strict concavity would put the graph strictly above the line between $s_1$ and $s_2$. Without the condition at infinity a maximizer need not exist: for $s_0 = 2$ and $f(s) = s - 1 - e^{-(s-2)}$ on $(2, \infty)$, $f(s)/s$ increases to $1$ without attaining it.

## Expansion

1. The model: a fixed budget, continuous offspring number, and the offspring fitness function.
2. The first-order condition and its tangent-line form.
3. Existence and uniqueness of the maximizer of $f(s)/s$ under the minimum-size, strict concavity and growth hypotheses, and the counterexample without the growth hypothesis.
4. Independence of $s^*$ from the budget $R$.

## Sources

- C. C. Smith, The optimal balance between size and number of offspring, Citation Classic commentary, Current Contents 1990, no. 7.
- Original result: C. C. Smith and S. D. Fretwell, The optimal balance between size and number of offspring, Am. Nat. 108 (1974), 499–506. <https://doi.org/10.1086/282929> The tangent construction follows Smith's Citation Classic commentary.
