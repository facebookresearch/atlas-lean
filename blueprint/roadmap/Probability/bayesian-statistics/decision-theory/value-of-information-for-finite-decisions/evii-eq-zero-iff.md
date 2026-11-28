# Equality condition for the value of information

Let the states $\Omega$ and evidence outcomes $\varepsilon$ be finite, let $w(\omega, e) \ge 0$ be joint weights, let a nonempty finite set of actions have utilities $U(a, \omega)$, and let the value of information be

$$\sum_e \max_a \sum_\omega w(\omega, e) U(a, \omega) \;-\; \max_a \sum_{\omega, e} w(\omega, e) U(a, \omega).$$

It is zero if and only if some single action $a$ is optimal under every evidence outcome $e$ with positive total weight $\sum_\omega w(\omega, e) > 0$: $\sum_\omega w(\omega, e) U(a', \omega) \le \sum_\omega w(\omega, e) U(a, \omega)$ for every action $a'$.
