# Hypotheses of the linear-gap log-odds correspondence

For a finite alphabet, a real [pair HMM](pair-hmm.md), transition weights $\pi$, an end weight $\tau$, background frequencies $q$, a real $\eta$, integer substitution scores $\sigma$ and an integer gap score $g$, the linear-gap log-odds hypotheses are

- the pair HMM is [memoryless](is-memoryless.md) with $\pi$ and $\tau$;
- $\pi(M) + \pi(X) + \pi(Y) + \tau = 1$;
- $\sum_a q(a) = 1$, $\sum_{a,b} e_M(a, b) = 1$, $\sum_a e_X(a) = 1$ and $\sum_b e_Y(b) = 1$;
- $\pi(s) > 0$ for every emitting state, $\tau > 0$, $q(a) > 0$ for every letter, and $0 < \eta < 1$;
- $e_M(a, b) > 0$, $e_X(a) > 0$ and $e_Y(b) > 0$ for all letters;
- for all letters $a, b$:

$$\log \frac{\pi(M)\, e_M(a, b)}{(1 - \eta)^2 q(a) q(b)} = \sigma(a, b), \qquad \log \frac{\pi(X)\, e_X(a)}{(1 - \eta) q(a)} = g, \qquad \log \frac{\pi(Y)\, e_Y(b)}{(1 - \eta) q(b)} = g.$$
