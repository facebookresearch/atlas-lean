# Availability of a two-state repairable component

A component alternates between up and down as a continuous-time Markov chain with failure rate $\lambda \ge 0$ (up to down) and repair rate $\mu \ge 0$ (down to up), started up with probability $p_0$. If $\lambda + \mu > 0$, the probability that it is up at time $t \ge 0$ is $A(t) = \frac{\mu}{\lambda + \mu} + \bigl(p_0 - \frac{\mu}{\lambda + \mu}\bigr)e^{-(\lambda + \mu)t}$, so $A(t) \to \mu/(\lambda + \mu)$ as $t \to \infty$; in particular $A(t) = 1$ for all $t$ when $\lambda = 0$ and $p_0 = 1$, and $A(t) \to 0$ when $\mu = 0 < \lambda$. If $\lambda = \mu = 0$, the generator is zero and the component keeps its initial state: $A(t) = p_0$ for every $t$.

Proof. For $\lambda + \mu > 0$ the transition function of the two-state generator is the sticky kernel $e^{tQ}(i, j) = e^{-(\lambda + \mu)t}[i = j] + (1 - e^{-(\lambda + \mu)t})\pi(j)$ with $\pi(\mathrm{up}) = \mu/(\lambda + \mu)$; average over the initial law. For $\lambda = \mu = 0$, $e^{tQ} = I$.

## Proof depends on

- [Transition function of the two-state chain](../../markov-chains/finite-continuous-time-markov-chains/the-sticky-equal-input-kernel-on-a-finite-state/ctmc-transition-two-state-rate.md): transition function of the two-state chain.
- [Long-distance limit of the sticky kernel](../../markov-chains/finite-continuous-time-markov-chains/the-sticky-equal-input-kernel-on-a-finite-state/tendsto-sticky-kernel-at-top.md): long-time limit of the sticky kernel.

## Sources

- The statement is derived on this page from its definitions and the linked results; no external source is followed.
