# Monogamy-of-entanglement game for BB84 states

In the game where a referee prepares $|x\rangle_\theta$ for uniformly random $x,\theta\in\{0,1\}^{n}$, an adversary splits it into a bipartite state held by two non-communicating players, and then both players receive $\theta$ and must each output $x$, the optimal winning probability over all quantum strategies is exactly $\bigl(\frac{1}{2}+\frac{1}{2\sqrt{2}}\bigr)^{n}\approx 0.854^{n}$.

## Proof sketch

The winning probability equals $\|\frac{1}{2^{n}}\sum_\theta\sum_x|x\rangle\langle x|_\theta\otimes P^{\theta}_x\otimes Q^{\theta}_x\|$ maximized over measurements; a norm bound for sums of products of projectors (overlap lemma) gives $\frac{1}{2}+\frac{1}{2\sqrt{2}}$ per qubit, and a strategy based on a state aligned between the two bases achieves it. Parallel repetition is perfect by the product structure.

## Depends on

- [Wiesner's private-key quantum money](wiesner-quantum-money.md)

## Sources

- Marco Tomamichel, Serge Fehr, Jędrzej Kaniewski, Stephanie Wehner, "A Monogamy-of-Entanglement Game with Applications to Device-Independent Quantum Cryptography", New Journal of Physics (2013).
