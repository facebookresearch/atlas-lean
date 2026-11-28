# Antithetic integral feedback and stochastic set-point tracking

Augment an open-loop stochastic reaction network with the antithetic integral controller of Briat, Gupta and Khammash (2016): species $Z_1$ is born at rate $\mu$ (the reference reaction), species $Z_2$ is born at rate $\theta X_\ell$ (the measurement reaction, proportional to the regulated species $X_\ell$), $Z_1 + Z_2 \to \emptyset$ at rate $\eta Z_1 Z_2$, and $Z_1$ actuates the network with gain $k$. Subtracting the moment equations of the two controller species gives $\frac{d}{dt}E[Z_1(t) - Z_2(t)] = \mu - \theta E[X_\ell(t)]$ (Eq. (3)). Theorem 1 states: if the closed-loop network is ergodic and has uniformly bounded first- and second-order moments, then $E[X_\ell(t)] \to \mu/\theta$ as $t \to \infty$. Theorem 2 states: if the open-loop network is unimolecular with irreducible state space, its first-moment linear system is asymptotically stable (Hurwitz) and output controllable, and the set-point $\mu/\theta$ is accessible, then for every $k, \eta > 0$ the closed-loop network is ergodic and $E[X_\ell(t)] \to \mu/\theta$.

## Expansion

1. The model: the open-loop network, the four controller reactions and the closed-loop continuous-time Markov chain.
2. The moment identity (3), its integrated form (4), and the derivation of Theorem 1 from ergodicity and bounded moments.
3. Theorem 2: ergodicity of the closed loop under the stated conditions (7) and (8), proved in the supplementary material of the source, and the steady-state values of the first moments.
4. The deterministic counterpart, [integral feedback gives perfect adaptation](../../../Biology/systems-biology/integral-feedback-and-perfect-adaptation/has-perfect-adaptation-of-has-integral-f.md), as background.

## Sources

- C. Briat, A. Gupta and M. Khammash, Antithetic integral feedback ensures robust perfect adaptation in noisy biomolecular networks, Cell Syst. 2 (2016), 15–26, Eq. (3) and Theorems 1 and 2. <https://arxiv.org/abs/1410.6064>
