# Random self-reduction for discrete logarithms, with iteration

In a fixed group of prime order $q$, let $A$ compute the discrete logarithm of a uniform element with probability $\varepsilon$. For any target $u$, the algorithm that draws a uniform $r$, runs $A$ on $u \cdot g^{r}$, and subtracts $r$ from the answer succeeds with probability exactly $\varepsilon$, for every $u$. Iterating with fresh $r$ and checking each answer, $\lceil n/\varepsilon\rceil$ (or $2n \cdot \mathrm{invEps}(n)$ for a polynomial-time computable $\mathrm{invEps} \ge 1/\varepsilon$) attempts compute the discrete logarithm of every $u$ with failure probability at most $e^{-n}$. The same exact self-reduction holds for CDH.

## Proof sketch

$u g^r$ is uniform and independent of $u$, so each attempt succeeds with probability $\varepsilon$; answers can be verified by exponentiation, and independent attempts fail together with probability $(1 - \varepsilon)^{k}$.

## Depends on

- [Discrete-logarithm experiment](../../hardness-assumptions/dlog-game.md)
- [Computational Diffie–Hellman experiment](../../hardness-assumptions/cdh-game.md)

## Proof depends on

- [Repeated simulation attempts with independent success coins](../../../security-games/computational-indistinguishability-of-ensembles/repeated-attempts-with-independent-success-coins.md)

## Sources

- S. D. Galbraith, "Mathematics of Public Key Cryptography", Cambridge University Press, 2012, Chapter 2 (random self-reducibility of the discrete logarithm problem and amplification) and Section 21.3.
