# Few inputs lack a second preimage, and inversion is at most twice as easy as second preimages

Let $H : M \to T$ with $M, T$ finite and $s \cdot |T| \le |M|$ for some $s > 0$. (a) At most a $1/s$ fraction of inputs $m$ have no $m' \ne m$ with $H(m') = H(m)$. (b) For every inverter $A$ and the second-preimage finder $B(m) = A(H(m))$,

$$\Pr_m[A(H(m)) \in H^{-1}(H(m))] \le 2\,\Pr_m[B(m) \ne m,\ H(B(m)) = H(m)] + \frac{1}{s}.$$

## Proof sketch

(a) Inputs without a sibling are alone in their fiber, so there are at most $|T| \le |M|/s$ of them. (b) For $m$ in a fiber of size $c \ge 2$, the inverter's answer is independent of which element of the fiber was sampled, so it differs from $m$ with probability at least $1 - 1/c \ge 1/2$ times the inversion probability.

## Depends on

- [Second-preimage resistance](second-preimage-resistance.md)
- [Inversion experiment](../../security-games/asymptotic-security/invert-game.md)

## Sources

- D. Boneh and V. Shoup, "A Graduate Course in Applied Cryptography", draft textbook, version 0.6, 2023.
