# Lower bounds and inversions of the binary relative entropy

Let $\mathrm{kl}$ denote binary relative entropy in nats and let $c \ge 0$.

1. For $0 \le q \le p < 1$ with $p > 0$: $\dfrac{(p-q)^2}{2p} \le \mathrm{kl}(q\,\|\,p)$.
2. For $q \in [0,1]$ and $p \in (0,1)$: if $\mathrm{kl}(q\|p) \le c$ then $|p - q| \le \sqrt{c/2}$.
3. For $0 \le q$ and $p < 1$: if $\mathrm{kl}(q\|p) \le c$ then $p \le q + c + \sqrt{c^2 + 2qc}$, and hence $p \le q + \sqrt{2qc} + 2c$.
4. For $p \in [0,1)$: if $\mathrm{kl}(0\|p) \le c$ then $p \le 1 - e^{-c} \le c$.

## Proof sketch

Item 1 follows by comparing second derivatives in $q$ on $[q, p]$, where the curvature $1/(x(1-x))$ is at least $1/p$. Item 2 is the binary Pinsker inequality $2(p-q)^2 \le \mathrm{kl}(q\|p)$. Item 3 solves the quadratic inequality $(p-q)^2 \le 2pc$ from item 1 for $p$ (the case $q > p$ being trivial), and $\sqrt{c^2 + 2qc} \le c + \sqrt{2qc}$. Item 4 is $\mathrm{kl}(0\|p) = -\ln(1-p)$.

## Depends on

- [Binary relative entropy](binary-relative-entropy.md)

## Proof depends on

- [Binary Pinsker inequality on the closed interval](../binary-pinsker-of-mem-icc.md)

## Sources

- I. O. Tolstikhin and Y. Seldin, "PAC-Bayes-Empirical-Bernstein Inequality", Advances in Neural Information Processing Systems, 2013.
- T. M. Cover and J. A. Thomas, "Elements of Information Theory", Wiley-Interscience, 2nd ed., 2006.
