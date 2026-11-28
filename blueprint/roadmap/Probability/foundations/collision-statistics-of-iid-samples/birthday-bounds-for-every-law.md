# Birthday lower bounds for every sampling law

Let $\alpha$ be a finite set with $n$ elements, $\mu$ any distribution on $\alpha$, and $x_1, \dots, x_k$ i.i.d. from $\mu$. Then

$$
\Pr[\exists i<j:\ x_i = x_j] \ge 1 - e^{-k(k-1)/(2n)} \ge \min\Bigl(\frac{k(k-1)}{4n},\ 0.63\Bigr),
$$

and for the uniform law and $k < n/2$ the collision probability is also at most $1 - e^{-k(k-1)/n}$.

## Proof sketch

By the previous theorem the collision probability of any law is at least that of the uniform law, $1 - \prod_{i<k}(1 - i/n) \ge 1 - e^{-k(k-1)/(2n)}$. The second lower bound is the inequality $1 - e^{-x} \ge \min(x/2, 1 - e^{-1})$ applied to $x = k(k-1)/(2n)$. The uniform upper bound uses $1 - i/n \ge e^{-2i/n}$ for $i \le n/2$.

The following two clauses are derived here and are not stated in the cited source. By the union bound, $\Pr[\exists i<j:\ x_i = x_j] \le \binom{k}{2}\sum_a \mu(a)^2$ for every law, since $\Pr[x_i = x_j] = \sum_a \mu(a)^2$ for each pair. The uniform upper bound needs only $k - 1 \le n/2$, that is, $2k \le n + 2$, since the inequality $1 - x \ge e^{-2x}$ is used only on $[0, 1/2]$.

## Proof depends on

- [The uniform law minimizes the probability of a repeat among i.i.d. samples](uniform-law-minimizes-collisions.md)
- [Birthday lower bound, exponential form](../../../ComputerScience/cryptography/hash-functions/birthday-bound/one-sub-exp-le-collision-prob.md)

## Sources

- Dan Boneh and Victor Shoup, "A Graduate Course in Applied Cryptography", version 0.6, 2023, Appendix B, Theorem B.1 and Corollary B.2.
