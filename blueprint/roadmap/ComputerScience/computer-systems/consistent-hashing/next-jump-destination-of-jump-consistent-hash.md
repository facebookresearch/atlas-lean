# Next jump destination of jump consistent hash

For the idealized [jump consistent hash](jump-consistent-hash.md) and a fixed key, call $j \ge 1$ a jump destination if $U_j < 1/(j+1)$, and let $b$ be $0$ or a jump destination. The next jump destination after $b$, $J = \min\{j > b : U_j < 1/(j+1)\}$, satisfies

$$
\Pr[J \ge i] = \frac{b + 1}{i} \qquad \text{for every integer } i > b ,
$$

independently of the earlier jumps. Hence $J$ has the law of $\lfloor (b + 1)/r \rfloor$ with $r$ uniform on $(0, 1)$, which lets the algorithm generate the jump destinations directly, stopping at the first one that is at least $n$; the bucket returned is the last destination below $n$.

## Depends on

- [Jump consistent hash](jump-consistent-hash.md)

## Proof depends on

- [Jump consistent hash is uniform and monotone](jump-consistent-hash-is-uniform-and-monotone.md): $\Pr[ch(k, i) = ch(k, b+1)] = (b+1)/i$.

## Sources

- J. Lamping and E. Veach, "A fast, minimal memory, consistent hash algorithm", arXiv:1406.2294, 2014, <https://arxiv.org/abs/1406.2294>, section "Explanation of the algorithm" (the derivation of $P(j \ge i) = (b+1)/i$ and $j = \lfloor (b+1)/r \rfloor$, and the logarithmic-time algorithm).
