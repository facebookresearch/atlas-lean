# The length is the maximum over the prime-power parts of the modulus

For integers $m' \ge 1$ and $n \ge 1$, let $L_{m'}(n)$ be the length of the basic Ducci sequence in $\mathbb{Z}_{m'}^n$: the least $\alpha \ge 0$ such that $D^{\alpha + \beta}(u) = D^{\alpha}(u)$ for some $\beta \ge 1$, where $D(x_1, \dots, x_n) = (x_1 + x_2, \dots, x_n + x_1)$ and $u = (0, \dots, 0, 1)$. Let $n$ be even, let $t \ge 1$, let $p_1 < p_2 < \dots < p_t$ be primes, and let $k_i \ge 1$ and $l_i \ge 1$ be integers with

$$n = p_1^{k_1} \cdots p_t^{k_t}\, n_1, \qquad m = p_1^{l_1} \cdots p_t^{l_t}\, m_1,$$

where $m \ge 1$, $\gcd(n_1, m_1) = 1$ and no $p_i$ divides $n_1$ or $m_1$. Then

$$L_m(n) = \max_{1 \le i \le t} L_{p_i^{l_i}}(n).$$

The hypothesis $t \ge 1$ is needed for the maximum to be over a nonempty set.

## Sources

- Mark L. Lewis and Shannon M. Tefft, *The Maximum Length for Ducci Sequences on $\mathbb{Z}_m^n$ when $n$ is Even*, INTEGERS 26 (2026), Article A17, Theorem 1, part 4.
