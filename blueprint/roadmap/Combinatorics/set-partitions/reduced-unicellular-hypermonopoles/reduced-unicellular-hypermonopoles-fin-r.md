# Vanishing of the reduced unicellular hypermonopole counts

Let $\sigma_n$ be the cyclic
permutation $i \mapsto i + 1$ (modulo $n$) of $\{0, 1, \dots, n - 1\}$, write $z(\pi)$ for the
number of cycles of a permutation $\pi$, fixed points included, and let $r(n, k)$ be the number
of permutations $\alpha$ of $\{0, 1, \dots, n - 1\}$ with no fixed point such that
$z(\alpha^{-1} \circ \sigma_n) = 1$ and $z(\alpha) = k$. Then $r(n, k) = 0$ for all natural
numbers $n$ and $k$ with $n - k$ odd; $r(3, k) > 0$ for some natural number $k$ with $2k \le 3$;
and $r(n, k) = 0$ whenever $n < 3$ and $2k \le n$.

So the least $n$ with $r(n, k) > 0$ for some $k \le n / 2$ is $n = 3$. In the terms of the
source, $r(n, k)$ counts the reduced unicellular hypermonopoles $(\sigma_n, \alpha)$ with
$\sigma_n = (1, \dots, n)$ and $z(\alpha) = k$.

## Sources

- Robert Cori and Gábor Hetyei, *On Reduced Unicellular Hypermonopoles*, Journal of Integer Sequences 28 (2025), Article 25.3.3, Corollary 13 (`jis-2025-25.3.3-cor-13`).
