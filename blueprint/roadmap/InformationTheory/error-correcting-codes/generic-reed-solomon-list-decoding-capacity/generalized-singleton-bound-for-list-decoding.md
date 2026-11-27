# Generalized Singleton bound for list decoding (Shangguan-Tamo)

Let $C \subseteq \Sigma^n$ with $|\Sigma| = q$, let $L \ge 1$ be an integer, and suppose $C$ is $(\rho, L)$-list decodable, i.e. every Hamming ball of radius $\rho n$ contains at most $L$ codewords. Put $e = \lfloor \rho n \rfloor$ and $a = \lfloor (L+1)e/L \rfloor$, and assume the nontrivial regime $a \le n$. Then

$$
|C| \le L\, q^{\,n - a} .
$$

If moreover $C$ is a linear $[n, k]$ code over $\mathbb{F}_q$ with $q > L$, the factor $L$ can be dropped: $k \le n - a$. Without $q > L$ the linear form fails: the full binary code of length one is $(1, 2)$-list decodable, with $e = a = 1$, but $k = 1 > n - a = 0$. Asymptotically, a $(\rho, L)$-list decodable code of rate $R = \log_q |C| / n$ satisfies $\rho \le \frac{L}{L+1}(1 - R) + o(1)$. For $L = 1$ this is the Singleton bound.

## Proof sketch

Suppose $|C| > L q^{n-a}$. By pigeonhole some $L + 1$ distinct codewords $c_1, \dots, c_{L+1}$ agree on the first $n - a$ coordinates. Split the last $a$ coordinates into blocks $I_1, \dots, I_{L+1}$ of sizes $\lfloor a/(L+1) \rfloor$ or $\lceil a/(L+1) \rceil$, and let $y$ agree with the common value on the first $n - a$ coordinates and with $c_j$ on its own block $I_j$. Then $c_j$ can differ from $y$ only on the other blocks, so $\mathrm{wt}(c_j - y) \le a - |I_j| \le a - \lfloor a/(L+1) \rfloor \le e$, and the ball of radius $e$ around $y$ contains $L + 1$ codewords. For a linear code, $q^k \le L q^{n-a} < q^{\,n-a+1}$ when $q > L$, and since $k$ is an integer this gives $k \le n - a$.

## Depends on

- [List-decodable code](../list-decoding/is-list-decodable.md)
- [Singleton bound](../bounds-on-code-size/singleton-bound.md)

## Sources

- Chong Shangguan, Itzhak Tamo, "Combinatorial list-decoding of Reed-Solomon codes beyond the Johnson radius", STOC (2020); arXiv:1911.01502, Theorem 1.2.
