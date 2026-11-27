# Bucket-load concentration for Feistel routing

Route keys $x = (x_L, x_R) \in [2^s] \times [T]$ to buckets in $[2^s]$ by the left half of the one-round Feistel image, $x \mapsto x_L \oplus f(x_R)$, with the round function $f : [T] \to [2^s]$ drawn from a $k$-wise independent family. Then distinct keys with the same right half go to distinct buckets, and each key is recovered from its bucket and right half. For a fixed set of $n$ distinct keys and a fixed bucket $y$, the load $X$ of $y$ is a sum of indicators $X_j \in \{0, 1\}$, one per distinct right half $z_j$ and each determined by $f(z_j)$, that are $k$-wise independent with $\mathbb{E}[X] = \mu = n / 2^s$; hence, for $0 < \delta \le 1$ and $k \le \delta^2 \mu e^{-1/3}$, $\Pr[|X - \mu| \ge \delta \mu] \le e^{-\lfloor k/2 \rfloor}$. In particular (Li, Liang, Yu and Zhou, Lemma 5.1 and Corollary B.5), if $k \ge 10 \ln n$, $s$ is sufficiently large and $n \ge 2^s s^4$, then with probability at least $1 - 1/(4n^2)$ every bucket receives between $\mu - \frac{1}{5}\mu^{2/3}$ and $\mu + \frac{1}{5}\mu^{2/3}$ keys.

## Proof sketch

Keys sharing a right half are mapped by a fixed exclusive or, which is injective, so each right half $z_j$ contributes at most one key to bucket $y$, and $\mathbb{E}[X_j] = |I_j| / 2^s$ where $I_j$ is the set of keys with right half $z_j$. The tail bound is the Chernoff–Hoeffding bound for $k$-wise independent variables of Schmidt, Siegel and Srinivasan (Theorem 5). For the last claim take $\delta = \frac{1}{5}\mu^{-1/3}$, check $\lceil 10 \ln n \rceil \le \delta^2 \mu e^{-1/3}$ from $n \ge 2^s s^4$, apply the bound with $\lceil 10 \ln n \rceil$ in place of $k$, so that each bucket fails with probability at most $e^{-5 \ln n + 1} \le 1/(4n^3)$, and take a union bound over the $2^s \le n$ buckets.

## Depends on

- [One-round Feistel permutations on mixed domains](one-round-feistel-on-mixed-domains.md)
- [k-wise independent hash family](../word-ram-hash-families/k-wise-independent-hash-family.md)

## Sources

- T. Li, J. Liang, H. Yu and R. Zhou, "Dynamic Dictionary with Subconstant Wasted Bits per Key", Proceedings of the 2024 ACM-SIAM Symposium on Discrete Algorithms (SODA), pp. 171-207, 2024; arXiv:2310.20536.
- Y. Arbitman, M. Naor and G. Segev, "Backyard Cuckoo Hashing: Constant Worst-Case Operations with a Succinct Representation", Proceedings of the 51st IEEE Symposium on Foundations of Computer Science (FOCS), pp. 787-796, 2010.
- J. P. Schmidt, A. Siegel and A. Srinivasan, "Chernoff-Hoeffding Bounds for Applications with Limited Independence", SIAM Journal on Discrete Mathematics 8(2), pp. 223-250, 1995.
