# At least half of independent estimates are rarely bad

Let $\mu$ be a probability measure, $s \in \mathbb{N}$, and let $Y_1, \dots, Y_s$ be independent
measurable real random variables with $\mu(Y_i \notin [a, b]) \le 1/8$ for every $i$. Then

$$\mu\big(s \le 2 \cdot \#\{i : Y_i \notin [a, b]\}\big) \le e^{-9s/32} :$$

at least half of the $Y_i$ lie outside $[a, b]$ with probability at most $e^{-9s/32}$. The proof
applies Hoeffding's inequality to the indicators of the bad events (in the source, "the standard
estimate of Chernoff" plays this role with $s = 2 \log(1/\varepsilon)$).

## Informally uses

- [Hoeffding's inequality for averages](../hoeffding-s-inequality/measure-real-avg-sub-ge-le.md): applied to the indicators of the bad events, which are independent, take values in $[0, 1]$ and have mean at most $1/8$.

## Sources

- N. Alon, Y. Matias and M. Szegedy, *The space complexity of approximating the frequency
  moments*, Journal of Computer and System Sciences 58 (1999), 137–147, proof of Theorem 2.1.
