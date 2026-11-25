# Prime-rich translates give short gaps between the $j$-th and $(j+m)$-th primes

Let $p_0 = 2 < p_1 = 3 < \cdots$ be the primes, indexed from $0$. Let $H$ be a finite set of natural numbers with $b \le a + D$ for all $a, b \in H$. If infinitely many $n$ have more than $m$ of the $n + h$, $h \in H$, prime, then

$$p_{j + m} - p_j \le D \quad \text{for infinitely many } j,$$

that is $\liminf_j (p_{j+m} - p_j) \le D$. This is the step "In particular, $\liminf_n (p_{n + r_k - 1} - p_n) \le \max_{1 \le i, j \le k} (h_i - h_j)$" of Maynard (2015), Proposition 4.2, with $r_k - 1 = m$.

Proof idea: if $n + a$ is the least prime among the $n + h$ and $j$ is its index, then the $m + 1$ primes among the $n + h$ lie in $[p_j, p_j + D]$, so $p_{j+m} \le p_j + D$; and $j \to \infty$ as $n \to \infty$.

## Background

- [Liminf of prime gaps](../../prime-gaps-short-intervals/prime-gaps/prime-gap-liminf.md): the case $m = 1$ of the quantity bounded here.

## Related topics

- [Maynard's explicit bound for gaps between $m + 1$ primes](../../prime-gaps-short-intervals/bounded-gaps-between-primes/frequently-nth-prime-add-sub-le-cube-mul.md): the theorem whose last step this is.

## Sources

- J. Maynard, "Small gaps between primes", *Ann. of Math.* 181 (2015), 383–413; theorem and display numbers are those of arXiv:1311.4600v3 (28 Oct 2019).
