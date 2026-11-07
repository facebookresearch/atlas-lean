# Zhang's six-parameter binomial sum

For natural numbers $n$, $r_1$, $r_2$, $s$, $t$, $u$,
Zhang's binomial sum is

$$
V(n, r_1, r_2, s, t, u) = \sum_{k=0}^{n} \binom{n}{k}^{r_1} \binom{n}{2k}^{r_2}
\binom{n+k}{k}^{s} \binom{2k}{k}^{t} \binom{2(n-k)}{n-k}^{u}.
$$

The source uses the convention $0^0 = 1$, which is also Lean's convention for natural-number
powers.
