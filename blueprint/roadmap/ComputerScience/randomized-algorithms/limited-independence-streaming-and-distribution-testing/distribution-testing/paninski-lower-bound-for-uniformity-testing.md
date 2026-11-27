# Paninski's lower bound for uniformity testing

For even $n$ and proximity $\delta \le 1/2$, every $k$-sample uniformity tester on $n$ points satisfies $n \le 52\, k^2 \delta^4$; hence $\Omega(\sqrt n/\delta^2)$ samples are necessary, matching the $O(\sqrt n/\delta^2)$ sample bound of the collision tester. At $\delta = 1/2$ this is the birthday-type bound $4n \le 13 k^2$.

## Proof sketch

Pair up the points and, for a uniformly random sign vector $\sigma \in \{\pm1\}^{n/2}$, give the two points of pair $j$ masses $(1 + 2\delta\sigma_j)/n$ and $(1 - 2\delta\sigma_j)/n$; each such distribution is $\delta$-far from uniform. The mixture over $\sigma$ of the $k$-sample product distributions is close to the uniform product distribution: its chi-square divergence is at most $\exp(16k^2\delta^4/n) - 1$. A tester with success probability $2/3$ needs total variation distance at least $1/3$, hence chi-square divergence at least $4/9$, so $16k^2\delta^4 \ge n\ln(13/9) \ge 0.36\,n$, which gives $n \le 45\,k^2\delta^4 \le 52\,k^2\delta^4$. Paninski proves the $\Omega(\sqrt n/\delta^2)$ bound with this construction; the explicit constant comes from the computation above.

## Depends on

- [Sample-based distribution testers](sample-based-distribution-testers.md)

## Sources

- L. Paninski, "A Coincidence-Based Test for Uniformity Given Very Sparsely Sampled Discrete Data", IEEE Transactions on Information Theory 54(10), 2008: the lower-bound construction.
- C. L. Canonne, "A Survey on Distribution Testing: Your Data is Big. But is it Blue?", Theory of Computing Graduate Surveys 9, 2020.
