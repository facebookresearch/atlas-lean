# Paninski's lower bound for uniformity testing

For even $n$ and proximity $\delta \le 1/2$, every $k$-sample uniformity tester on $n$ points satisfies $n \le 52\, k^2 \delta^4$; hence $\Omega(\sqrt n/\delta^2)$ samples are necessary, matching the $O(\sqrt n/\delta^2)$ sample bound of the collision tester. At $\delta = 1/2$ this is the birthday-type bound $4n \le 13 k^2$.

## Proof sketch

Pair up the points and, for a uniformly random sign vector $\sigma$, perturb the uniform distribution by $\pm 2\delta/n$ on each pair; each such distribution is $\delta$-far from uniform. The mixture over $\sigma$ of the $k$-sample product distributions is close to the uniform product distribution: its chi-square divergence is bounded by $\exp(O(k^2\delta^4/n)) - 1$, so a tester needs $k^2\delta^4 = \Omega(n)$.

## Depends on

- [Sample-based distribution testers](sample-based-distribution-testers.md)

## Sources

- L. Paninski, "A Coincidence-Based Test for Uniformity Given Very Sparsely Sampled Discrete Data", IEEE Transactions on Information Theory 54(10), 2008.
- C. L. Canonne, "A Survey on Distribution Testing: Your Data is Big. But is it Blue?", Theory of Computing Graduate Surveys 9, 2020.
