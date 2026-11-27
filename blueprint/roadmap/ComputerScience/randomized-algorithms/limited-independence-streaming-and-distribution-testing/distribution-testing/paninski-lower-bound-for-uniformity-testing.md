# Paninski's lower bound for uniformity testing

Every uniformity tester on $n$ points with proximity $\delta$ (in total variation distance) needs $\Omega(\sqrt n/\delta^2)$ samples. This matches the $O(\sqrt n/\delta^2)$ upper bound, so the sample complexity of uniformity testing is $\Theta(\sqrt n/\delta^2)$.

## Proof sketch

For even $n$, pair up the points and, for a uniformly random sign vector $\sigma \in \{\pm1\}^{n/2}$, give the two points of pair $j$ masses $(1 + 2\delta\sigma_j)/n$ and $(1 - 2\delta\sigma_j)/n$; each such distribution is $\delta$-far from uniform. The mixture over $\sigma$ of the $k$-sample product distributions is close to the uniform product distribution: Paninski bounds their total variation distance by $\tfrac12\sqrt{e^{c k^2\delta^4/n} - 1}$ for an absolute constant $c$, which is below $1/3$ when $k \le c'\sqrt n/\delta^2$, so no tester with that many samples succeeds with probability $2/3$. (Derived, not stated by the sources: with the chi-square divergence of the mixture at most $\exp(16k^2\delta^4/n) - 1$, a tester with success probability $2/3$ needs total variation distance at least $1/3$, hence chi-square divergence at least $4/9$, so $16k^2\delta^4 \ge n\ln(13/9) \ge 0.36\,n$; for even $n$ and $\delta \le 1/2$ every $k$-sample tester therefore satisfies $n \le 45\,k^2\delta^4 \le 52\,k^2\delta^4$, and at $\delta = 1/2$ this is the birthday-type bound $4n \le 13k^2$.)

## Depends on

- [Sample-based distribution testers](sample-based-distribution-testers.md)

## Sources

- L. Paninski, "A Coincidence-Based Test for Uniformity Given Very Sparsely Sampled Discrete Data", IEEE Transactions on Information Theory 54(10), 2008: the lower-bound construction.
- C. L. Canonne, "A Survey on Distribution Testing: Your Data is Big. But is it Blue?", Theory of Computing Graduate Surveys 9, 2020: Theorem 5.1 (uniformity testing with $O(\sqrt n/\varepsilon^2)$ samples, and tightness), Section 5.1 (Paninski's matching $\Omega(\sqrt n/\varepsilon^2)$ lower bound) and Appendix E.2 (the total variation estimate).
