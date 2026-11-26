# The LOS greedy mechanism is truthful and √m-approximate

Order single-minded bids by $v_i / \sqrt{|S_i|}$ (ties broken by a fixed order) and greedily accept bids whose bundles are disjoint from all previously accepted ones, charging each winner its critical value. This mechanism is DSIC, and for every nonnegative bid profile and every set $\mathrm{OPT}$ of pairwise disjoint bids, its welfare is at least $\frac{1}{\sqrt m} \sum_{i \in \mathrm{OPT}} v_i$, where $m \ge 1$ is the number of items.

## Proof sketch

The greedy rule is monotone. Charge each optimal bid to the first accepted bid that blocks it; for an accepted bid $i$ blocking a set $B_i$ of optimal bids, each blocked bid has ratio at most that of $i$, the blocked bundles are disjoint and each meets $S_i$, so $|B_i| \le |S_i|$, and Cauchy–Schwarz gives $\sum_{j \in B_i} v_j \le \frac{v_i}{\sqrt{|S_i|}} \sum_{j \in B_i} \sqrt{|S_j|} \le \frac{v_i}{\sqrt{|S_i|}} \sqrt{|B_i|} \sqrt{m} \le \sqrt{m}\, v_i$.

## Depends on

- [Single-minded bidders and combinatorial auction mechanisms](single-minded-bidders-and-combinatorial-auction-mechanisms.md)

## Proof depends on

- [Characterization of truthful mechanisms for single-minded bidders](characterization-of-truthful-mechanisms-for-single-minded-bidders.md)

## Sources

- Liad Blumrosen and Noam Nisan, "Combinatorial Auctions", Algorithmic Game Theory, Cambridge University Press, 2007.
- Ron Lavi, "Computationally Efficient Approximation Mechanisms", Algorithmic Game Theory, Cambridge University Press, 2007.
