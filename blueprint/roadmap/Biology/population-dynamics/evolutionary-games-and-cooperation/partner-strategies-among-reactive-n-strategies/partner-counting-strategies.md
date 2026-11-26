# Partner conditions for reactive-n counting strategies

In the infinitely repeated donation game (cost $c > 0$, benefit $b > c$), a **reactive-$n$ counting strategy** is $r = (r_n, r_{n-1}, \dots, r_0) \in [0,1]^{n+1}$, where $r_i$ is the probability of cooperating when the co-player cooperated $i$ times during the last $n$ rounds, irrespective of when. Counting strategies are the reactive-$n$ strategies whose entries depend only on the number of $C$'s in the co-player's $n$-history (for $n = 2$: $p_{CD} = p_{DC}$); a player still needs the exact sequence of the co-player's last $n$ moves in order to update the count.

**Theorem.** A reactive-$n$ counting strategy $r$ is a partner (nice and a Nash equilibrium) if and only if

$$r_n = 1 \qquad\text{and}\qquad r_{n-k} \le 1 - \frac{k}{n}\cdot\frac{c}{b} \quad \text{for } k \in \{1, 2, \dots, n\}.$$

For every defection of the co-player in memory, the maximal admissible cooperation probability drops by $c/(nb)$: a partner's generosity decreases in proportion to the co-player's selfishness. The equilibrium property holds against all deviations, including strategies that do not merely count and strategies with memory longer than $n$. For $n = 1$ the theorem is the classical condition $p_C = 1$, $p_D \le 1 - c/b$ for reactive partners.

For sufficiently small cost-to-benefit ratios $c/b$, the volume of partners exceeds that of defector strategies, and the relative volume of partners compared with strategies that sustain stable mutual defection grows with $n$, both among reactive-$n$ strategies and among counting strategies, so randomly generated mutant strategies are increasingly likely to lie near partners as memory grows.

## Depends on

- [Self-reactive best responses to reactive-n strategies](self-reactive-best-responses-to-reactive-n-strategies.md)

## Proof sketch

Necessity: the self-reactive deviation that repeats a word of length $n$ with $k$ defections presents, over one period, the $n$ cyclic shifts of that word as co-player histories, each with exactly $n - k$ cooperations, so all are answered with probability $r_{n-k}$. The deviator then earns $n\,r_{n-k}\,b - (n-k)\,c$ per period, and requiring this to be at most $n(b - c)$ gives $r_{n-k} \le 1 - (k/n)(c/b)$. Sufficiency, i.e. that no other periodic deviation does better once these $n$ inequalities hold, is proved in the paper's supplementary information. For $n = 2$ the conditions are the reactive-2 partner conditions restricted to the plane $p_{CD} = p_{DC} = r_1$.

## Sources

- N. E. Glynatsi, E. Akin, M. A. Nowak, C. Hilbe, "Conditional cooperation with longer memory", Proceedings of the National Academy of Sciences USA 121(50) (2024) e2420125121, Eq. 3 and "Partners Among the Reactive-n Counting Strategies", <https://doi.org/10.1073/pnas.2420125121> (PMC11648855).
