# Benefit-to-cost rule b/c > k on regular graphs

In the donation game a cooperator pays cost $c > 0$ to give benefit $b > c$ to its partner, and a defector pays nothing and gives nothing. With cooperators as $A$ and defectors as $B$, the payoffs are $R = b - c$, $S = -c$, $T = b$, $P = 0$. By the [sigma rule](sigma-rule-for-strategy-selection-under-weak-selection.md), cooperation is favoured under weak selection iff

$$\sigma(b - c) - c > b \iff (\sigma - 1)\,b > (\sigma + 1)\,c .$$

- If $\sigma > 1$, this is $\dfrac{b}{c} > \dfrac{\sigma + 1}{\sigma - 1}$.
- If $\sigma \le 1$, it never holds for $b, c > 0$; in particular cooperation is never favoured in a well-mixed population ($\sigma = (N-2)/N < 1$).

For a large $k$-regular graph with death–birth updating, $\sigma = (k+1)/(k-1)$ gives $(\sigma+1)/(\sigma-1) = k$, so cooperation is favoured iff

$$\frac{b}{c} > k .$$

## Depends on

- [Sigma rule for strategy selection under weak selection](sigma-rule-for-strategy-selection-under-weak-selection.md)

## Expansion

Substituting the donation-game payoffs into $\sigma R + S > T + \sigma P$ and collecting terms gives $(\sigma - 1)b > (\sigma + 1)c$. With $\sigma = (k+1)/(k-1)$, $\sigma + 1 = 2k/(k-1)$ and $\sigma - 1 = 2/(k-1)$, whose ratio is $k$. The rule says that sparse networks (small $k$) support cooperation, because a cooperator's benefits stay among neighbours who are likely cooperators themselves; as $k$ grows the graph approaches a well-mixed population and the required benefit-to-cost ratio diverges.

## Sources

- M. A. Nowak, C. E. Tarnita, T. Antal, "Evolutionary dynamics in structured populations", Philosophical Transactions of the Royal Society B 365 (2010) 19–30, <https://doi.org/10.1098/rstb.2009.0215> (PMC2842709).
- H. Ohtsuki, C. Hauert, E. Lieberman, M. A. Nowak, "A simple rule for the evolution of cooperation on graphs and social networks", Nature 441 (2006) 502–505, <https://doi.org/10.1038/nature04605>.
