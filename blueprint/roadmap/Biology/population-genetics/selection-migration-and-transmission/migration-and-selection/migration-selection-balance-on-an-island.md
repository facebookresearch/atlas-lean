# Migration–selection balance on an island

A haploid population on an island receives immigrants from a continent fixed for allele $a$. On the
island allele $A$ has fitness $1$ and $a$ fitness $1 - s$ with $0 < s \le 1$; each generation selection
acts and then a fraction $m \in (0, 1]$ of the island population is replaced by immigrants. Exclude
$m = s = 1$: then the island consists of immigrants after the first generation, all of them die in the
next selection step, and the recursion has no next generation. If $p$ is the
frequency of $A$ on the island,

$$p' = \frac{p\,(1 - m)}{1 - (1 - p)s},$$

whose denominator is positive whenever $s < 1$ or $p > 0$.

- If $m < s$, the interior equilibrium is $p_e = 1 - m/s$ (the continental allele has frequency
  exactly $m/s$), and $p_t \to p_e$ monotonically from every $p_0 \in (0, 1]$.
- If $m \ge s$, then $p_t \to 0$: immigration swamps the locally favoured allele.

For $m < 1$ the recursion is that of
[haploid mutation–selection balance](../../mutation-selection-balance/haploid-mutation-selection-balance.md)
with the mutation probability $u$ replaced by $m$, and both statements are that page's convergence
statements. For $m = 1$ (so $s < 1$), $p_1 = 0$ and $p_t = 0$ for all $t \ge 1$.

## Proof depends on

- [Mutation–selection balance in a haploid population](../../mutation-selection-balance/haploid-mutation-selection-balance.md)

## Sources

- J. Felsenstein, *Theoretical Evolutionary Genetics* (GENOME 562 course text, University of Washington, version of December 2019), <https://felsenst.github.io/pgbook/pgbook.pdf>, Section IV.8 "Migration vs. Selection: Patches of Adaptation", equations (IV-23)–(IV-26),
  pp. 186–188.
