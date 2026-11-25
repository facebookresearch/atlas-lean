# Hudson's $F_{ST}$ (ratio of averages)

For a finite set $s$ of sites and allele frequencies $p_A, p_B : s \to \mathbb{R}$, Hudson's $F_{ST}$ in ratio-of-averages form is (Bhatia et al. 2013)

$$F_{ST} = \frac{\sum_{i \in s} (p_{A,i} - p_{B,i})^2}{\sum_{i \in s} D(p_{A,i}, p_{B,i})},$$

where $D$ is [Hudson's denominator](hudson-den.md), with the convention $x/0 = 0$. For frequencies in $[0, 1]$, the denominator vanishes only when every site is fixed for the same allele in both populations.

## Sources

- G. Bhatia, N. Patterson, S. Sankararaman, A. L. Price, *Estimating and interpreting $F_{ST}$: the impact of rare variants*, Genome Res. 23 (2013), 1514–1521.
