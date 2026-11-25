# Mutation–selection balance for a recessive allele

Consider one diploid locus in an infinite randomly mating population with nonoverlapping generations:
genotypes $AA$, $Aa$, $aa$ have viabilities $1$, $1$, $1 - s$ with $0 < s \le 1$, and after selection each
$A$ gene mutates to $a$ with probability $u \in (0, 1)$, with no back mutation. If $p$ is the frequency of
$A$ among newborns (in Hardy–Weinberg proportions), the next generation has

$$p' = \frac{p\,(1 - u)}{1 - s (1 - p)^2},$$

provided the mean fitness of the newborns $1 - s(1 - p)^2$ is positive, that is, $s < 1$ or $p > 0$. If
$s = 1$ and $p = 0$, all newborns are $aa$ and die, and no generation follows; this state is excluded.

In terms of the mutant frequency $q = 1 - p$ this is the
[one-generation selection–mutation map](diploid-step.md) with heterozygote cost $0$ and homozygote
cost $s$. Within this domain the fixed points are $p = 0$ (for $s < 1$) and the solutions in $[0, 1]$ of
$s (1 - p)^2 = u$. If
$0 < u < s$, the interior equilibrium has mutant frequency exactly

$$q_e = 1 - p_e = \sqrt{u/s},$$

and the mean fitness of the newborns there is $1 - s q_e^2 = 1 - u$, so the mutational load is $u$,
independent of $s$. If $u \ge s$ (so $s < 1$), the only fixed point in $[0, 1]$ is $p = 0$.

## Sources

- J. Felsenstein, *Theoretical Evolutionary Genetics* (GENOME 562 course text, University of Washington, version of December 2019), <https://felsenst.github.io/pgbook/pgbook.pdf>, Section III.6 "Mutation vs. Selection: Effects of Dominance", equations (III-19)–(III-24),
  pp. 149–150.
