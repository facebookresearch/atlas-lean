# Mutation–selection balance in a haploid population

In an infinite haploid population with discrete generations, let the wild-type allele $A$ have fitness
$1$ and the mutant $a$ fitness $1 - s$ with $0 < s \le 1$; each generation selection acts and then each
$A$ gene mutates to $a$ with probability $u \in (0, 1)$, with no back mutation. If $p$ is the frequency
of $A$, the next generation has

$$p' = \frac{p\,(1 - u)}{1 - (1 - p)s},$$

provided the mean fitness $1 - (1 - p)s$ is positive, that is, $s < 1$ or $p > 0$. If $s = 1$ and $p = 0$,
every individual has fitness $0$ and no generation follows (extinction); this state is excluded. If
$p > 0$ then $p' > 0$, so every trajectory started in $(0, 1]$ stays in $(0, 1]$ with positive mean
fitness.

For $s < 1$ the fixed points in $[0, 1]$ are $p = 0$ and, if $u < s$, $p = 1 - u/s$; for $s = 1$ the
map is defined on $(0, 1]$, where it is constant equal to $1 - u$. If $0 < u < s$, the mutant frequency at
the interior equilibrium is exactly

$$q_e = 1 - p_e = u/s,$$

$p_t \to p_e$ monotonically from every $p_0 \in (0, 1]$, and the mean fitness there is
$1 - s q_e = 1 - u$, so the mutational load is $u$, independent of $s$. If $u \ge s$ (so $s < 1$), then $p_t \to 0$.

The map $p \mapsto p(1 - u)/(1 - s + sp)$ is increasing on $[0, 1]$ for $s < 1$, and $p' - p$ has the sign
of $p_e - p$ on $(0, 1]$ when $u < s$ (of $-p$ when $u \ge s$), which gives monotone convergence to the
only fixed point in $(0, 1]$, respectively to $0$; for $s = 1$, $p_1 = 1 - u = p_e$.

## Sources

- J. Felsenstein, *Theoretical Evolutionary Genetics* (GENOME 562 course text, University of Washington, version of December 2019), <https://felsenst.github.io/pgbook/pgbook.pdf>, Section III.4 "Mutation versus Selection: Haploids", equations (III-13)–(III-18),
  pp. 146–148.
