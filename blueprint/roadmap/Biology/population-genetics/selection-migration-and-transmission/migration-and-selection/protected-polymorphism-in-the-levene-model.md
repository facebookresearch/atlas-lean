# Protected polymorphism in the Levene model

In Levene's model a single randomly mating pool of a diploid population produces offspring in
Hardy–Weinberg proportions, which are distributed among $n$ niches; in niche $i$ the genotypes $AA$,
$Aa$, $aa$ have viabilities $w_i, 1, v_i$ with $w_i, v_i > 0$, and after selection niche $i$ contributes
the fixed fraction $c_i > 0$ of the next mating pool ($\sum_i c_i = 1$). If $p$ is the frequency of $A$ in
the pool,

$$p' = F(p) = \sum_{i=1}^n c_i \, \frac{p^2 w_i + p(1 - p)}{p^2 w_i + 2p(1 - p) + (1 - p)^2 v_i} .$$

Then $F(0) = 0$, $F(1) = 1$, $F'(0) = \sum_i c_i / v_i$ and $F'(1) = \sum_i c_i / w_i$. Hence:

- if $\sum_i c_i / v_i > 1$, then $A$ increases when rare: $F(p) > p$ for all sufficiently small $p > 0$;
- if $\sum_i c_i / w_i > 1$, then $a$ increases when rare: $F(p) < p$ for all $p < 1$ close enough to $1$;
- if both hold, the polymorphism is protected, and $F$ has a fixed point in $(0, 1)$.

If $\sum_i c_i / v_i < 1$ (respectively $\sum_i c_i / w_i < 1$), the boundary $p = 0$ (respectively
$p = 1$) is locally attracting. The conditions compare the heterozygote's viability $1$ with the
weighted harmonic means of the homozygote viabilities.

**Haploid case.** If in niche $i$ the haploid types $A$ and $a$ have viabilities in the ratio $a_i : 1$
($a_i > 0$), then

$$p' = F(p) = \sum_{i=1}^n c_i \, \frac{p\,a_i}{p\,a_i + 1 - p} .$$

This is the diploid map with $w_i = a_i$ and $v_i = 1/a_i$: multiplying the numerator and denominator of
the $i$-th term of the diploid map by $a_i$ gives $p\,a_i\,(p\,a_i + 1 - p)/(p\,a_i + 1 - p)^2$. Hence
$F'(0) = \sum_i c_i a_i$ and $F'(1) = \sum_i c_i / a_i$. Moreover, $A$ is protected ($F(p) > p$ for all
sufficiently small $p > 0$) if and only if $\sum_i c_i a_i > 1$, and $a$ is protected ($F(p) < p$ for
all $p < 1$ close enough to $1$) if and only if $\sum_i c_i / a_i > 1$. For the boundary case,
$F(p) = p \sum_i c_i a_i - p^2 \sum_i c_i a_i (a_i - 1) + O(p^3)$; if $\sum_i c_i a_i = 1$, then
$F(p) - p = -p^2 (\sum_i c_i a_i^2 - 1) + O(p^3)$, and $\sum_i c_i a_i^2 \ge (\sum_i c_i a_i)^2 = 1$ with
equality only when every $a_i = 1$, in which case $F(p) = p$; so $A$ is not protected. The statement for
$a$ follows by exchanging the two types, which replaces $a_i$ by $1/a_i$.

## Sources

- J. Felsenstein, *Theoretical Evolutionary Genetics* (GENOME 562 course text, University of Washington, version of December 2019), <https://felsenst.github.io/pgbook/pgbook.pdf>, Section IV.10 "The Levene Model: High Migration", equations (IV-42)–(IV-46), pp. 196–198.
