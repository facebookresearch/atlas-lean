# Allele frequency change under meiotic drive without viability differences

Consider one diploid locus with alleles $A$ and $a$ in an infinite randomly mating population with
nonoverlapping generations and no viability differences, in which heterozygotes of both sexes transmit
$A$ with probability $k \in [0, 1]$ and $a$ with probability $1 - k$ ($k = 1/2$ is Mendelian
segregation), and homozygotes transmit their own allele. If the newborns are in Hardy–Weinberg
proportions, $p \in [0, 1]$ is the frequency of $A$ among them and $q = 1 - p$, then the newborns of the
next generation are again in Hardy–Weinberg proportions and the frequency of $A$ among them is
$p' = p^2 + 2pq\,k$; after $t$ generations it is $p_t$, the $t$-th iterate of $p \mapsto p'$ at
$p_0 = p$. As an identity in $p$,

$$p' - p = pq\,(2k - 1).$$

Consequently $p' \in [0, 1]$, and for $p_0 \in (0, 1)$: if $k > 1/2$, then $p_t$ increases strictly and
$p_t \to 1$; if $k < 1/2$, then $p_t$ decreases strictly and $p_t \to 0$; if $k = 1/2$, then $p_t = p_0$.
Indeed the adults have the newborns' genotype frequencies $p^2$, $2pq$, $q^2$, so their gametes carry $A$
with frequency $p^2 + 2pq\,k$, and random union of gametes gives Hardy–Weinberg proportions with that
frequency. Further, $p - pq \le p' \le p + pq = p(2 - p) \le 1$, the only fixed points of
$p \mapsto p + pq(2k - 1)$ for $k \ne 1/2$ are $0$ and $1$, and $p_t$ stays in $(0, 1)$ because $p' - p$
has the sign of $2k - 1$ and $p' < 1$, $p' > 0$ for $p \in (0, 1)$.

## Sources

- J. Felsenstein, *Theoretical Evolutionary Genetics* (GENOME 562 course text, University of Washington, version of December 2019), <https://felsenst.github.io/pgbook/pgbook.pdf>, Chapter II, Complements/Problems, Problem 19, p. 135 (the meiotic-drive model with drive in both sexes,
  heterozygotes producing a fraction $(1 + \alpha)/2$ of $A$ gametes, that is $k = (1 + \alpha)/2$; the
  problem asks for the change in gene frequency; the convergence statement is derived from it).
