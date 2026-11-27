# Directional selection, overdominance and underdominance at one locus

Consider one diploid locus with alleles $A$ and $a$ in an infinite randomly mating population with
nonoverlapping generations and constant nonnegative genotype viabilities $w_{AA}, w_{Aa}, w_{aa}$, with
positive mean viability $\bar w$ at every frequency used below. If $p$
is the frequency of $A$ among newborns (in Hardy–Weinberg proportions) and
$\bar w = p^2 w_{AA} + 2pq w_{Aa} + q^2 w_{aa}$ with $q = 1 - p$, viability selection gives

$$p' - p = \frac{pq\,[\,p (w_{AA} - w_{Aa}) + q (w_{Aa} - w_{aa})\,]}{\bar w}.$$

Let $p_0 \in (0, 1)$ and $p_{t+1} = p_t'$.

1. **Directional selection.** Let $w_{AA} \ge w_{Aa} \ge w_{aa}$, not all equal (so $w_{AA} > 0$ and
   $\bar w > 0$ on $(0, 1]$). If $w_{Aa} > 0$, then $p_t \in (0, 1)$ for all $t$, $p_t$ increases strictly
   and $p_t \to 1$; if $w_{Aa} = w_{aa} = 0$, then $p_1 = 1$.
2. **Overdominance.** Write $w_{AA} = 1 - s$, $w_{Aa} = 1$, $w_{aa} = 1 - t$ with $0 < s, t \le 1$ (zero
   homozygote viabilities are allowed; $\bar w \ge 2pq > 0$ on $(0, 1)$). The only fixed point in $(0, 1)$ is $p_e = t/(s + t)$, and $p_t \to p_e$ monotonically, without
   overshooting $p_e$.
3. **Underdominance.** With the same parametrization and $s, t < 0$, $p_e = t/(s + t) \in (0, 1)$ is the
   only interior fixed point; $p_t \to 0$ if $p_0 < p_e$, $p_t \to 1$ if $p_0 > p_e$, and $p_t = p_e$
   for all $t$ if $p_0 = p_e$.

In the parametrization of cases 2 and 3, $p' - p = pq(s + t)(p_e - p)/\bar w$. In case 2 the factor
$pq(s + t)/\bar w$ lies in $(0, 1]$, since $\bar w - pq(s + t) = p(1 - s) + q(1 - t) \ge 0$, with equality
only when $s = t = 1$, in which case $p_1 = p_e$; this gives monotone convergence without overshooting.

## Sources

- J. Felsenstein, *Theoretical Evolutionary Genetics* (GENOME 562 course text, University of Washington, version of December 2019), <https://felsenst.github.io/pgbook/pgbook.pdf>, Section II.4 "Selection in Diploids", equation (II-31) and the form of $\Delta p$ derived from it, pp. 62–63; Section II.7 "Overdominance and Underdominance", equations (II-101)–(II-102), pp. 84–87
  (the change in gene frequency, the interior equilibrium and the sign analysis), and Chapter II,
  Exercise 15, p. 135 (no overshooting under overdominance).
