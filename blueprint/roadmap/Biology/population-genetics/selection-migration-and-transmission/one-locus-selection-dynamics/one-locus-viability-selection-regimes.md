# Directional selection, overdominance and underdominance at one locus

Consider one diploid locus with alleles $A$ and $a$ in an infinite randomly mating population with
nonoverlapping generations and constant nonnegative genotype viabilities $w_{AA}, w_{Aa}, w_{aa}$.
If $p \in [0, 1]$ is the frequency of $A$ among newborns (in Hardy–Weinberg proportions),
$q = 1 - p$ and the mean viability $\bar w = p^2 w_{AA} + 2pq w_{Aa} + q^2 w_{aa}$ is positive,
viability selection changes the frequency of $A$ to $p' = p\,(p w_{AA} + q w_{Aa})/\bar w$, and

$$p' - p = \frac{pq\,[\,p (w_{AA} - w_{Aa}) + q (w_{Aa} - w_{aa})\,]}{\bar w}.$$

This identity is algebraic: with $p' = p\,(p w_{AA} + q w_{Aa})/\bar w$ it holds for every real $p$
and all real viabilities with $\bar w \ne 0$, although $p'$ is then not necessarily a frequency.
Let $p_0 \in (0, 1)$ and $p_{n+1} = p_n'$.

1. **Directional selection.** Let $w_{AA} \ge w_{Aa} \ge w_{aa} \ge 0$, not all equal (that is,
   $w_{aa} < w_{AA}$). Then $w_{AA} > 0$ and $\bar w > 0$ on $(0, 1]$. If $w_{Aa} > 0$, then
   $p_n \in (0, 1)$ for all $n$, $p_n$ increases strictly and $p_n \to 1$; if
   $w_{Aa} = w_{aa} = 0$, then $p_1 = 1$.
2. **Overdominance.** Write $w_{AA} = 1 - s$, $w_{Aa} = 1$, $w_{aa} = 1 - t$ with $0 < s, t \le 1$ (zero
   homozygote viabilities are allowed; $\bar w \ge 2pq > 0$ on $(0, 1)$). The only fixed point in
   $(0, 1)$ is $p_e = t/(s + t)$, and $p_n \to p_e$ monotonically, without overshooting $p_e$: if
   $p_0 \le p_e$, then $p_n$ is nondecreasing and $p_n \le p_e$ for all $n$; if $p_0 \ge p_e$, then
   $p_n$ is nonincreasing and $p_n \ge p_e$ for all $n$.
3. **Underdominance.** With the same parametrization and $s, t < 0$, $p_e = t/(s + t) \in (0, 1)$ is the
   only interior fixed point; $p_n \to 0$ if $p_0 < p_e$, $p_n \to 1$ if $p_0 > p_e$, and $p_n = p_e$
   for all $n$ if $p_0 = p_e$.

Whenever $w_{AA} = 1 - s$, $w_{Aa} = 1$ and $w_{aa} = 1 - t$ for real $s$ and $t$, as in cases 2
and 3, $\bar w - pq(s + t) = p(1 - s) + q(1 - t)$ for every real $p$, and, if $s + t \ne 0$ (as in
cases 2 and 3), $p' - p = pq(s + t)(p_e - p)/\bar w$ for every real $p$ with $\bar w \ne 0$, with
$p'$ the quotient above; like the change formula, these are algebraic identities. In case 2, for
$p \in (0, 1)$, $p(1 - s) + q(1 - t) \ge 0$, so the factor $pq(s + t)/\bar w$ lies in $(0, 1]$,
and it equals $1$ exactly when $s = t = 1$, in which case $p_1 = p_e$; this gives monotone
convergence without overshooting.

## Sources

- J. Felsenstein, *Theoretical Evolutionary Genetics* (GENOME 562 course text, University of Washington, version of December 2019), <https://felsenst.github.io/pgbook/pgbook.pdf>, Section II.4 "Selection in Diploids", equation (II-31) and the form of $\Delta p$ derived from it, pp. 62–63; Section II.7 "Overdominance and Underdominance", equations (II-101)–(II-102), pp. 84–89
  (the change in gene frequency, the interior equilibrium, the sign analysis and the global
  behaviour under overdominance and underdominance), and Chapter II, Complements/Problems,
  Problem 15, p. 135 (no overshooting under overdominance).
