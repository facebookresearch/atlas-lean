# Dejean's theorem on repetition thresholds

For a natural number $n$ and a real number
$r$, call an infinite word $w = w_0 w_1 w_2 \cdots$ over the alphabet $\{0, \dots, n-1\}$
*$r^+$-free* if for all natural numbers $s$, $\ell$ and $p$ with $0 < p \le \ell$ such that
$w_{s+i+p} = w_{s+i}$ for every natural number $i$ with $i + p < \ell$, we have $\ell / p \le r$;
that is, no factor of $w$ has exponent strictly greater than $r$. Let $\mathrm{RT}(n)$, the
repetition threshold, be the infimum of the set of real numbers $r > 1$ for which there is an
infinite $r^+$-free word over $\{0, \dots, n-1\}$. Then $\mathrm{RT}(2) = 2$,
$\mathrm{RT}(3) = 7/4$, $\mathrm{RT}(4) = 7/5$, and $\mathrm{RT}(n) = n/(n-1)$ for every
$n \ge 5$.

This is a proved result (Dejean's conjecture of 1972): the last cases were proved in 2011 by
Currie and Rampersad and, independently, by Rao.

Paper: James D. Currie, Lucas Mol, and Narad Rampersad, "The Number of Threshold
Words on n Letters Grows Exponentially for Every n ≥ 27", Journal of Integer
Sequences 23 (2020), Article 20.3.1.

## Sources

- Period/exponent and `r`/`r⁺`-free definitions, lines 93--99; repetition-threshold definition and exact values, lines 100--113. Original definition/conjecture: Françoise Dejean, "Sur un théorème de Thue", Journal of Combinatorial Theory, Series A 13(1) (1972), 90--99, DOI 10.1016/0097-3165(72)90011-8. Final cases confirmed in 2011 by James D. Currie and Narad Rampersad, "A proof of Dejean's conjecture", Mathematics of Computation 80 (2011), 1063--1070, arXiv:0905.1129, and independently by Michaël Rao, "Last cases of Dejean's conjecture", Theoretical Computer Science 412(27) (2011), 3010--3018, DOI 10.1016/j.tcs.2010.06.020. Lean representation: `Fin n` harmlessly relabels the source `n`-letter alphabet `A_n`; the universal period clause expresses absence of factors with exponent strictly greater than `r`, i.e. `r⁺`-freeness; `RT` is the real-valued `sInf` over `r > 1` admitting such an infinite word.
- <https://cs.uwaterloo.ca/journals/JIS/VOL23/Mol/mol2.tex>.
