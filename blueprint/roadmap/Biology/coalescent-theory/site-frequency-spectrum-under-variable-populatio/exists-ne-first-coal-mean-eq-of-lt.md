# Tightness of the sample-size bound $n \ge 2K$

For every natural number $K \ge 2$, there are two [piecewise-constant histories](piecewise-history.md) with $K$ pieces whose [size functions](size-fn.md) differ at some time $s \ge 0$ but whose [first-coalescence times](first-coal-mean.md) agree for every $2 \le m \le 2K - 1$. So [Bhaskar–Song identifiability](size-fn-eq-of-first-coal-mean-eq.md) fails for $n = 2K - 1$. The construction is explicit: with $z = 2^{-\binom{m}{2}}$, the two histories have coalescent-time breakpoints $(2j-1) \log 2$ and $2j \log 2$, so $\binom{m}{2}(c_m - c'_m)$ is a polynomial of degree $2K - 2$ in $z$, whose coefficients are those of $\prod_{m=2}^{2K-1} (X - 2^{-\binom{m}{2}})$; it vanishes at the $2K - 2$ points and has a nonzero constant term, since the sizes at time $0$ differ.

## Sources

- A. Bhaskar and Y. S. Song, *Descartes' rule of signs and the identifiability of population demographic models from genomic variation data*, Ann. Statist. 42 (2014), 2469–2493; arXiv:1309.5056, remark after Corollary 7.
