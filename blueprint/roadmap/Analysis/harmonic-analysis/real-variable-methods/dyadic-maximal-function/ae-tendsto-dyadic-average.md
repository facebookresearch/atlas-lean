# Dyadic differentiation of the norm of an integrable function

Let $f \colon \mathbb{R} \to E$ with $x \mapsto \|f(x)\|$ a.e. measurable and $\int \|f\| < \infty$. Then for almost every $x$,

$$\lim_{n \to \infty} A_n f(x) = \|f(x)\|,$$

where $A_n f(x)$ is the [average](dyadic-average.md) of $\|f\|$ over the level-$n$ [dyadic interval](dyadic-interval.md) containing $x$. This is the dyadic case, applied to $\|f\|$, of T. Hytönen, *Dyadic analysis and weights*, lecture notes, University of Helsinki, version of 2 May 2014, Theorem 5.1 (Lebesgue's differentiation theorem along cubes containing $x$ with side length tending to $0$), in dimension one. It is weaker than the source in two respects: it differentiates $\|f\|$ rather than $f$, and it assumes $f \in L^1$ rather than $f \in L^1_{\mathrm{loc}}$. The full statement, for the averages of $f$ itself and locally integrable $f$, is the [dyadic Lebesgue differentiation theorem](ae-tendsto-set-average-dyadic-interval.md); this extended-real form is the one the Calderón–Zygmund decomposition uses.

The proof uses Vitali-family differentiation rather than a dyadic covering argument. Lebesgue measure on $\mathbb{R}$ is uniformly locally doubling, so the Vitali family of closed balls differentiates every integrable function; the closed intervals $[m 2^{-n}, (m+1) 2^{-n}]$ containing $x$, closed balls of radius $2^{-n-1}$, converge to $x$ along that family, and they differ from the half-open dyadic intervals by a null set.

## Informally uses

- [Dyadic interval](dyadic-interval.md): its agreement with a closed ball up to a null set.

## Background

- [Lebesgue differentiation along shrinking off-center intervals](../../../../Probability/stochastic-calculus/it-integral/ae-tendsto-average-icc.md): a stronger real-valued statement, for locally integrable $f$ and any intervals $[a_n, b_n]$ of lengths tending to $0$ whose midpoints stay within twice their length of the point, again from Vitali-family differentiation.

## Sources

- T. Hytönen, *Dyadic analysis and weights*, lecture notes, University of Helsinki, version of 2 May 2014 (a secondary source: lecture notes presenting the dyadic theory of C. Fefferman and E. M. Stein, *Some maximal inequalities*, Amer. J. Math. 93 (1971), 107–115, and of E. M. Stein, *Harmonic Analysis*, Princeton University Press, 1993).
