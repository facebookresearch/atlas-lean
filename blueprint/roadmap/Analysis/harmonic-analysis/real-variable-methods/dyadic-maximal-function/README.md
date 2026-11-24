# Dyadic maximal function

The dyadic intervals $I_{k,m} = [m 2^{-k}, (m+1) 2^{-k})$ of the real line are nested: two of them are either disjoint or one contains the other. The [dyadic maximal function](dyadic-maximal-function.md) $M_d f(x)$ is the supremum of the averages of $\|f\|$ over the dyadic intervals containing $x$. Real-variable harmonic analysis in the tradition of C. Fefferman and E. M. Stein (*Some maximal inequalities*, Amer. J. Math. 93 (1971), 107–115; E. M. Stein, *Harmonic Analysis*, Princeton University Press, 1993) rests on one stopping-time idea, presented in T. Hytönen, *Dyadic analysis and weights*, lecture notes, University of Helsinki, version of 2 May 2014, §§1, 3, 5 and 7, which these pages follow:

1. **Stopping time.** For a height $c$, the maximal dyadic intervals with average above $c$ are disjoint ([stopping level](is-stopping-level.md), [finite-level estimate](mul-volume-window-le.md)).
2. **Weak type (1,1).** Summing over these disjoint intervals gives $c\,|\{M_d f > c\}| \le \int_{\{M_d f > c\}} \|f\|$ ([localized form](mul-volume-lt-dyadic-maximal-function-le.md), [weak type (1,1)](dyadic-maximal-function-mul-volume-le-li.md)), valid for every $f$, with constant $1$ and no covering lemma.
3. **Differentiation.** For locally integrable $f$ the averages of $f$ over the dyadic intervals containing $x$ converge to $f(x)$ almost everywhere ([dyadic Lebesgue differentiation](ae-tendsto-set-average-dyadic-interval.md)); the form used below, for the averages of $\|f\|$ with $f$ integrable, is [its norm version](ae-tendsto-dyadic-average.md). Both follow from Vitali-family differentiation; hence $\|f\| \le M_d f$ a.e. ([domination](ae-enorm-le-dyadic-maximal-function.md)).
4. **Strong type.** Integrating the localized bound gives the [Doob-type inequality](lintegral-rpow-le-lintegral-mul-dyadic-m.md) $\int (M_d f)^p \le p' \int \|f\| (M_d f)^{p-1}$, and with Hölder's inequality the [$L^p$ bound](lintegral-rpow-dyadic-maximal-function-l.md) $\|M_d f\|_p \le p' \|f\|_p$, $p' = p/(p-1)$, for $1 < p < \infty$; the Marcinkiewicz splitting gives the [cruder constant $2^p p/(p-1)$](lintegral-rpow-dyadic-maximal-le-two-rpo.md) without any finiteness assumption, which the sharp proof needs.
5. **Calderón–Zygmund decomposition.** For integrable $f$ the stopping intervals at height $c$ exist ([existence](exists-is-stopping-level.md)), partition $\{M_d f > c\}$, carry averages in $(c, 2c]$, and $\|f\| \le c$ a.e. off their union ([dyadic Calderón–Zygmund decomposition](calderon-zygmund.md)).

The decomposition is the entry point for the weak type (1,1) of singular integrals, the John–Nirenberg inequality (see Related topics) and the [Fefferman–Stein vector-valued inequality](exists-lintegral-tsum-rpow-dyadic-maxima.md). Everything here is on $\mathbb{R}$; the sources work on $\mathbb{R}^d$ with dyadic cubes, where the constant $2$ in step 5 becomes $2^d$.

- [Dyadic interval](dyadic-interval.md)
- [Dyadic index](dyadic-index.md)
- [Nesting of dyadic intervals](dyadic-index-of-le.md)
- [Dyadic average](dyadic-average.md)
- [Dyadic maximal function](dyadic-maximal-function.md)
- [Stopping-time estimate on finitely many levels](mul-volume-window-le.md)
- [Weak type (1,1) of the dyadic maximal function, localized form](mul-volume-lt-dyadic-maximal-function-le.md)
- [Weak type (1,1) of the dyadic maximal function](dyadic-maximal-function-mul-volume-le-li.md)
- [Doob-type inequality for the dyadic maximal function](lintegral-rpow-le-lintegral-mul-dyadic-m.md)
- [$L^p$ bound for the dyadic maximal function with constant $2^p p/(p-1)$](lintegral-rpow-dyadic-maximal-le-two-rpo.md)
- [$L^p$ bound for the dyadic maximal function](lintegral-rpow-dyadic-maximal-function-l.md)
- [Dyadic Lebesgue differentiation theorem for locally integrable functions](ae-tendsto-set-average-dyadic-interval.md)
- [Dyadic differentiation of the norm of an integrable function](ae-tendsto-dyadic-average.md)
- [Pointwise domination by the dyadic maximal function](ae-enorm-le-dyadic-maximal-function.md)
- [Stopping level](is-stopping-level.md)
- [Existence of the stopping level](exists-is-stopping-level.md)
- [Calderón–Zygmund decomposition, dyadic form](calderon-zygmund.md)
- [Dyadic Fefferman–Stein vector-valued maximal inequality](exists-lintegral-tsum-rpow-dyadic-maxima.md)

## Related topics

- [Bounded mean oscillation](../bounded-mean-oscillation/README.md): the John–Nirenberg inequality and the $H^1$–$\mathrm{BMO}$ inequality, built on the Calderón–Zygmund decomposition.
- [Hardy–Littlewood maximal function](../../../../MeasureTheory/real-functions/hardy-littlewood-maximal-function/README.md): the maximal function over all intervals containing a point, used there in statements with an inline definition; on $\mathbb{R}$ it is at most $6$ times the larger of the dyadic maximal functions of the standard and of one shifted dyadic system (Hytönen's notes, Proposition 2.9), so the bounds here transfer to it.
- [Lebesgue differentiation along shrinking off-center intervals](../../../../Probability/stochastic-calculus/it-integral/ae-tendsto-average-icc.md): a real-valued differentiation theorem along any intervals $[a_n, b_n]$ with lengths tending to $0$ and $|u - (a_n + b_n)/2| \le 2(b_n - a_n)$; it contains the real-valued case of the dyadic theorem, since $x$ lies in its dyadic interval $I_n(x)$, at distance at most half the length from the midpoint.
- [Haar system](../../wavelets/haar-system/README.md): the Haar wavelets live on the same dyadic intervals; for $f \in L^2$, the averages of $f$ over the level-$k$ dyadic intervals are the orthogonal projection of $f$ onto the Haar approximation space $V_k$ of S. Mallat's multiresolution framework ($A_k f$ is the same average taken for $\|f\|$).
- [Convergence of Fourier series](../../fourier-series/convergence-of-fourier-series/README.md): Carleson's theorem on almost-everywhere convergence is proved by a time–frequency refinement of these stopping-time arguments.
- [Doob's maximal inequalities](../../../../Probability/martingales/doob-s-maximal-inequalities/README.md): for $f$ integrable on $[0,1)$ the dyadic averages form a martingale and the weak type (1,1) bound is Doob's maximal inequality.
- [Fundamental solutions of the Laplacian](../../../potential-theory/fundamental-solutions-of-the-laplacian/README.md): the Calderón–Zygmund decomposition is the tool behind $L^p$ bounds for the second derivatives of the Newton potential $\Gamma * f$, the singular integrals that motivate the theory.
