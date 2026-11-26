# Fefferman's ball multiplier theorem

Let $n \ge 2$ and $1 \le p < \infty$ with $p \ne 2$, and let $B$ be the unit ball of $\mathbb{R}^n$. The Fourier multiplier of $B$,

$$Tf(x) = \int_B e^{2\pi i \langle \xi, x\rangle} \hat f(\xi)\, d\xi, \qquad \hat f(\xi) = \int_{\mathbb{R}^n} e^{-2\pi i \langle x, \xi\rangle} f(x)\, dx,$$

is unbounded on $L^p$: there is no finite $C$ with $\|Tf\|_p \le C\|f\|_p$ for every Schwartz function $f$.

This is Theorem 1 of C. Fefferman, *The multiplier problem for the ball*, Ann. of Math. 94 (1971), 330–336: "$T$ is bounded only on $L^2$ ($n > 1$)". The source includes $p = \infty$, which is not stated here, so the statement is slightly weaker. The statement uses the Fourier transform and its inverse with $2\pi$ in the exponent, a normalisation that differs from the source's; since $1_B$ is a multiplier on $L^p$ exactly when its dilates are, the radius and normalisation do not matter. For $f$ Schwartz, $1_B \hat f$ is integrable, so $Tf$ is a genuine continuous function and no integral defaults to $0$; for $p \le 2n/(n+1)$, $Tf$ is not even in $L^p$ in general, which the statement allows since its $L^p$ norm is then $+\infty$.

The proof reduces, by de Leeuw's theorem and duality, to $p > 2$ in the plane; a lemma of Y. Meyer turns boundedness of $T$ into a vector-valued inequality for half-plane multipliers, which a Besicovitch set of small measure contradicts.

## Background

- [Besicovitch's Kakeya set of measure zero](besicovitch-kakeya-compact-measure-zero.md): the geometric construction behind the counterexample.

## Sources

- C. Fefferman, *The multiplier problem for the ball*, Ann. of Math. (2) 94 (1971), 330–336, Theorem 1 and §2.
