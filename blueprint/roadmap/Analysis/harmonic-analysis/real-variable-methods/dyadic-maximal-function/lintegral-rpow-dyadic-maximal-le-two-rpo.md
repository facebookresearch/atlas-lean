# $L^p$ bound for the dyadic maximal function with constant $2^p p/(p-1)$

For $1 < p$ and every $f \colon \mathbb{R} \to E$ with $\|f\|$ a.e. measurable,

$$\int_{\mathbb{R}} (M_d f)^p \le \frac{2^p p}{p-1} \int_{\mathbb{R}} \|f\|^p.$$

This is the Marcinkiewicz argument. For $t > 0$ write $\|f\| \le \|f\| \mathbf{1}_{\{\|f\| > t/2\}} + t/2$; every dyadic average of the second term is at most $t/2$, so $\{M_d f > t\} \subseteq \{M_d(\|f\| \mathbf{1}_{\{\|f\| > t/2\}}) > t/2\}$, and the [weak type (1,1) bound](dyadic-maximal-function-mul-volume-le-li.md) gives $|\{M_d f > t\}| \le \frac{2}{t} \int_{\{\|f\| > t/2\}} \|f\|$. Integrating against $p t^{p-1} dt$ (layer-cake formula and Tonelli's theorem) yields the bound. Its constant is larger than the sharp $(p/(p-1))^p$ of the $L^p$ bound, but its proof needs no a priori finiteness, which is why the sharp proof uses it. The constant is that of the special case of the Marcinkiewicz interpolation theorem (weak type (1,1) with constant $1$, strong type $(\infty, \infty)$ with constant $1$) proved by this splitting; T. Hytönen, *Dyadic analysis and weights*, lecture notes, University of Helsinki, version of 2 May 2014, Theorem 3.10, obtains the better constant $p'$.

## Informally uses

- [Weak type (1,1) of the dyadic maximal function](dyadic-maximal-function-mul-volume-le-li.md): applied to the part of $\|f\|$ above $t/2$.

## Sources

- T. Hytönen, *Dyadic analysis and weights*, lecture notes, University of Helsinki, version of 2 May 2014 (a secondary source: lecture notes presenting the dyadic theory of C. Fefferman and E. M. Stein, *Some maximal inequalities*, Amer. J. Math. 93 (1971), 107–115, and of E. M. Stein, *Harmonic Analysis*, Princeton University Press, 1993).
