# Doob-type inequality for the dyadic maximal function

For $1 < p$ and every $f \colon \mathbb{R} \to E$ with $\|f\|$ a.e. measurable,

$$\int_{\mathbb{R}} (M_d f)^p \le \frac{p}{p-1} \int_{\mathbb{R}} \|f\|\,(M_d f)^{p-1}.$$

Proof: by the layer-cake formula $\int (M_d f)^p = \int_0^\infty p t^{p-1} |\{M_d f > t\}| \, dt$; the [localized weak type (1,1) bound](mul-volume-lt-dyadic-maximal-function-le.md) gives $t |\{M_d f > t\}| \le \int_{\{M_d f > t\}} \|f\|$; and Tonelli's theorem with $\int_0^{M_d f(x)} p t^{p-2} dt = \frac{p}{p-1} M_d f(x)^{p-1}$ concludes. This is the argument behind Doob's $L^p$ inequality, and the first step towards the $L^p$ bound of T. Hytönen, *Dyadic analysis and weights*, lecture notes, University of Helsinki, version of 2 May 2014, Theorem 3.8. The layer-cake formula used is a version for $[0, \infty]$-valued functions, proved from the identity $a^q = \int_0^\infty \mathbf{1}_{t < a} \, q t^{q-1} \, dt$ for $a \in [0, \infty]$.

## Informally uses

- [Weak type (1,1), localized form](mul-volume-lt-dyadic-maximal-function-le.md): the estimate integrated in $t$.

## Sources

- T. Hytönen, *Dyadic analysis and weights*, lecture notes, University of Helsinki, version of 2 May 2014 (a secondary source: lecture notes presenting the dyadic theory of C. Fefferman and E. M. Stein, *Some maximal inequalities*, Amer. J. Math. 93 (1971), 107–115, and of E. M. Stein, *Harmonic Analysis*, Princeton University Press, 1993).
