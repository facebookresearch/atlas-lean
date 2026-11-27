# Square roots of cubics with positive leading coefficient are uniformly distributed modulo one

**Square roots of cubics with positive leading coefficient are uniformly distributed modulo
one.** Let $q(t) = a t^3 + b t^2 + c t + d$ with real coefficients $a, b, c, d$ and $a > 0$,
write $\{x\} = x - \lfloor x \rfloor$ for the fractional part of a real $x$, and let
$e(x) = e^{2\pi i x}$. Then there is an integer $T \ge 1$ with three properties. First,
$q(t) > 0$ for every real $t \ge T$. Second, the sequence $\sqrt{q(T)}, \sqrt{q(T + 1)}, \dots$
is uniformly distributed modulo one: for all real $\alpha, \beta$ with $0 \le \alpha < \beta \le 1$,

$$\lim_{N \to \infty} \frac{1}{N}
\#\bigl\{0 \le n < N : \alpha \le \{\sqrt{q(T + n)}\} < \beta\bigr\} = \beta - \alpha.$$

Third, there is a real constant $C$ such that for every integer $N \ge T$ and every nonzero
integer $\gamma$,

$$\Bigl|\sum_{n=T}^{N} e\bigl(\gamma \sqrt{q(n)}\bigr)\Bigr| \le
C \bigl(|\gamma|^{1/2} N^{3/4} + |\gamma| N^{1/2} + |\gamma|^{-1/2} N^{1/4} + 1\bigr).$$

## Sources

- Anji Dong, Katerina Saettone, Kendra Song and Alexandru Zaharescu, *An Equidistribution Result for Differences Associated with Square Pyramidal Numbers*, Journal of Integer Sequences 29 (2026), Article 26.5.5, Proposition 6 (`jis-2026-26.5.5-prop-6`).
