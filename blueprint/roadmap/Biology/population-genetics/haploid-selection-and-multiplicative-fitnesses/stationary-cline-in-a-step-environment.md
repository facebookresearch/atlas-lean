# Haldane's cline in a step environment

On the line, let selection be $s(x) = +s$ for $x > 0$ and $-s$ for $x < 0$ ($s > 0$), and let migration have variance $\sigma^2 > 0$ per generation. Consider
$p : \mathbb R \to (0, 1)$, twice continuously differentiable on each half-line and continuously differentiable at $0$ (frequency and flux
continuous), with

$$\frac{\sigma^2}{2}\, p'' + s(x)\, p(1 - p) = 0 \quad (x \ne 0), \qquad p(-\infty) = 0, \quad p(+\infty) = 1 .$$

Multiplying by $p'$ gives the first integrals $\frac{\sigma^2}{4} p'^2 = s\bigl(\frac16 - G(p)\bigr)$ for $x > 0$ and $\frac{\sigma^2}{4} p'^2 = s\, G(p)$ for $x < 0$, with
$G(p) = \frac{p^2}{2} - \frac{p^3}{3}$; continuity of $p'$ at $0$ forces $G(p(0)) = \frac1{12}$, so $p(0) = \frac12$, since $G$ is increasing on $(0, 1)$. Since $p'^2 > 0$ wherever $0 < p < 1$, every solution is strictly increasing, so it is unique (the two half-line problems
have unique solutions from $p(0) = \frac12$ with $p'(0) > 0$), antisymmetric, $p(-x) = 1 - p(x)$, and for $x \ge 0$

$$p(x) = -\frac12 + \frac32 \tanh^2\Bigl(\sqrt{\frac{s}{2\sigma^2}}\, x + \operatorname{artanh}\sqrt{\tfrac23}\Bigr),$$

with central slope $p'(0) = \sqrt{s/(3\sigma^2)}$. Since $p''(0^-) = s/(2\sigma^2) = -p''(0^+)$, no solution is twice differentiable at $0$. The cline depends
on $x$ only through $x\sqrt s/\sigma$. This is the continuous-space analogue of [logistic selection](weak-selection-and-the-logistic-approximation.md) balanced by migration.

## Related topics

- [Weak haploid selection follows the logistic curve on the time scale 1/s](weak-selection-and-the-logistic-approximation.md)

## Sources

- J. Felsenstein, *Theoretical Evolutionary Genetics*, University of Washington (2019 edition), <https://felsenst.github.io/pgbook/pgbook.pdf>, Section IV.11, equations (IV-61)–(IV-71) (Haldane's 1948 solution for a symmetric step, $p(x) = -\frac12 + \frac32\tanh^2(\sqrt{s/2m}\,x + \tanh^{-1}\sqrt{2/3})$, and the first-integral derivation of the central slope $(s/3m)^{1/2}$, with $m$ the migration variance).
