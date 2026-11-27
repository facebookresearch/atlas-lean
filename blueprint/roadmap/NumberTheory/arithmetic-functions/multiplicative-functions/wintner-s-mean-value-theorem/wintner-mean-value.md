# Wintner's mean-value theorem

Let $f$ be a complex-valued arithmetic function, let $\mu$
be the Möbius function, and let $\mu * f$ be their Dirichlet convolution,
$(\mu * f)(n) = \sum_{d \mid n} \mu(d) f(n/d)$. If the series $\sum_{n \ge 1} |(\mu * f)(n)|/n$
converges, then

$$\frac{1}{x} \sum_{n=1}^{x} f(n) \to \sum_{n \ge 1} \frac{(\mu * f)(n)}{n}$$

as the integer $x$ tends to infinity.

No multiplicativity, Euler product, quantitative error term, or alternating mean is assumed or
concluded.

## Sources

- László Tóth, *On the Asymptotic Density of k-tuples of Positive Integers with Pairwise Non-Coprime Components*, Journal of Integer Sequences 27 (2024), Article 24.8.5, mean-value definition and Theorem `Th_Wintner_gen`, lines 292–310 (the `k = 1` case identified at lines 297–298 as Wintner's classical theorem; the source theorem itself is Ushiroya's multivariable generalization), <https://cs.uwaterloo.ca/journals/JIS/VOL27/Toth/toth27.tex>.
