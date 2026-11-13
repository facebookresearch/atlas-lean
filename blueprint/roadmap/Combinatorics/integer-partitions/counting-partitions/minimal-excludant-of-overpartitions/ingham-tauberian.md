# Ingham's Tauberian theorem

Let $a : \mathbb{N} \to \mathbb{R}$ be nonnegative and weakly
increasing, let $A : \mathbb{C} \to \mathbb{C}$ be a function, and let $\alpha$, $\beta$, $C$
be real numbers with $C > 0$. Suppose that for every complex $q$ with $|q| < 1$ the series
$\sum_{n \ge 0} a(n) q^n$ is summable with sum $A(q)$, and that for every complex $q$ with
$|q| > 1$ it is not summable. Suppose also that $A(e^{-t}) \sim \alpha t^\beta e^{C/t}$ as
$t \to 0^+$ through positive reals, and that for every $\Delta > 0$,
$A(e^{-z}) = O(|z|^\beta e^{C/|z|})$ as $z \to 0$ within the cone
$\{z \in \mathbb{C} : \mathrm{Re}\, z > 0,\ |\mathrm{Im}\, z| \le \Delta\, \mathrm{Re}\, z\}$.
Then, as $n \to \infty$,

$$a(n) \sim \frac{\alpha}{2\sqrt{\pi}} C^{(2\beta + 1)/4} n^{-(2\beta + 3)/4} e^{2\sqrt{Cn}}.$$

Nothing is assumed about the series on the circle $|q| = 1$, since radius of convergence one
permits either behavior there.

## Sources

- Victor Manuel R. Aricheta, Judy Ann L. Donato, *A Minimal Excludant over Overpartitions*, Journal of Integer Sequences 27 (2024), Article 24.7.1, Proposition 9.
