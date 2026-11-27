# Functional equation of the $L$-function of a newform

Let $f$ be a newform of weight $2$ and level $N$ with [Fricke eigenvalue](fricke-eigenvalue-of-a-newform.md)
$\varepsilon \in \{1, -1\}$, and let $\Lambda(f, s) = N^{s/2} \int_0^\infty f(it) t^{s-1} \, dt$ as in the
[Mellin transform page](mellin-transform-of-a-weight-two-cusp-form.md). Then the integral converges for every
$s \in \mathbb{C}$ and defines an entire function, which agrees with $(2\pi)^{-s}\Gamma(s)N^{s/2}L(f, s)$ where the
Dirichlet series converges absolutely, and

$$\Lambda(f, s) = -\varepsilon \, \Lambda(f, 2 - s) \qquad (s \in \mathbb{C}).$$

Proof outline (worked out here, as Darmon's Exercise 9 asks): $f \mid_2 W_N = \varepsilon f$ gives
$f(i/(Nt)) = -\varepsilon N t^2 f(it)$ for $t > 0$; splitting $\int_0^\infty$ at $t = N^{-1/2}$ and substituting
$t \mapsto 1/(Nt)$ on $(0, N^{-1/2})$ writes $\Lambda(f, s)$ as
$\int_{N^{-1/2}}^\infty f(it) \bigl(N^{s/2} t^{s-1} - \varepsilon N^{1-s/2} t^{1-s}\bigr) \, dt$, which converges for every
$s$ because $f(it)$ decays exponentially as $t \to \infty$, and which is visibly multiplied by $-\varepsilon$ under
$s \mapsto 2 - s$.

## Depends on

- [Fricke eigenvalue of a newform](fricke-eigenvalue-of-a-newform.md), for $\varepsilon$
- [Mellin transform of a weight-two cusp form](mellin-transform-of-a-weight-two-cusp-form.md), for $\Lambda(f, s)$

## Proof depends on

- [Fricke eigenvalue of a newform](fricke-eigenvalue-of-a-newform.md), for $f \mid_2 W_N = \varepsilon f$
- [Mellin transform of a weight-two cusp form](mellin-transform-of-a-weight-two-cusp-form.md), for the agreement with $(2\pi)^{-s}\Gamma(s)N^{s/2}L(f, s)$
- [Cusp form](../../modular-forms-q-series/modular-forms/cusp-form.md), for the vanishing of $f$ at the cusp $\infty$, which gives the exponential decay of $f(it)$

## Sources

- H. Darmon, *Rational points on modular elliptic curves*, CBMS Regional Conference Series in Mathematics 101,
  American Mathematical Society, 2004; author's version,
  <https://www.math.mcgill.ca/darmon/pub/Articles/Research/36.NSF-CBMS/chapter.pdf>, cited by the page numbers
  printed in that version: (2.14), p. 18 ("Hecke showed (cf. Exercise 9) that $L(f, s)$ satisfies the functional equation
  $\Lambda(f, s) = -\Lambda(w_N(f), 2 - s) = -\varepsilon\Lambda(f, 2 - s)$."), and Exercise 9 of Chapter 2, p. 24
  ("Prove the functional equation (2.14) in the text.").
- B. H. Gross, *Kolyvagin's work on modular elliptic curves*, in *L-functions and arithmetic* (Durham, 1989),
  London Math. Soc. Lecture Note Ser. 153, Cambridge Univ. Press, 1991, 235–256: (5.2) and the sentence after it, p. 243.
