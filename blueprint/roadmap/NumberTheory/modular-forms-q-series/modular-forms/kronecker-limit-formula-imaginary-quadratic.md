# Kronecker's limit formula for an imaginary quadratic field at $s = 0$

Let $K$ be an imaginary quadratic field of discriminant $D < 0$, with class number $h$ and $w$ roots of
unity, and let $\zeta_K$ be its Dedekind zeta function. Let
$\eta(\tau) = e^{\pi i \tau / 12} \prod_{n \ge 1} (1 - e^{2\pi i n \tau})$ be the Dedekind eta function. For
each ideal class $c$ of $K$ choose a fractional ideal $\mathfrak{a}_c = \mathbb{Z}\omega_1 + \mathbb{Z}\omega_2$
in $c$, ordered so that $\tau_c = \omega_1 / \omega_2$ has positive imaginary part. Then $\zeta_K$ continues to a
meromorphic function on $\mathbb{C}$ that is regular at $s = 0$, with

$$\zeta_K(0) = -\frac{h}{w}, \qquad \zeta_K'(0) = -\frac{1}{w} \sum_{c} \log \frac{8\pi^2 \operatorname{Im}(\tau_c)\, |\eta(\tau_c)|^4}{\sqrt{|D|}},$$

the sum running over the $h$ ideal classes; each term depends only on $c$, because
$\operatorname{Im}(\tau) |\eta(\tau)|^4$ is invariant under $\mathrm{SL}_2(\mathbb{Z})$. Changing the oriented basis of $\mathfrak{a}_c$ acts on $\tau_c$ by $\mathrm{SL}_2(\mathbb{Z})$, and scaling $\mathfrak{a}_c$
does not change $\tau_c$.

Kaneko writes the formula through the discriminant $\Delta(L) = g_2(L)^3 - 27 g_3(L)^2$ of a lattice
$L \subset \mathbb{C}$, where $g_2(L) = 60 \sum_{\omega \in L \setminus 0} \omega^{-4}$ and
$g_3(L) = 140 \sum_{\omega \in L \setminus 0} \omega^{-6}$, and the class invariant
$F(\mathfrak{a}) = \Delta(\mathfrak{a}) \Delta(\mathfrak{a}^{-1})$, which depends only on the class of
$\mathfrak{a}$ since $\Delta(\alpha L) = \alpha^{-12} \Delta(L)$:

$$\zeta_K'(0) = -\frac{1}{12 w} \sum_c \log F(\mathfrak{a}_c).$$

The two forms agree because

$$F(\mathfrak{a}_c)^{1/12} = \frac{2\pi}{\sqrt{|D|}} \cdot 4\pi \operatorname{Im}(\tau_c)\, |\eta(\tau_c)|^4 = \frac{8\pi^2 \operatorname{Im}(\tau_c)\, |\eta(\tau_c)|^4}{\sqrt{|D|}},$$

which follows from [Jacobi's formula](lattice-discriminant-eta-product.md)
$\Delta(\mathbb{Z}\tau + \mathbb{Z}) = (2\pi)^{12} \eta(\tau)^{24}$, the homogeneity of $\Delta$, $\Delta(\overline{L}) = \overline{\Delta(L)}$,
$\mathfrak{a}^{-1} = N(\mathfrak{a})^{-1} \overline{\mathfrak{a}}$, that is, $\mathfrak{a}\overline{\mathfrak{a}} = N(\mathfrak{a}) \mathcal{O}_K$, and
$|\omega_2|^2 \operatorname{Im}(\tau_c) = N(\mathfrak{a}_c) \sqrt{|D|} / 2$. The identity
$\mathfrak{a}\overline{\mathfrak{a}} = N(\mathfrak{a}) \mathcal{O}_K$ holds for the nonzero prime ideals by the
[decomposition of rational primes](../../algebraic-number-theory/quadratic-fields/quadratic-field-prime-decomposition.md) (in the
ramified case $\overline{\mathfrak{p}}^2 = \mathfrak{p}^2$ forces $\overline{\mathfrak{p}} = \mathfrak{p}$). By
[unique factorisation](../../../RingTheory/dedekind-domains/ideal-unique-factorization.md), every nonzero ideal is a product of
irreducible ideals, and these are the nonzero prime ideals, because an ideal of a Dedekind domain
[divides exactly the ideals it contains](../../../RingTheory/dedekind-domains/characterizations-of-dedekind-domains/is-dedekind-domain-iff-contain-is-divide.md);
so the identity holds for every nonzero ideal, by the
[multiplicativity of $N$](../../../RingTheory/dedekind-domains/ideal-absolute-norm.md), and for a fractional ideal $\mathfrak{a}$ by
applying it to $d \mathfrak{a} \subseteq \mathcal{O}_K$ for the least positive integer $d$ with this property, as
$N(\mathfrak{a}) = N(d \mathfrak{a})/d^2$ for that $d$ (the norm of fractional ideals of the
[partial zeta functions](imaginary-quadratic-partial-zeta-epstein.md)). The last relation is
$2 \operatorname{Im} z = N(\mathfrak{b}) \sqrt{|D|}$ for
$\mathfrak{b} = \omega_2^{-1} \mathfrak{a}_c = \mathbb{Z} + \mathbb{Z} \tau_c$.

Proof. The fractional ideal $\omega_2^{-1} \mathfrak{a}_c = \mathbb{Z} + \mathbb{Z}\tau_c$ lies in $c$, so the
[partial zeta functions](imaginary-quadratic-partial-zeta-epstein.md) give
$\zeta_K(s) = \frac{1}{w} \bigl(2/\sqrt{|D|}\bigr)^{s} \sum_c Z(\tau_c, s)$, as $c \mapsto c^{-1}$ permutes the
classes, where $Z(\tau, s) = \sum_{(m, n) \neq (0, 0)} (\operatorname{Im} \tau)^s |m + n\tau|^{-2s}$. By the
[functional equation](epstein-zeta-binary-functional-equation.md), $Z(\tau, s)$ is meromorphic on
$\mathbb{C}$, regular at $s = 0$, with $Z(\tau, 0) = -1$, and
$\Lambda(\tau, s) = \pi^{-s} \Gamma(s) Z(\tau, s)$ satisfies $\Lambda(\tau, s) = \Lambda(\tau, 1 - s)$. Near
$s = 1$, [Kronecker's first limit formula](kronecker-first-limit-formula.md) and
$\pi^{-s}\Gamma(s) = \pi^{-1}(1 - (\gamma + \log \pi)(s - 1) + O((s - 1)^2))$, obtained from the Taylor expansion of the function
$\Gamma$, [analytic](../../../Analysis/special-functions/gamma-function/digamma-and-trigamma-functions/analytic-at-gamma.md) at $1$, with $\Gamma(1) = \int_0^\infty e^{-t} \, dt = 1$ and
[$\Gamma'(1) = -\gamma$](../../special-numbers/harmonic-numbers/gamma-derivative-at-one.md), give
$\Lambda(\tau, s) = \frac{1}{s - 1} + 2(\gamma - \log 2 - \log(\sqrt{y} |\eta(\tau)|^2)) - \gamma - \log \pi + O(s - 1)$
with $y = \operatorname{Im} \tau$; the functional equation turns this into the expansion of $\Lambda(\tau, s)$ at
$s = 0$, and comparing it with $\pi^{-s} \Gamma(s) = \frac{1}{s} - \gamma - \log \pi + O(s)$, which follows from
the [recurrence](../../../Analysis/special-functions/gamma-function/gamma-function-recurrence.md) $\Gamma(s) = \Gamma(s + 1)/s$ for
$s \neq 0$ and the Taylor expansion $\Gamma(1 + s) = 1 - \gamma s + O(s^2)$, gives

$$\frac{\partial Z}{\partial s}(\tau, 0) = -\log\bigl(4\pi^2 \operatorname{Im}(\tau)\, |\eta(\tau)|^4\bigr).$$

Differentiating $\zeta_K(s) = \frac{1}{w} (2/\sqrt{|D|})^s \sum_c Z(\tau_c, s)$ at $s = 0$ gives both formulas.
(Kaneko derives the formula from Kronecker's first limit formula, following Weil; the computation is
written out here.)

## Depends on

- [The class group of a number field is finite](../../algebraic-number-theory/number-fields-embeddings/class-group-finite.md), for the $h$ ideal classes
- [A finitely generated torsion-free module over a principal ideal domain is free](../../../LinearAlgebra/eigenvalues-and-canonical-forms/finite-torsion-free-module-pid-free.md), for the $\mathbb{Z}$-bases $(\omega_1, \omega_2)$ of the fractional ideals $\mathfrak{a}_c$

## Proof depends on

- [Partial zeta functions of an imaginary quadratic field as Epstein zeta functions](imaginary-quadratic-partial-zeta-epstein.md)
- [Functional equation of the Epstein zeta function of a binary form](epstein-zeta-binary-functional-equation.md)
- [Kronecker's first limit formula](kronecker-first-limit-formula.md), for the expansion of $Z(\tau, s)$ at $s = 1$ and for the invariance of $\operatorname{Im}(\tau) |\eta(\tau)|^4$ under $\mathrm{SL}_2(\mathbb{Z})$, which makes each term independent of the choice of $\mathfrak{a}_c$ and of its basis
- [Jacobi's product formula for the discriminant of a lattice](lattice-discriminant-eta-product.md), for Kaneko's form
- [Decomposition of rational primes in a quadratic field](../../algebraic-number-theory/quadratic-fields/quadratic-field-prime-decomposition.md), for $\mathfrak{p}\overline{\mathfrak{p}} = N(\mathfrak{p}) \mathcal{O}_K$, in Kaneko's form
- [Unique factorisation of ideals in a Dedekind domain](../../../RingTheory/dedekind-domains/ideal-unique-factorization.md), for passing from prime ideals to all ideals, in Kaneko's form
- [Dedekind domains as the Noetherian domains where to contain is to divide](../../../RingTheory/dedekind-domains/characterizations-of-dedekind-domains/is-dedekind-domain-iff-contain-is-divide.md), for the irreducible ideals being the nonzero prime ideals
- [Absolute norm of an ideal](../../../RingTheory/dedekind-domains/ideal-absolute-norm.md), for the multiplicativity of $N$, in Kaneko's form
- [Recurrence of the gamma function](../../../Analysis/special-functions/gamma-function/gamma-function-recurrence.md), for $\Gamma(s) = \Gamma(s + 1)/s$
- [The derivative of the gamma function at 1 is minus Euler's constant](../../special-numbers/harmonic-numbers/gamma-derivative-at-one.md), for $\Gamma'(1) = -\gamma$
- [Analyticity of the Gamma function](../../../Analysis/special-functions/gamma-function/digamma-and-trigamma-functions/analytic-at-gamma.md), for the Taylor expansion of $\Gamma$ at $1$ to second order

## Sources

- M. Kaneko, *A generalization of the Chowla–Selberg formula and the zeta functions of quadratic
  orders*, Proc. Japan Acad. 66, Ser. A (1990), 201–203,
  <https://www2.math.kyushu-u.ac.jp/~mkaneko/papers/07Chowla-Selberg.pdf>: Section 1, the definitions
  of $g_2$, $g_3$, $\Delta$ and $F(\mathfrak{a})$ and property (1); Section 2, the formula for
  $\zeta_{\mathcal{O}_f}'(0)$ obtained from Kronecker's first limit formula, in the case $f = 1$ of the
  maximal order, with a reference to A. Weil, *Elliptic functions according to Eisenstein and
  Kronecker*, Springer (1976), Chapter IX.
- C. L. Siegel, *Lectures on advanced analytic number theory*, notes by S. Raghavan, Tata Institute of
  Fundamental Research Lectures on Mathematics 23, Bombay (1961, reissued 1965),
  <https://www.math.tifr.res.in/~publ/ln/tifr23.pdf> (copy:
  <https://www-users.cse.umn.edu/~garrett/m/mfms/notes_2013-14/Siegel_AdvAnNoTh.pdf>), Chapter 1, §2,
  formula (17) (p. 15).
- F. W. J. Olver et al. (eds.), *NIST Digital Library of Mathematical Functions*, Version 1.2.8 of 2026-09-15,
  <https://dlmf.nist.gov/5.4> and <https://dlmf.nist.gov/5.5>: equations 5.4.1 ($\Gamma(1) = 1$), 5.4.12
  ($\psi(1) = -\gamma$, so $\Gamma'(1) = \Gamma(1) \psi(1) = -\gamma$) and 5.5.1 ($\Gamma(z + 1) = z \Gamma(z)$).
