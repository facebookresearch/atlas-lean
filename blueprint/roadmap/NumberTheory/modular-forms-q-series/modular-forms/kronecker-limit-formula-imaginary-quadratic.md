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
$\mathfrak{a}^{-1} = N(\mathfrak{a})^{-1} \overline{\mathfrak{a}}$ (that is, $\mathfrak{a}\overline{\mathfrak{a}} = N(\mathfrak{a}) \mathcal{O}_K$, which
holds for prime ideals by the [decomposition of rational primes](../../algebraic-number-theory/quadratic-fields/quadratic-field-prime-decomposition.md)
and so for all fractional ideals) and
$|\omega_2|^2 \operatorname{Im}(\tau_c) = N(\mathfrak{a}_c) \sqrt{|D|} / 2$,
the last being the relation $2 \operatorname{Im} z = N(\mathfrak{b}) \sqrt{|D|}$ for
$\mathfrak{b} = \omega_2^{-1} \mathfrak{a}_c = \mathbb{Z} + \mathbb{Z} \tau_c$.

Proof. The fractional ideal $\omega_2^{-1} \mathfrak{a}_c = \mathbb{Z} + \mathbb{Z}\tau_c$ lies in $c$, so the
[partial zeta functions](imaginary-quadratic-partial-zeta-epstein.md) give
$\zeta_K(s) = \frac{1}{w} \bigl(2/\sqrt{|D|}\bigr)^{s} \sum_c Z(\tau_c, s)$, as $c \mapsto c^{-1}$ permutes the
classes, where $Z(\tau, s) = \sum_{(m, n) \neq (0, 0)} (\operatorname{Im} \tau)^s |m + n\tau|^{-2s}$. By the
[functional equation](epstein-zeta-binary-functional-equation.md), $Z(\tau, s)$ is meromorphic on
$\mathbb{C}$, regular at $s = 0$, with $Z(\tau, 0) = -1$, and
$\Lambda(\tau, s) = \pi^{-s} \Gamma(s) Z(\tau, s)$ satisfies $\Lambda(\tau, s) = \Lambda(\tau, 1 - s)$. Near
$s = 1$, [Kronecker's first limit formula](kronecker-first-limit-formula.md) and
$\pi^{-s}\Gamma(s) = \pi^{-1}(1 - (\gamma + \log \pi)(s - 1) + \cdots)$, which uses $\Gamma(1) = 1$ and $\Gamma'(1) = -\gamma$, give
$\Lambda(\tau, s) = \frac{1}{s - 1} + 2(\gamma - \log 2 - \log(\sqrt{y} |\eta(\tau)|^2)) - \gamma - \log \pi + O(s - 1)$
with $y = \operatorname{Im} \tau$; the functional equation turns this into the expansion of $\Lambda(\tau, s)$ at
$s = 0$, and comparing it with $\pi^{-s} \Gamma(s) = \frac{1}{s} - \gamma - \log \pi + O(s)$, which follows from
$\Gamma(s) = \Gamma(s + 1)/s$ with $\Gamma(1) = 1$ and $\Gamma'(1) = -\gamma$, gives

$$\frac{\partial Z}{\partial s}(\tau, 0) = -\log\bigl(4\pi^2 \operatorname{Im}(\tau)\, |\eta(\tau)|^4\bigr).$$

Differentiating $\zeta_K(s) = \frac{1}{w} (2/\sqrt{|D|})^s \sum_c Z(\tau_c, s)$ at $s = 0$ gives both formulas.
(Kaneko derives the formula from Kronecker's first limit formula, following Weil; the computation is
written out here.)

## Depends on

This node has no prerequisites.

## Proof depends on

- [Partial zeta functions of an imaginary quadratic field as Epstein zeta functions](imaginary-quadratic-partial-zeta-epstein.md)
- [Functional equation of the Epstein zeta function of a binary form](epstein-zeta-binary-functional-equation.md)
- [Kronecker's first limit formula](kronecker-first-limit-formula.md), for the expansion of $Z(\tau, s)$ at $s = 1$ and for the invariance of $\operatorname{Im}(\tau) |\eta(\tau)|^4$ under $\mathrm{SL}_2(\mathbb{Z})$, which makes each term independent of the choice of $\mathfrak{a}_c$ and of its basis
- [Jacobi's product formula for the discriminant of a lattice](lattice-discriminant-eta-product.md), for Kaneko's form
- [Decomposition of rational primes in a quadratic field](../../algebraic-number-theory/quadratic-fields/quadratic-field-prime-decomposition.md), for $\mathfrak{p}\overline{\mathfrak{p}} = N(\mathfrak{p}) \mathcal{O}_K$, in Kaneko's form

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
