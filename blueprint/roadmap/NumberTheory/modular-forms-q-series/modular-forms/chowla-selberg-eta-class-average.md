# Chowla–Selberg formula: the class average of logarithms of CM values of the eta function

Let $K$ be an imaginary quadratic field of discriminant $D < 0$, with class number $h$ and $w$ roots of
unity, let $\chi = \left(\frac{D}{\cdot}\right)$ be its quadratic Dirichlet character, of conductor
$|D|$, and $L(s, \chi)$ the Dirichlet $L$-function of $\chi$. Let
$\eta(\tau) = e^{\pi i \tau / 12} \prod_{n \ge 1} (1 - e^{2\pi i n \tau})$ be the Dedekind eta function
on the upper half-plane. For each ideal class $c$ of $K$ choose a fractional ideal
$\mathfrak{a}_c = \mathbb{Z}\omega_1 + \mathbb{Z}\omega_2$ in $c$, ordered so that
$\tau_c = \omega_1 / \omega_2$ has positive imaginary part. Then

$$\frac{1}{h} \sum_{c} \log\bigl(4\pi \operatorname{Im}(\tau_c) \, |\eta(\tau_c)|^4\bigr) = \gamma + \log \frac{2\pi}{\sqrt{|D|}} - \frac{L'(1, \chi)}{L(1, \chi)},$$

where $\gamma$ is Euler's constant and the sum runs over the $h$ ideal classes. Each term depends only on
the class $c$, because $\operatorname{Im}(\tau) |\eta(\tau)|^4$ is invariant under
$\mathrm{SL}_2(\mathbb{Z})$.

Kaneko writes the identity through the discriminant $\Delta(L) = g_2(L)^3 - 27 g_3(L)^2$ of a lattice $L$
and the class invariant $F(\mathfrak{a}) = \Delta(\mathfrak{a}) \Delta(\mathfrak{a}^{-1})$: Kronecker's
first limit formula gives

$$\zeta_K'(0) = -\frac{1}{12 w} \sum_{c} \log F(\mathfrak{a}_c),$$

and, with $\zeta_K(s) = \zeta(s) L(s, \chi)$ and a formula expressing $L'(0, \chi)$ through the gamma
function, the Chowla–Selberg formula

$$\prod_{c} F(\mathfrak{a}_c) = \left(\frac{2\pi}{|D|}\right)^{12h} \prod_{a=1}^{|D| - 1} \Gamma\!\left(\frac{a}{|D|}\right)^{6 w \chi(a)}.$$

The identity in the first display is the logarithmic form of these, rewritten with $\eta$ at $s = 1$. The
rewriting, written out here and not in the sources, uses
$\Delta(\mathbb{Z}\tau + \mathbb{Z}) = (2\pi)^{12} \eta(\tau)^{24}$, the homogeneity
$\Delta(\alpha L) = \alpha^{-12} \Delta(L)$, $\mathfrak{a}^{-1} = N(\mathfrak{a})^{-1} \overline{\mathfrak{a}}$
and the covolume $N(\mathfrak{a}) \sqrt{|D|} / 2$ of $\mathfrak{a}$, which give
$F(\mathfrak{a}_c)^{1/12} = \frac{2\pi}{\sqrt{|D|}} \cdot 4\pi \operatorname{Im}(\tau_c) |\eta(\tau_c)|^4$;
then $\zeta(0) = -1/2$, $\zeta'(0) = -\frac12 \log 2\pi$ and $L(0, \chi) = 2h/w$ turn Kronecker's
formula into $\frac{1}{h} \sum_c \log(4\pi \operatorname{Im}(\tau_c) |\eta(\tau_c)|^4) = \frac12 \log|D| + L'(0, \chi)/L(0, \chi)$,
and the functional equation of $L(s, \chi)$, an odd real primitive character, moves the right-hand side
to $s = 1$.

This node is still to be broken down. A good expansion has pages for Kronecker's first limit formula in
the form above, for the formula expressing $L'(0, \chi)$ through the gamma function, and for the
Chowla–Selberg product formula, with the rewriting above as the last step; the functional equation of
$L(s, \chi)$ that it uses is a case of the
[functional equation of Hecke L-functions](../../zeta-l-functions/dirichlet-l-functions/hecke-l-function-functional-equation.md).

## Proof depends on

- [Functional equation of Hecke L-functions](../../zeta-l-functions/dirichlet-l-functions/hecke-l-function-functional-equation.md)

## Sources

- M. Kaneko, *A generalization of the Chowla–Selberg formula and the zeta functions of quadratic
  orders*, Proc. Japan Acad. 66, Ser. A (1990), 201–203,
  <https://www2.math.kyushu-u.ac.jp/~mkaneko/papers/07Chowla-Selberg.pdf>: Section 1, the definitions
  of $g_2$, $g_3$, $\Delta$ and $F(\mathfrak{a})$, property (1) and formula (2) (Chowla–Selberg);
  Section 2, the formula for $\zeta_{\mathcal{O}_f}'(0)$ from Kronecker's first limit formula (case
  $f = 1$) and the identity $\zeta_K(s) = \zeta(s) L(s, \chi)$.
- S. Chowla and A. Selberg, *On Epstein's zeta-function*, J. Reine Angew. Math. 227 (1967), 86–110, the
  original source, as cited by Kaneko.
- Provenance: Alpöge's Lean library (<https://alpo.ge/remark.pdf>; source mirror
  <https://github.com/leanprover-community/riemann-hypothesis/tree/79c751e0b0a5ea3bbfc20198c852fa85f28661e6>) uses this identity, for $|D| > 4$, as `GlobalTheory.chowla_selberg_eta`.
