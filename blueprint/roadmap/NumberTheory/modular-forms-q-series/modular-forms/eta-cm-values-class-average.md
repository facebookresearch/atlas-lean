# Class average of logarithms of CM values of the eta function

Let $K$ be an imaginary quadratic field of discriminant $D < 0$, with class number $h$ and $w$ roots of
unity, let $\chi = \left(\frac{D}{\cdot}\right)$ be its quadratic Dirichlet character, a character modulo $|D|$, and
$L(s, \chi)$ the Dirichlet $L$-function of $\chi$. Let
$\eta(\tau) = e^{\pi i \tau / 12} \prod_{n \ge 1} (1 - e^{2\pi i n \tau})$ be the Dedekind eta function on the
upper half-plane. For each ideal class $c$ of $K$ choose a fractional ideal
$\mathfrak{a}_c = \mathbb{Z}\omega_1 + \mathbb{Z}\omega_2$ in $c$, ordered so that $\tau_c = \omega_1 / \omega_2$
has positive imaginary part. Then $L(1, \chi) = 2\pi h / (w \sqrt{|D|}) \neq 0$ and

$$\frac{1}{h} \sum_{c} \log\bigl(4\pi \operatorname{Im}(\tau_c) \, |\eta(\tau_c)|^4\bigr) = \gamma + \log \frac{2\pi}{\sqrt{|D|}} - \frac{L'(1, \chi)}{L(1, \chi)},$$

where $\gamma$ is Euler's constant and the sum runs over the $h$ ideal classes. Each term depends only on
the class $c$, because $\operatorname{Im}(\tau) |\eta(\tau)|^4$ is invariant under $\mathrm{SL}_2(\mathbb{Z})$. Changing the oriented basis of $\mathfrak{a}_c$ acts on $\tau_c$ by $\mathrm{SL}_2(\mathbb{Z})$, and scaling $\mathfrak{a}_c$
does not change $\tau_c$.

Proof. The fractional ideal $\mathfrak{b}_c = \omega_2^{-1}\mathfrak{a}_c = \mathbb{Z} + \mathbb{Z}\tau_c$ lies in $c$
and has norm $N(\mathfrak{b}_c) = 2 \operatorname{Im}(\tau_c) / \sqrt{|D|}$, and the
[partial zeta function](imaginary-quadratic-partial-zeta-epstein.md) of the inverse class is
$\zeta_K(s, c^{-1}) = \frac{1}{w} \bigl(2/\sqrt{|D|}\bigr)^{s} Z(\tau_c, s)$, where
$Z(\tau, s) = \sum_{(m, n) \neq (0, 0)} (\operatorname{Im} \tau)^s |m + n\tau|^{-2s}$. By
[Kronecker's first limit formula](kronecker-first-limit-formula.md),

$$\zeta_K(s, c^{-1}) = \frac{2\pi}{w \sqrt{|D|}} \left( \frac{1}{s - 1} + 2\gamma - \log |D| - \log\bigl(N(\mathfrak{b}_c) |\eta(\tau_c)|^4\bigr) + O(s - 1) \right).$$

Summing over the classes gives the expansion of $\zeta_K(s)$ at $s = 1$, and
[$\zeta_K(s) = \zeta(s) L(s, \chi)$](../../zeta-l-functions/dirichlet-l-functions/dedekind-zeta-quadratic-field-factorization.md)
for $\operatorname{Re} s > 1$, with $\zeta(s) = \frac{1}{s - 1} + \gamma + O(s - 1)$ (the
[Laurent expansion of $\zeta$ at $1$](../../zeta-l-functions/riemann-zeta/stieltjes-constants/ramanujan-part1-ch7-entry13-bernoullirec.md), whose constant term is
[Euler's constant](../../zeta-l-functions/riemann-zeta/stieltjes-constants/ramanujan-part1-ch7-entry13-bernoullipol.md)), shows that
$L(s, \chi)$ is holomorphic at $s = 1$: near $1$, the quotient of $(s - 1) \zeta_K(s)$, holomorphic with the residue of
$\zeta_K$ at $1$ as its value there, by $(s - 1) \zeta(s)$, holomorphic with value $1$, is holomorphic and agrees with the
Dirichlet series of $L(s, \chi)$ for $\operatorname{Re} s > 1$, so by the [identity theorem](../../../Geometry/complex-and-symplectic-geometry/identity-and-open-mapping-theorems-for-holomorph/holomorphic-identity-on-connected-comple.md), on the
connected union of a disc around $1$ and that half-plane, it is $L(s, \chi)$. This gives $\zeta_K(s) = \frac{L(1, \chi)}{s - 1} + \gamma L(1, \chi) + L'(1, \chi) + O(s - 1)$. Comparing the residues gives
Dirichlet's class number formula $L(1, \chi) = 2\pi h / (w \sqrt{|D|})$, and comparing the constant terms gives

$$\frac{L'(1, \chi)}{L(1, \chi)} = \gamma - \log |D| - \frac{1}{h} \sum_c \log\bigl(N(\mathfrak{b}_c) |\eta(\tau_c)|^4\bigr),$$

which is the identity above, rewritten with $N(\mathfrak{b}_c) = 2 \operatorname{Im}(\tau_c) / \sqrt{|D|}$.

## Depends on

- [Quadratic Dirichlet character of a fundamental discriminant](../../congruences/power-residues-reciprocity/kronecker-symbol-and-quadratic-characters/quadratic-dirichlet-character.md)
- [The class group of a number field is finite](../../algebraic-number-theory/number-fields-embeddings/class-group-finite.md), for the $h$ ideal classes
- [A finitely generated torsion-free module over a principal ideal domain is free](../../../LinearAlgebra/eigenvalues-and-canonical-forms/finite-torsion-free-module-pid-free.md), for the $\mathbb{Z}$-bases $(\omega_1, \omega_2)$ of the fractional ideals $\mathfrak{a}_c$

## Proof depends on

- [Kronecker's first limit formula](kronecker-first-limit-formula.md), for the expansion of $Z(\tau_c, s)$ at $s = 1$ and for the invariance of $\operatorname{Im}(\tau) |\eta(\tau)|^4$ under $\mathrm{SL}_2(\mathbb{Z})$, which makes each term depend only on $c$
- [Partial zeta functions of an imaginary quadratic field as Epstein zeta functions](imaginary-quadratic-partial-zeta-epstein.md)
- [Dedekind zeta function of a quadratic field as $\zeta(s) L(s, \chi_D)$](../../zeta-l-functions/dirichlet-l-functions/dedekind-zeta-quadratic-field-factorization.md)
- [Laurent expansion of $\zeta$ at $s = 1$](../../zeta-l-functions/riemann-zeta/stieltjes-constants/ramanujan-part1-ch7-entry13-bernoullirec.md), for its constant term $c_0$
- [Stieltjes constants exist, and the zeroth is Euler's constant](../../zeta-l-functions/riemann-zeta/stieltjes-constants/ramanujan-part1-ch7-entry13-bernoullipol.md), for $c_0 = \gamma$
- [Identity theorem for holomorphic maps](../../../Geometry/complex-and-symplectic-geometry/identity-and-open-mapping-theorems-for-holomorph/holomorphic-identity-on-connected-comple.md), for the uniqueness of $L(s, \chi)$ near $s = 1$, on the domain it shares with $\zeta_K(s) / \zeta(s)$

## Sources

- C. L. Siegel, *Lectures on advanced analytic number theory*, notes by S. Raghavan, Tata Institute of
  Fundamental Research Lectures on Mathematics 23, Bombay (1961, reissued 1965),
  <https://www.math.tifr.res.in/~publ/ln/tifr23.pdf> (copy:
  <https://www-users.cse.umn.edu/~garrett/m/mfms/notes_2013-14/Siegel_AdvAnNoTh.pdf>), Chapter 2, §1,
  pp. 64–68: the expansion of $\zeta(s, A)$ (p. 65), the class invariant
  $F(A) = \sqrt{N([1, z])}\, |\eta(z)|^2$ of formula $(*)$, formula (70) and formulas (71) and $(71)'$, which give
  $L(1) = 2\pi h / (w \sqrt{|d|})$ and $L'(1)/L(1) = C - \log |d| - \frac{2}{h} \sum_A \log F(A)$; Chapter 1, §2,
  formula (17) (p. 15), for the invariance of $\operatorname{Im}(z)^{1/4} |\eta(z)|$.
- D. Zagier, *Elliptic modular forms and their applications*, in *The 1-2-3 of Modular Forms*,
  Universitext, Springer (2008), 1–103,
  <https://people.mpim-bonn.mpg.de/zagier/files/doi/10.1007/978-3-540-74119-0_1/fulltext.pdf>, §6.3,
  pp. 84–85: the comparison of the Laurent expansions at $s = 1$ of the two decompositions of $\zeta_K(s)$.
- Provenance: Alpöge's Lean library (<https://alpo.ge/remark.pdf>; source mirror
  <https://github.com/leanprover-community/riemann-hypothesis/tree/79c751e0b0a5ea3bbfc20198c852fa85f28661e6>) uses this identity, for $|D| > 4$, as `GlobalTheory.chowla_selberg_eta`.
