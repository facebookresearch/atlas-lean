# Chowla–Selberg formula

Let $K$ be an imaginary quadratic field of discriminant $D < 0$, with class number $h$ and $w$ roots of
unity, and let $\chi = \left(\frac{D}{\cdot}\right)$ be its quadratic Dirichlet character modulo $|D|$. For a
lattice $L \subset \mathbb{C}$ let $\Delta(L) = g_2(L)^3 - 27 g_3(L)^2$, with
$g_2(L) = 60 \sum_{\omega \in L \setminus 0} \omega^{-4}$ and $g_3(L) = 140 \sum_{\omega \in L \setminus 0} \omega^{-6}$,
and for a fractional ideal $\mathfrak{a}$ of $K$ let $F(\mathfrak{a}) = \Delta(\mathfrak{a}) \Delta(\mathfrak{a}^{-1})$,
which depends only on the ideal class of $\mathfrak{a}$. Then, with $\mathfrak{a}_c$ a fractional ideal in the
class $c$,

$$\prod_{c} F(\mathfrak{a}_c) = \left(\frac{2\pi}{|D|}\right)^{12h} \prod_{a=1}^{|D| - 1} \Gamma\!\left(\frac{a}{|D|}\right)^{6 w \chi(a)},$$

the product on the left running over the $h$ ideal classes. Equivalently, with
$\mathfrak{a}_c = \mathbb{Z}\omega_1 + \mathbb{Z}\omega_2$ ordered so that $\tau_c = \omega_1/\omega_2$ has positive
imaginary part and $\eta$ the Dedekind eta function,

$$\prod_{c} \Bigl(4\pi \sqrt{|D|}\, \operatorname{Im}(\tau_c)\, |\eta(\tau_c)|^4\Bigr)^{2/w} = \prod_{a=1}^{|D| - 1} \Gamma\!\left(\frac{a}{|D|}\right)^{\chi(a)},$$

since $F(\mathfrak{a}_c)^{1/12} = 8\pi^2 \operatorname{Im}(\tau_c) |\eta(\tau_c)|^4 / \sqrt{|D|}$ (see
[Kronecker's limit formula at $s = 0$](kronecker-limit-formula-imaginary-quadratic.md)). Each factor of the second form
depends only on $c$, because $\operatorname{Im}(\tau) |\eta(\tau)|^4$ is invariant under $\mathrm{SL}_2(\mathbb{Z})$: changing the oriented basis of $\mathfrak{a}_c$ acts on $\tau_c$ by $\mathrm{SL}_2(\mathbb{Z})$, and scaling $\mathfrak{a}_c$
does not change $\tau_c$.

Proof. By [Kronecker's limit formula at $s = 0$](kronecker-limit-formula-imaginary-quadratic.md),
$\zeta_K(0) = -h/w$ and $\zeta_K'(0) = -\frac{1}{12w} \sum_c \log F(\mathfrak{a}_c)$. The factorization
[$\zeta_K(s) = \zeta(s) L(s, \chi)$](../../zeta-l-functions/dirichlet-l-functions/dedekind-zeta-quadratic-field-factorization.md),
which persists from $\operatorname{Re} s > 1$ to all of $\mathbb{C}$ as an identity of meromorphic functions, by the
[identity theorem](../../../Geometry/complex-and-symplectic-geometry/identity-and-open-mapping-theorems-for-holomorph/holomorphic-identity-on-connected-comple.md) on the complement of their poles, a connected open set, with
$\zeta(0) = -\frac{1}{2}$ and $\zeta'(0) = -\frac{1}{2} \log 2\pi$ (the case $a = 1$ of [Lerch's formula](../../zeta-l-functions/dirichlet-l-functions/lerch-formula-hurwitz-zeta.md)),
gives $L(0, \chi) = 2h/w$ and $\zeta_K'(0) = -\frac{h}{w} \log 2\pi - \frac{1}{2} L'(0, \chi)$. The character $\chi$ is not
the principal character modulo $|D|$: for that character
$L(s, \chi) = \zeta(s) \prod_{p \mid D} (1 - p^{-s})$, for $\operatorname{Re} s > 1$ by inclusion–exclusion over the primes dividing $D$
and then everywhere by the identity theorem, vanishes at $s = 0$, whereas $L(0, \chi) = 2h/w \neq 0$. So
[the formula for $L'(0, \chi)$](../../zeta-l-functions/dirichlet-l-functions/dirichlet-l-derivative-at-zero-gamma.md)
gives $L'(0, \chi) = \sum_{a=1}^{|D| - 1} \chi(a) \log \Gamma(a / |D|) - \frac{2h}{w} \log |D|$. Hence
$\sum_c \log F(\mathfrak{a}_c) = 12 h \log (2\pi / |D|) + 6 w \sum_{a} \chi(a) \log \Gamma(a / |D|)$, which is the
first formula. On the way, the computation gives
$\frac{1}{h} \sum_c \log(4\pi \operatorname{Im}(\tau_c) |\eta(\tau_c)|^4) = \frac{1}{2} \log |D| + L'(0, \chi) / L(0, \chi)$.

## Depends on

- [Quadratic Dirichlet character of a fundamental discriminant](../../congruences/power-residues-reciprocity/kronecker-symbol-and-quadratic-characters/quadratic-dirichlet-character.md)
- [The class group of a number field is finite](../../algebraic-number-theory/number-fields-embeddings/class-group-finite.md), for the $h$ ideal classes
- [A finitely generated torsion-free module over a principal ideal domain is free](../../../LinearAlgebra/eigenvalues-and-canonical-forms/finite-torsion-free-module-pid-free.md), for the $\mathbb{Z}$-bases $(\omega_1, \omega_2)$ of the fractional ideals $\mathfrak{a}_c$

## Proof depends on

- [Kronecker's first limit formula](kronecker-first-limit-formula.md), for the invariance of $\operatorname{Im}(\tau) |\eta(\tau)|^4$ under $\mathrm{SL}_2(\mathbb{Z})$, which makes the second form independent of the choice of $\mathfrak{a}_c$ and of its basis
- [Kronecker's limit formula for an imaginary quadratic field at $s = 0$](kronecker-limit-formula-imaginary-quadratic.md)
- [Dedekind zeta function of a quadratic field as $\zeta(s) L(s, \chi_D)$](../../zeta-l-functions/dirichlet-l-functions/dedekind-zeta-quadratic-field-factorization.md)
- [Lerch's formula for the Hurwitz zeta function at $s = 0$](../../zeta-l-functions/dirichlet-l-functions/lerch-formula-hurwitz-zeta.md), for $\zeta(0) = -\frac{1}{2}$ and $\zeta'(0) = -\frac{1}{2} \log 2\pi$, its case $a = 1$
- [The derivative at $s = 0$ of a Dirichlet $L$-function through the gamma function](../../zeta-l-functions/dirichlet-l-functions/dirichlet-l-derivative-at-zero-gamma.md)
- [Identity theorem for holomorphic maps](../../../Geometry/complex-and-symplectic-geometry/identity-and-open-mapping-theorems-for-holomorph/holomorphic-identity-on-connected-comple.md), for extending $\zeta_K(s) = \zeta(s) L(s, \chi)$ and the formula for the principal character from $\operatorname{Re} s > 1$

## Sources

- M. Kaneko, *A generalization of the Chowla–Selberg formula and the zeta functions of quadratic
  orders*, Proc. Japan Acad. 66, Ser. A (1990), 201–203,
  <https://www2.math.kyushu-u.ac.jp/~mkaneko/papers/07Chowla-Selberg.pdf>: Section 1, the definitions
  of $g_2$, $g_3$, $\Delta$ and $F(\mathfrak{a})$, property (1) and formula (2) (Chowla–Selberg), and the last paragraph,
  which says that the proof uses Kronecker's limit formula and a formula relating $L'(0, \chi)$ with the gamma
  function; Section 2, the outline of the proof (Kronecker's first limit formula and
  $\zeta_K(s) = \zeta(s) L(s, \chi)$).
- D. Zagier, *Elliptic modular forms and their applications*, in *The 1-2-3 of Modular Forms*,
  Universitext, Springer (2008), 1–103,
  <https://people.mpim-bonn.mpg.de/zagier/files/doi/10.1007/978-3-540-74119-0_1/fulltext.pdf>, §6.3,
  the Theorem with formula (96) (p. 84), stated with $\Phi(z) = \operatorname{Im}(z) |\eta(z)|^4$ and the
  product over the $h(D)$ CM points of discriminant $D$ modulo $\mathrm{SL}_2(\mathbb{Z})$, and the remarks
  after formula (97) (pp. 84–85).
- S. Chowla and A. Selberg, *On Epstein's zeta-function*, J. Reine Angew. Math. 227 (1967), 86–110, cited by
  Kaneko for the formula; Zagier notes that it is contained in a paper of Chowla and Selberg published in 1949
  and appears already in a paper of Lerch from 1897.
