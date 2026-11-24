# Partial zeta functions of an imaginary quadratic field as Epstein zeta functions

Let $K$ be an imaginary quadratic field of discriminant $D < 0$, with ring of integers $\mathcal{O}_K$ and
$w$ roots of unity. Write $N$ for the [absolute norm](../../../RingTheory/dedekind-domains/ideal-absolute-norm.md) of ideals,
$N(\mathfrak{a}) = \#(\mathcal{O}_K / \mathfrak{a})$ for a nonzero ideal $\mathfrak{a}$ of $\mathcal{O}_K$, extended to fractional ideals
by $N(\mathfrak{b}) = N(d \mathfrak{b}) / d^2$ for a positive integer $d$ with $d \mathfrak{b} \subseteq \mathcal{O}_K$, which does not
depend on $d$ because $N$ is multiplicative and $N(d \mathcal{O}_K) = d^2$
([norm of a principal ideal](../../../RingTheory/dedekind-domains/ideal-absolute-norm-principal.md)). For an ideal class $A$ of
$K$ let

$$\zeta_K(s, A) = \sum_{\mathfrak{a} \in A} N(\mathfrak{a})^{-s} \qquad (\operatorname{Re} s > 1),$$

the sum running over the nonzero integral ideals $\mathfrak{a}$ of $\mathcal{O}_K$ in $A$, so that the
Dedekind zeta function of $K$ is $\zeta_K(s) = \sum_A \zeta_K(s, A)$, a sum over the $h$ ideal classes, finitely many by the
[finiteness of the class group](../../algebraic-number-theory/number-fields-embeddings/class-group-finite.md). Every
ideal class contains fractional ideals of the form $\mathfrak{b} = \mathbb{Z} + \mathbb{Z} z$ with
$\operatorname{Im} z > 0$: take a $\mathbb{Z}$-basis $(\alpha, \beta)$, ordered so that $\operatorname{Im}(\beta / \alpha) > 0$, of any
fractional ideal of the class, a finitely generated torsion-free $\mathbb{Z}$-module and hence
[free](../../../LinearAlgebra/eigenvalues-and-canonical-forms/finite-torsion-free-module-pid-free.md) of rank $2$, and divide
by $\alpha$. If
$\mathfrak{b} = \mathbb{Z} + \mathbb{Z} z$, with $\operatorname{Im} z > 0$, lies in the inverse class $A^{-1}$,
then $2 \operatorname{Im} z = N(\mathfrak{b}) \sqrt{|D|}$ and

$$\zeta_K(s, A) = \frac{1}{w} \left( \frac{2}{\sqrt{|D|}} \right)^{s} Z(z, s), \qquad Z(z, s) = \sum_{(m, n) \neq (0, 0)} \frac{(\operatorname{Im} z)^s}{|m + n z|^{2s}} \qquad (\operatorname{Re} s > 1).$$

Choosing such a $\mathfrak{b}_A = \mathbb{Z} + \mathbb{Z} z_A$ in $A^{-1}$ for every class $A$ therefore gives
$\zeta_K(s) = \frac{1}{w} \bigl(2/\sqrt{|D|}\bigr)^{s} \sum_A Z(z_A, s)$ for $\operatorname{Re} s > 1$.

Indeed, $\mathfrak{a} \mapsto \mathfrak{a} \mathfrak{b}$ maps the integral ideals of $A$ bijectively onto the
principal ideals $(\gamma)$ with $0 \neq \gamma \in \mathfrak{b}$, and $N(\mathfrak{a}) = |\gamma|^2 / N(\mathfrak{b})$ with
$\gamma = m + n z$: if $d \mathfrak{b} \subseteq \mathcal{O}_K$, then $\mathfrak{a} \cdot d \mathfrak{b} = (d \gamma)$, so
$N(\mathfrak{a}) N(d \mathfrak{b}) = N((d \gamma)) = |N_{K/\mathbb{Q}}(d \gamma)| = d^2 |\gamma|^2$, by the multiplicativity of $N$ and the
norm of a principal ideal. Each such ideal has exactly $w$ generators: its generators are the $\gamma u$ with $u$ a unit of
$\mathcal{O}_K$, and the units are the elements of $\mathcal{O}_K$ of
[norm $\pm 1$](../../algebraic-number-theory/discriminants-ramification/unit-iff-norm-plus-minus-one.md), that is, as
$N_{K/\mathbb{Q}}(u) = |u|^2$, the points of the lattice $\mathcal{O}_K \subset \mathbb{C}$ on the unit circle, a finite group,
hence the group of the $w$ roots of unity of $K$. For the relation $2 \operatorname{Im} z = N(\mathfrak{b}) \sqrt{|D|}$, choose a
positive integer $d$ with $d \mathfrak{b} \subseteq \mathcal{O}_K$ and a $\mathbb{Z}$-basis $(\omega_1, \omega_2)$ of $\mathcal{O}_K$, whose
discriminant is $D$, and let $T$ be the matrix of the coordinates of the basis $(d, d z)$ of $d \mathfrak{b}$ in it. Then
[$|\det T| = N(d \mathfrak{b})$](../../../RingTheory/dedekind-domains/ideal-absolute-norm-det-basis-change.md) $= d^2 N(\mathfrak{b})$, so
by the [change of basis for discriminants](../../../RingTheory/algebras-and-differentials/discriminant-change-of-basis.md) the
discriminant of $(d, d z)$, which is $d^4 (z - \bar z)^2 = -4 d^4 (\operatorname{Im} z)^2$, equals
$(\det T)^2 D = -d^4 N(\mathfrak{b})^2 |D|$; dividing by $-d^4$ gives $4 (\operatorname{Im} z)^2 = N(\mathfrak{b})^2 |D|$.

## Depends on

- [Absolute norm of an ideal](../../../RingTheory/dedekind-domains/ideal-absolute-norm.md), for $N$ and its multiplicativity
- [The absolute norm of a principal ideal](../../../RingTheory/dedekind-domains/ideal-absolute-norm-principal.md), for $N(d \mathcal{O}_K) = d^2$, which makes $N(\mathfrak{b})$ independent of $d$
- [The class group of a number field is finite](../../algebraic-number-theory/number-fields-embeddings/class-group-finite.md), for the $h$ ideal classes
- [A finitely generated torsion-free module over a principal ideal domain is free](../../../LinearAlgebra/eigenvalues-and-canonical-forms/finite-torsion-free-module-pid-free.md), for the $\mathbb{Z}$-bases of fractional ideals

## Proof depends on

- [An algebraic integer of a number field is a unit if and only if its norm is ±1](../../algebraic-number-theory/discriminants-ramification/unit-iff-norm-plus-minus-one.md), for the units of $\mathcal{O}_K$
- [The absolute norm of an ideal as a determinant](../../../RingTheory/dedekind-domains/ideal-absolute-norm-det-basis-change.md), for $|\det T| = N(d \mathfrak{b})$
- [Discriminants under a change of basis](../../../RingTheory/algebras-and-differentials/discriminant-change-of-basis.md), for the discriminant of $(d, d z)$

## Sources

- C. L. Siegel, *Lectures on advanced analytic number theory*, notes by S. Raghavan, Tata Institute of
  Fundamental Research Lectures on Mathematics 23, Bombay (1961, reissued 1965),
  <https://www.math.tifr.res.in/~publ/ln/tifr23.pdf> (copy:
  <https://www-users.cse.umn.edu/~garrett/m/mfms/notes_2013-14/Siegel_AdvAnNoTh.pdf>), Chapter 2, §1,
  p. 64: for $\mathfrak{b} = [1, z] \in A^{-1}$, "$|z' - z| = 2y = N(\mathfrak{b}) \sqrt{|d|}$" and
  $\zeta(s, A) = \frac{1}{w} \bigl(\frac{2y}{\sqrt{|d|}}\bigr)^{s} \sum'_{m, n} |m + nz|^{-2s}$, and p. 67,
  $\zeta_d(s) = \sum_A \zeta(s, A)$.
