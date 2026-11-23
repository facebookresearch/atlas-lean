# Partial zeta functions of an imaginary quadratic field as Epstein zeta functions

Let $K$ be an imaginary quadratic field of discriminant $D < 0$, with ring of integers $\mathcal{O}_K$ and
$w$ roots of unity, and write $N$ for the absolute norm of fractional ideals. For an ideal class $A$ of
$K$ let

$$\zeta_K(s, A) = \sum_{\mathfrak{a} \in A} N(\mathfrak{a})^{-s} \qquad (\operatorname{Re} s > 1),$$

the sum running over the nonzero integral ideals $\mathfrak{a}$ of $\mathcal{O}_K$ in $A$, so that the
Dedekind zeta function of $K$ is $\zeta_K(s) = \sum_A \zeta_K(s, A)$, a sum over the $h$ ideal classes. Every
ideal class contains fractional ideals of the form $\mathfrak{b} = \mathbb{Z} + \mathbb{Z} z$ with
$\operatorname{Im} z > 0$: take a $\mathbb{Z}$-basis $(\alpha, \beta)$ of any fractional ideal of the class,
ordered so that $\operatorname{Im}(\beta / \alpha) > 0$, and divide by $\alpha$. If
$\mathfrak{b} = \mathbb{Z} + \mathbb{Z} z$, with $\operatorname{Im} z > 0$, lies in the inverse class $A^{-1}$,
then $2 \operatorname{Im} z = N(\mathfrak{b}) \sqrt{|D|}$ and

$$\zeta_K(s, A) = \frac{1}{w} \left( \frac{2}{\sqrt{|D|}} \right)^{s} Z(z, s), \qquad Z(z, s) = \sum_{(m, n) \neq (0, 0)} \frac{(\operatorname{Im} z)^s}{|m + n z|^{2s}} \qquad (\operatorname{Re} s > 1).$$

Choosing such a $\mathfrak{b}_A = \mathbb{Z} + \mathbb{Z} z_A$ in $A^{-1}$ for every class $A$ therefore gives
$\zeta_K(s) = \frac{1}{w} \bigl(2/\sqrt{|D|}\bigr)^{s} \sum_A Z(z_A, s)$ for $\operatorname{Re} s > 1$.

Indeed, $\mathfrak{a} \mapsto \mathfrak{a} \mathfrak{b}$ maps the integral ideals of $A$ bijectively onto the
principal ideals $(\gamma)$ with $0 \neq \gamma \in \mathfrak{b}$, and $N(\mathfrak{a}) = N(\gamma) / N(\mathfrak{b}) = |\gamma|^2 / N(\mathfrak{b})$
with $\gamma = m + n z$. Each such ideal has exactly $w$ generators: its generators are the $\gamma u$ with $u$ a unit of
$\mathcal{O}_K$, and the units, which have norm $|u|^2 = 1$, are the points of the lattice $\mathcal{O}_K \subset \mathbb{C}$ on the
unit circle, a finite group, hence the group of the $w$ roots of unity of $K$. For the relation
$2 \operatorname{Im} z = N(\mathfrak{b}) \sqrt{|D|}$, choose a positive integer $d$ with $d \mathfrak{b} \subseteq \mathcal{O}_K$. The
matrix expressing the basis $(d, d z)$ of $d \mathfrak{b}$ in a $\mathbb{Z}$-basis of $\mathcal{O}_K$ has determinant
$\pm [\mathcal{O}_K : d \mathfrak{b}] = \pm N(d \mathfrak{b}) = \pm d^2 N(\mathfrak{b})$, so the discriminant of $(d, d z)$, which is
$d^4 (z - \bar z)^2 = -4 d^4 (\operatorname{Im} z)^2$, equals $d^4 N(\mathfrak{b})^2 D = -d^4 N(\mathfrak{b})^2 |D|$; dividing by $-d^4$ gives
$4 (\operatorname{Im} z)^2 = N(\mathfrak{b})^2 |D|$.

## Depends on

This node has no prerequisites.

## Proof depends on

This node has no prerequisites.

## Sources

- C. L. Siegel, *Lectures on advanced analytic number theory*, notes by S. Raghavan, Tata Institute of
  Fundamental Research Lectures on Mathematics 23, Bombay (1961, reissued 1965),
  <https://www.math.tifr.res.in/~publ/ln/tifr23.pdf> (copy:
  <https://www-users.cse.umn.edu/~garrett/m/mfms/notes_2013-14/Siegel_AdvAnNoTh.pdf>), Chapter 2, §1,
  p. 64: for $\mathfrak{b} = [1, z] \in A^{-1}$, "$|z' - z| = 2y = N(\mathfrak{b}) \sqrt{|d|}$" and
  $\zeta(s, A) = \frac{1}{w} \bigl(\frac{2y}{\sqrt{|d|}}\bigr)^{s} \sum'_{m, n} |m + nz|^{-2s}$, and p. 67,
  $\zeta_d(s) = \sum_A \zeta(s, A)$.
