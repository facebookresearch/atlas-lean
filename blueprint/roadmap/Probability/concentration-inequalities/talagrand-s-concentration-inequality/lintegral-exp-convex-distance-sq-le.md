# Talagrand's convex-distance inequality

Let $(\Omega, \mu)$ be a probability space, $P = \mu^{\otimes N}$ the product probability on
$\Omega^N$ and $A \subseteq \Omega^N$ measurable. Then

$$\int \exp\Big(\frac14 f_c^2(A, x)\Big)\,dP(x) \le \frac{1}{P(A)}$$

(Talagrand, *Concentration of measure and isoperimetric inequalities in product spaces*, Publ.
Math. IHÉS 81 (1995), Theorem 4.1.1, (4.1.2)). Neither $N$ nor $\mu$ enters the bound.

The source treats $f_c(A, \cdot)$ as measurable and otherwise reads the integral as an upper
integral. The statement above uses the lower Lebesgue integral (the supremum of the integrals of measurable
minorants), which is at most the upper integral, so it follows from the source's statement. For a
finite $\Omega$ it holds in this very form:
[the measure form for a finite probability space](lintegral-exp-convex-distance-sq-le-of-f.md).

## Informally uses

- [Talagrand's geometric step](convex-distance-cons-sq-le.md): the inequality (4.1.7) of the
  induction on $N$.
- [Talagrand's numerical lemma](exists-exp-le-two-sub-mul-rpow.md): Lemma 4.1.3, combined with
  Hölder's inequality in the induction step.

## Background

- [Talagrand's convex distance](convex-distance.md): the distance being integrated.
- [Talagrand's concentration inequality around a median](talagrand-concentration-median.md): the
  form in which the inequality is usually applied, for convex Lipschitz functions of independent
  bounded variables (as stated in Tao's book).
