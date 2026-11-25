# Talagrand's convex-distance inequality on a product of finite sets

Let $p$ be a probability vector on a finite set $\Omega$ and $P = p^{\otimes N}$. For every $N$
and every $A \subseteq \Omega^N$,

$$\Big(\sum_{x} P(x)\, e^{f_c^2(A, x)/4}\Big)\cdot P(A) \le 1,$$

that is $\int e^{f_c^2(A, \cdot)/4}\,dP \le 1/P(A)$ when $P(A) > 0$ (Talagrand, *Concentration of
measure and isoperimetric inequalities in product spaces*, Publ. Math. IHÉS 81 (1995), Theorem
4.1.1, (4.1.2), for a finite $\Omega$). The product form also covers $P(A) = 0$.

The proof is Talagrand's induction on $N$. For $N = 0$ the space is a point. For the step, fix
the first coordinate $\omega$ and put $\alpha = P(A(\omega))$, $\beta = P(B)$ and
$r = \alpha/\beta$. The geometric step, Hölder's inequality and the induction hypothesis bound the
sum over $x$ by $e^{(1-\lambda)^2/4}\alpha^{-\lambda}\beta^{-(1-\lambda)}$, and the numerical
lemma bounds this by $(2 - r)/\beta$. Summing over $\omega$ gives at most
$(2 - P(A)/\beta)/\beta$, and $u(2 - u) \le 1$ for $u = P(A)/\beta$ concludes.

## Informally uses

- [Talagrand's geometric step](convex-distance-cons-sq-le.md): the inequality (4.1.7).
- [Weighted Hölder inequality for two factors](sum-mul-rpow-mul-rpow-le.md): Hölder's inequality
  in the induction step.
- [Talagrand's numerical lemma](exists-exp-le-two-sub-mul-rpow.md): Lemma 4.1.3, the choice of
  $\lambda$.

## Background

- [Talagrand's convex-distance inequality](lintegral-exp-convex-distance-sq-le.md): the statement
  for an arbitrary probability space.
