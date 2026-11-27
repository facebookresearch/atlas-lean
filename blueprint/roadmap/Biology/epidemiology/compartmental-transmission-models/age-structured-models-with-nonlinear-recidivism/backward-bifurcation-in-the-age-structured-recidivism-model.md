# Backward bifurcation in the age-structured recidivism model

**Setting.** Take the age-structured susceptible–infectious–temporarily-recovered model with nonlinear recidivism ([threshold stability of the infection-free state](threshold-stability-of-the-infection-free-state-with-recidivism.md)): infection at rate $\beta(a)B$, removal from the infectious class at rate $\phi(a)+\gamma(a)$, and relapse of recovered individuals at rate $\rho(a)B$, where $B$ is the force of infection.

**Theorem (existence).** If $\mathcal R_0>1$, the model has an endemic (non-uniform in age) steady-state distribution.

**Constant coefficients.** Now let $\mu,\beta,\rho,\phi,\gamma$ and the activity $c$ be positive constants, so $p_\infty(a) = \mu e^{-\mu a}$. For a prescribed force of infection $B$, the steady-state profiles are $s_B^*(a) = e^{-B\beta a}$ and explicit combinations of $e^{-B\beta a}$ and $e^{-(\phi+\gamma+B\rho)a}$ for $i_B^*$ and $r_B^*$. Self-consistency $B = \int_0^\infty i_B^*(a)p_\infty(a)\,da$ with $B>0$ becomes $\widehat G(B) = 1$, where

$$
\widehat G(B) = \frac{B + \frac{\mu}{\rho}}{\left(B + \frac{\mu}{\beta}\right)\left(B + \frac{\mu+\phi+\gamma}{\rho}\right)}, \qquad
\mathcal R_0 = \widehat G(0) = \frac{\beta}{\mu+\phi+\gamma}, \qquad \mathcal R_C = \frac{\beta}{\mu}.
$$

Write $x = \mu/\beta$, $y = (\mu+\phi+\gamma)/\rho$ and $z = \mu/\rho$. Then $\widehat G(B)=1$ is the quadratic

$$
B^2 + (x + y - 1)\,B + (xy - z) = 0 ,
$$

and it has two distinct roots in $(0,1)$, i.e. two endemic steady states coexisting with the stable infection-free state (a backward bifurcation), if and only if

$$
\mathcal R_0 < 1, \qquad \frac{\mu}{\beta} + \frac{\mu+\phi+\gamma}{\rho} < 1, \qquad (1 - x - y)^2 > 4(xy - z).
$$

These conditions force $\mathcal R_C>1$ and $\rho>\phi+\gamma$: relapse must be faster than removal from the infectious class. The paper displays the backward-bifurcation region as $\mathcal R_0<1<\mathcal R_C$ together with $\beta > \rho\mu/\bigl(\mu + (\sqrt\rho - \sqrt{\phi+\gamma})^2\bigr)$. Those inequalities, together with $\rho>\phi+\gamma$, are necessary consequences of the exact conditions above, but they are not sufficient.

## Depends on

- [Threshold stability of the infection-free state in an age-structured recidivism model](threshold-stability-of-the-infection-free-state-with-recidivism.md)

## Expansion

The product of the roots is $xy - z = \tfrac{\mu}{\rho}\bigl(\tfrac{1}{\mathcal R_0} - 1\bigr)$, so two positive roots require $\mathcal R_0<1$. Their sum $1 - x - y$ must be positive, and the discriminant must be positive. The larger root is below the sum, hence below $1$, so the restriction $B<1$ is automatic. For $\mathcal R_0<1$ the infection-free state is locally stable, so these two positive equilibria give bistability: a large enough introduction can establish endemic infection sustained by relapse, even though a single case does not replace itself. Since relapse feeds the infectious class through $\rho B r$ without depleting susceptibles, the backward branch disappears when $\rho\le\phi+\gamma$. When $\mathcal R_C<1$, global stability of the infection-free state rules out any endemic equilibrium.

## Sources

- Fabio Sanchez, Juan G. Calvo, Esteban Segura, Zhilan Feng, "A partial differential equation model with age-structure and nonlinear recidivism: Conditions for a backward bifurcation and a general numerical implementation", Computers & Mathematics with Applications 78 (2019), 3916–3930, <https://doi.org/10.1016/j.camwa.2019.06.021>. Published version of arXiv:1712.09105, cited next; locators there refer to the arXiv version.
- Fabio Sanchez, Juan G. Calvo, Esteban Segura, Zhilan Feng, "A Partial Differential Equation Model with Age-Structure and Nonlinear Recidivism: Conditions for a Backward Bifurcation and a General Numerical Implementation", arXiv 2017: Theorem 4.1 and Section 4.2, "Conditions for a backward bifurcation" (the formula for $\widehat G$ and the paper's displayed conditions). The exact root conditions above follow by direct algebra on $\widehat G(B)=1$. <https://doi.org/10.48550/arXiv.1712.09105>
