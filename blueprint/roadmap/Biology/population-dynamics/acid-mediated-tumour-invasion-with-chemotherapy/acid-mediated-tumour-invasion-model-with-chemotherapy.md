# Acid-mediated tumour invasion model with chemotherapy

**Model.** Let $u_1$, $u_2$ be the normal and tumour cell densities (scaled by their carrying capacities), $u_3$ the excess $\mathrm{H}^+$ ion concentration produced by glycolytic tumour cells, and $u_4$ the concentration of a cytotoxic drug infused at normalized rate $i(t) \ge 0$ (mean $1$ over a treatment cycle). In nondimensional form,
$$\begin{aligned}
u_1' &= u_1(1 - u_1 - \alpha_1u_2 - \delta_1u_3), &\qquad u_3' &= \beta_3(u_2 - u_3),\\
u_2' &= \beta_2u_2(1 - u_2 - \alpha_2u_1 - \delta_2u_4), &\qquad u_4' &= \beta_4\big(i(t) - u_4 - \delta_4u_4u_2\big),
\end{aligned}$$
with logistic growth and Lotka–Volterra competition ($\alpha_1, \alpha_2$), acid kill of normal cells ($\delta_1$, tumour aggressiveness), drug kill of tumour cells ($\delta_2$, chemotherapy strength, the main control parameter), and drug consumption by tumour cells ($\delta_4$); all parameters are positive.

**Theorem (well-posedness and positivity).** If $i \in C(\mathbb{R}_+, [0, i_M])$ and $\mathbf{u}(0) \in \mathbb{R}^4_+$, the system has a unique global solution with $\mathbf{u}(t) \in \mathbb{R}^4_+$ for all $t \ge 0$; the faces $\{u_1 = 0\}$ and $\{u_2 = 0\}$ are invariant.

**Steady states under constant infusion ($i \equiv 1$).** The equilibria are
1. $(0,0,0,1)$, always unstable;
2. the tumour-free state $(1,0,0,1)$, stable if and only if $\alpha_2 + \delta_2 > 1$;
3. the normal-tissue-free (invasive) state $(0, \hat u, \hat u, (1+\delta_4\hat u)^{-1})$ with $\delta_4\hat u^2 + (1-\delta_4)\hat u + \delta_2 - 1 = 0$, stable when, writing $\kappa = \alpha_1 + \delta_1$, either $\delta_2 < (\kappa + \delta_4)(\kappa - 1)/\kappa^2$, or $(\kappa+\delta_4)(\kappa-1)/\kappa^2 \le \delta_2 < (1+\delta_4)^2/(4\delta_4)$ and $1/\delta_4 < (\kappa - 2)/\kappa$; in particular it requires $\kappa > 1$;
4. a coexistence state $(1 - \kappa\tilde u, \tilde u, \tilde u, (1+\delta_4\tilde u)^{-1})$, where $\tilde u$ solves $\delta_4[1 - \alpha_2\kappa]\tilde u^2 + [1 - \alpha_2\kappa + \delta_4(\alpha_2 - 1)]\tilde u + \delta_2 + \alpha_2 - 1 = 0$, which exists and is stable only for weak competition, low aggressiveness and weak treatment.

For the tumour–drug subsystem ($\alpha_2 = 0$), the tumour-free state is stable for $\delta_2 > 1$, and if $\delta_2 \ge 1$ with $\delta_4 < 1$, or $\delta_2 > (1+\delta_4)^2/(4\delta_4)$, the tumour is eradicated because no positive tumour equilibrium exists.

## Expansion

Positivity and global existence follow from the invariance theorem for ODEs: the box $\prod_k[0, \max\{\cdot\}]$ with corners at the carrying capacities, the initial data and $i_M$ satisfies the tangent condition on every face, and the right-hand side is locally Lipschitz. The stability thresholds come from the Jacobian at each equilibrium; the condition $\alpha_2 + \delta_2 > 1$ shows that competition from healthy tissue and chemotherapy add up, so a drug too weak to clear the tumour alone ($\delta_2 < 1$) can succeed when normal tissue competes strongly enough. Bistability between the tumour-free and invasive states is possible, in which case the outcome depends on the initial tumour burden.

## Depends on

- [Explicit solution of the logistic equation](../logistic-growth-equation/logistic.md)

## Sources

- Andrew B. Holder, Marianito R. Rodrigo, "Model for Acid-Mediated Tumour Invasion with Chemotherapy Intervention I: Homogeneous Populations", arXiv:1412.0748 (2014): Section 2 (model, nondimensionalization, Theorem 2.1), Section 3.1 (steady states and stability, with full conditions in the appendix lemma on the full-system steady states), Section 3.2 (reduced tumour–drug model). <https://doi.org/10.48550/arXiv.1412.0748>
