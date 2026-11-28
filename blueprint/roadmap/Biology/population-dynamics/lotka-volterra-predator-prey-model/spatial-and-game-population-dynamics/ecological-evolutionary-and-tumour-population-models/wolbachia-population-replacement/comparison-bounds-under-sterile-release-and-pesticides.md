# Comparison bounds under sterile release and pesticides

In the Wolbachia replacement model, release infected sterile mosquitoes at rate $R(t)$ and spray pesticides causing excess death rates $\phi_I(t), \phi_U(t)$ (Eq. 4):

$$\frac{dx}{dt} = (b_I - \delta_I - \phi_I(t))\, x - d\, x (x + y), \qquad \frac{dy}{dt} = b_U\, \frac{y}{x + y + R(t)}\, y - (\delta_U + \phi_U(t))\, y - d\, y (x + y).$$

**Sterile release** (Thm. 1). Take $\phi_I = \phi_U = 0$ and suppose the release ratio $K(t) = R(t)/(x(t) + y(t))$ satisfies $K_1 < K(t) < K_2$ (Eq. 8). Put $\bar b_U = b_U/(1 + K_2)$ and $\hat b_U = b_U/(1 + K_1)$ (Eq. 10), and let $(X, Y)$, $(X_1, Y_1)$, $(X_2, Y_2)$ solve the release model and the release-free model with $b_U$ replaced by $\bar b_U$ and by $\hat b_U$, respectively (Eqs. 11–12), all from the same initial state $(x_0, y_0)$. If the release-free solution from $(x_0, y_0)$ tends to the infected-only equilibrium and $\bar b_U < \hat b_U$, then

$$Y(t) \to 0 \quad (t \to \infty), \qquad Y_1(t) \le Y(t) \le Y_2(t) \quad \text{for all } t \ge 0.$$

**Pesticides acting equally** (Remark 2.2). If $\phi_I \equiv \phi_U$, the infection frequency is unaffected by spraying, and the wild population is sandwiched between the solutions with the death rates frozen at $\min \phi$ and at $\max \phi$.

**Unequal pesticide damage** (Remark 2.3). If $\phi_I \not\equiv \phi_U$, with $a(t) = b_I - \delta_I - \phi_I(t) + \delta_U + \phi_U(t)$ (Eq. 15) the frequency obeys $p' = p(1 - p)\big(a(t) - b_U(1 - p)\big)$ (Eq. 16); spraying that harms infected mosquitoes more than uninfected ones lowers $a$ and can slow or prevent the elimination of wild mosquitoes.

## Depends on

- [Wolbachia infection-frequency threshold](wolbachia-infection-frequency-threshold.md)

## Proof depends on

Its proof consists of the steps listed under Expansion.

## Expansion

Since $y/(x + y + R) = \frac{1}{1 + K(t)} \cdot \frac{y}{x + y}$, release acts as a time-varying reduction of the uninfected birth rate to $b_U/(1 + K(t)) \in (\bar b_U, \hat b_U)$. The frequency equations $p_i' = p_i(1 - p_i)(b_I - \delta_I + \delta_U - \beta_i(1 - p_i))$ are ordered in the birth parameter $\beta_i$, and a first-crossing-time argument shows that the trajectories, and then the uninfected numbers, can never cross, which gives the sandwich bounds.

## Sources

- L. Hu, C. Yang, Y. Hui, et al., *Mosquito control based on pesticides and endosymbiotic bacterium Wolbachia*, Bull. Math. Biol. (2021). <https://doi.org/10.1007/s11538-021-00881-9> (PMCID: PMC8043933)
