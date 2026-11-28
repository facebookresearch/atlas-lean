# Stability boundary for delayed case isolation under contact heterogeneity

**Homogeneous model with delayed isolation.** With proportions $S, I, R$, mixing parameter $\beta$, removal rate $\gamma$, isolated fraction $\alpha \in [0,1]$ and isolation delay $T_{\mathrm{delay}} \ge 0$,

$$\dot S = -\beta S (I - Q), \qquad \dot I = \beta S(I - Q) - \gamma I, \qquad Q(t) = \alpha\, e^{-\gamma T_{\mathrm{delay}}}\, I(t - T_{\mathrm{delay}}),$$

where $Q$ is the infectious-and-isolated fraction (cases found after the delay and still infectious).

**Heterogeneous model.** The population is partitioned by contact rate: $N_k$ individuals make $k$ contacts per unit time, the contact-rate distribution has mean $\mu$, standard deviation $\sigma$ and coefficient of variation $c_v = \sigma/\mu$. Susceptibles $X_k$ and infectives $Y_k$ of class $k$ satisfy $\dot X_k = -k\lambda X_k$, $\dot Y_k = k\lambda X_k - \gamma Y_k$, with force of infection per contact $\lambda = \rho\,\sum_k k Y_k / \sum_k k N_k$ and transmission probability per contact $\rho$; isolation acts with the same $\alpha$ and delay on each class.

**Lemma (equivalence).** About the all-susceptible equilibrium $X_k = N_k$, the heterogeneous model with delayed case isolation is asymptotically stable if and only if the linearization of the homogeneous model about $(S,I,R,Q) = (1,0,0,0)$ is asymptotically stable with mixing parameter

$$\beta = \rho\,\mu\,(c_v^2 + 1).$$

**Proposition (stability boundary).** Write $\beta = \rho\mu$ and $h = c_v^2 + 1$, and suppose $\beta h > \gamma$. The linearized heterogeneous dynamics with delayed case isolation are stable if and only if

$$T_{\mathrm{delay}} < \frac{1}{\gamma}\ln\Big(\frac{\alpha\beta h}{\beta h - \gamma}\Big).$$

**Corollary.** Let $\mathcal{R}_0 = \beta/\gamma > 1$ be the basic reproduction number of the homogeneous population with the same mean contact rate, and $\alpha \in [0,1)$. Some positive isolation delay is compatible with stability in the heterogeneous population if and only if

$$c_v^2 < \frac{1}{\mathcal{R}_0 (1 - \alpha)} - 1.$$

## Depends on

- [Solution of the Kermack–McKendrick SIR system](../../kermack-mckendrick-sir-model/is-solution.md)

## Expansion

Linearizing at the disease-free state and introducing $\lambda$ as a state reduces the class-structured system to the two-dimensional delay system $\dot I = -\gamma I + \mu(\lambda - \alpha e^{-\gamma T}\lambda(t - T))$, $\dot\lambda = \rho(\sigma^2/\mu + \mu)\big(\lambda - \alpha e^{-\gamma T}\lambda(t - T)\big) - \gamma\lambda$: the $\lambda$-equation is decoupled and has effective rate $\rho(\sigma^2/\mu + \mu) = \rho\mu(c_v^2 + 1)$, because new infections are drawn in proportion to contacts, so the second moment of the contact distribution enters. The resulting scalar delay equation $\dot z = (\beta h - \gamma) z - \beta h\,\alpha e^{-\gamma T} z(t - T)$ is stable iff its non-delayed loss dominates, $\beta h - \gamma < \beta h\,\alpha e^{-\gamma T}$ (positive feedback through the delay cannot produce oscillatory instability here), which rearranges to the stated bound. Requiring the bound to be positive gives the corollary: contact heterogeneity can make even instantaneous isolation of a fixed fraction insufficient.

## Sources

- Jonas Hansson, Alain Govaert, Richard Pates, Emma Tegling, Kristian Soltesz, "Limitations of time-delayed case isolation in heterogeneous SIR models", in 2022 American Control Conference (ACC) (2022), 2994–2999, <https://doi.org/10.23919/acc53348.2022.9867465>. Published version of arXiv:2209.09186, cited next; locators there refer to the arXiv version.
- Jonas Hansson, Alain Govaert, Richard Pates, Emma Tegling, "Limitations of time-delayed case isolation in heterogeneous SIR models", arXiv (2022). Section 2, Remark 1, Lemma 1, Proposition 2, Corollary 3. <https://doi.org/10.48550/arXiv.2209.09186>
