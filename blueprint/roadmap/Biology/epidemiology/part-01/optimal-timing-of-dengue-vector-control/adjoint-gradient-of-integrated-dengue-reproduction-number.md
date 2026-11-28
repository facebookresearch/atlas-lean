# Adjoint gradient of the time-integrated dengue reproduction number

For dengue in a homogeneously mixed susceptible human population, the basic reproduction number driven by the adult female *Aedes* population $A$ is

$$R_0 = \frac{A}{N_H}\, n_B^2\, \gamma_{a,e}^2\, \phi_{HV}\phi_{VH}\, \gamma_{a,d}^{-1}\, \eta_H^{-1}\Big(1 + \frac{\gamma_{a,d}}{\gamma_V}\Big)^{-1},$$

where $N_H$ is the human population, $\eta_H^{-1}$ and $\gamma_V^{-1}$ are the intrinsic and extrinsic incubation periods, $\gamma_{a,d}$ is the adult mosquito mortality rate, $\gamma_{a,e}^{-1}$ the gonotrophic cycle length, $n_B$ the number of bites per gonotrophic cycle, and $\phi_{VH},\phi_{HV}$ the per-bite transmission probabilities. With temperature-dependent entomological rates, $R_0(x(t),t)$ varies in time both directly and through the stage-structured mosquito state $x(t)$ (eggs, larvae, pupae, adults).

Interventions (larvicide, adulticide, breeding-site removal) are encoded by timing parameters $p$ that switch on fixed temporal profiles of added mortality or reduced capacity. The scheduling problem is

$$\min_p\ F(p) = \int_0^T R_0\big(x(t;p),t\big)\,dt \quad\text{subject to}\quad h(x,\dot x,p,t) = 0,\ \ g(x(0)) = 0.$$

**Theorem (adjoint formula).** Assume $h$ is continuously differentiable in $(x,\dot x,p)$, the initial condition does not depend on $p$, and $R_0$ is continuously differentiable in $x$. Let $\lambda$ solve the backward adjoint system

$$\dot\lambda^{\top}\,\partial_{\dot x} h = \lambda^{\top}\big(\partial_x h - \tfrac{d}{dt}(\partial_{\dot x} h)\big) + \partial_x R_0, \qquad \lambda(T) = 0.$$

Then

$$\frac{dF}{dp} = \int_0^T \lambda(t)^{\top}\, \partial_p h(x,\dot x,p,t)\,dt.$$

One forward solve of the mosquito model and one backward adjoint solve therefore give the full gradient with respect to all intervention times, which drives gradient descent on the schedule.

## Expansion

Add $\int_0^T \lambda^{\top} h\,dt = 0$ to $F$ and differentiate in $p$. The terms in $\partial_p x$ and $\partial_p \dot x$ are collected by integrating the $\dot x$-term by parts; the adjoint equation is chosen to cancel every coefficient of $\partial_p x$, and the terminal condition $\lambda(T) = 0$ together with $p$-independent initial data removes the boundary terms. What remains is the explicit dependence of the constraint on $p$. Because $R_0$ is linear in $A$, $\partial_x R_0$ is nonzero only in the adult compartments, so the adjoint is forced only through adults.

## Sources

- Aram Vajdi, Lee W. Cohnstaedt, Caterina M. Scoglio, Heman Shakeri, "Optimal scheduling of dengue vector control", arXiv (2026). Section 2 (reproduction number and optimization problem), Appendix (Theorem A.1, adjoint formula for the gradient). <https://doi.org/10.48550/arXiv.2605.12441>. Published version: Journal of Theoretical Biology 637 (2027), article 112617, <https://doi.org/10.1016/j.jtbi.2026.112617>; locators above refer to the arXiv version.
