# Performance sensitivity of powerstroke–recovery limit cycles

**Setting.** Let $\dot z = F_\kappa(z)$, $z = (a, x)$ (neural and mechanical variables, coupled through motor output and sensory feedback), have for each parameter $\kappa$ in an interval $I$ an asymptotically stable limit cycle $\gamma_\kappa$ of period $T_\kappa$; $F_\kappa$ may be piecewise smooth across surfaces separating phases. Let $q_\kappa(\cdot)$ be the instantaneous rate of progress and define the progress per cycle and the task performance

$$y_\kappa = \int_0^{T_\kappa} q_\kappa(\gamma_\kappa(t))\,dt, \qquad Q(\kappa) = \frac{y_\kappa}{T_\kappa}.$$

The source's Eq. (2) prints the upper limit $\kappa$, $Q(\kappa)=\frac1{T_\kappa}\int_0^{\kappa}q_\kappa(\gamma_\kappa(t))\,dt$; the page writes $T_\kappa$ because $Q$ is the progress per cycle divided by the period, as the source's text defines it, and the integral must run over one full period of $\gamma_\kappa$.

In a **powerstroke–recovery** system, $t = 0$ is the start of the powerstroke of duration $T^{ps}_\kappa$, and $q_\kappa \equiv 0$ during the recovery of duration $T^{re}_\kappa = T_\kappa - T^{ps}_\kappa$. The **sensitivity** to a sustained perturbation $\kappa_0 \to \kappa_0 + \epsilon$ is $S = \partial Q/\partial\kappa(\kappa_0)$; $S = 0$ means first-order performance homeostasis.

**Infinitesimal shape response curve (iSRC).** With a monotone time rescaling $\tau_\epsilon$ mapping $[0,T_0)$ onto $[0,T_\epsilon)$, write $\gamma_\epsilon(\tau_\epsilon(t)) = \gamma_0(t) + \epsilon\,\gamma_1(t) + O(\epsilon^2)$. Then $\gamma_1$ solves

$$\dot\gamma_1 = DF_0(\gamma_0(t))\,\gamma_1 + \nu_1(t)\,F_0(\gamma_0(t)) + \partial_\kappa F_\kappa(\gamma_0(t))\big|_{\kappa_0}, \qquad \nu_1 = \partial_\epsilon\partial_t \tau_\epsilon\big|_{\epsilon=0},$$

with $\gamma_1(0)$ the displacement of the cycle's crossing point on a transverse section. Take $\tau_\epsilon$ linear within each phase: $\tau_\epsilon(t) = (T^{ps}_\epsilon/T^{ps}_0)\,t$ on $[0, T^{ps}_0)$ and $\tau_\epsilon(t) = T^{ps}_\epsilon + (T^{re}_\epsilon/T^{re}_0)(t - T^{ps}_0)$ on $[T^{ps}_0, T_0)$; then $\nu_1 = T_1^{i}/T_0^{i}$ on phase $i \in \{ps, re\}$. This is the time scaling the source fixes in Sec. 2.2 before Eq. (10) and uses in Appendix C.3; the first sensitivity formula below depends on the rescaling and uses the iSRC $\gamma_1$ of this phase-wise linear rescaling.

**Local timing response curve (lTRC).** The gradient $\eta_i$ of the time remaining in phase $i$ solves the adjoint equation $\dot\eta_i = -DF_0(\gamma_0(t))^{\mathsf T}\eta_i$ with $\eta_i(z^{out}_0) = -n^{out}/\bigl((n^{out})^{\mathsf T} F_0(z^{out}_0)\bigr)$, where $n^{out}$ is normal to the exit surface. The first-order change of the phase duration is

$$T_1^{i} = \eta_i(z^{in}_0)\cdot\partial_\kappa z^{in}_\kappa - \eta_i(z^{out}_0)\cdot\partial_\kappa z^{out}_\kappa + \int_{t^{in}}^{t^{out}} \eta_i(\gamma_0(t))\cdot\partial_\kappa F_\kappa(\gamma_0(t))\,dt .$$

**Sensitivity formulas.** With $\beta_0 = T_0^{ps}/T_0$ and $\beta_1 = (T_1^{ps}T_0 - T_0^{ps}T_1)/T_0^2$,

$$\frac{\partial Q}{\partial\kappa}(\kappa_0) = \frac{1}{T_0^{ps}}\int_0^{T_0^{ps}} \Bigl[\beta_0\bigl(\nabla q_0(\gamma_0)\cdot\gamma_1 + \partial_\kappa q_\kappa(\gamma_0)\bigr) + \beta_1\, q_0(\gamma_0)\Bigr] dt,$$

and equivalently, expanding $y_\epsilon = y_0 + \epsilon y_1 + O(\epsilon^2)$ and $T_\epsilon = T_0 + \epsilon T_1 + O(\epsilon^2)$ with $T_1 = T_1^{ps} + T_1^{re}$,

$$\frac{\partial Q}{\partial\kappa}(\kappa_0) = Q_0\left(\frac{y_1}{y_0} - \frac{T_1}{T_0}\right).$$

## Expansion

The second formula is the quotient rule applied to $Q = y/T$: performance is robust exactly when the relative change in progress per cycle, a shape effect read off the mechanical component of the iSRC over the powerstroke, cancels the relative change in period, a timing effect computed phase by phase from the lTRC. The first formula differentiates the powerstroke average directly, splitting the change into a shape term (perturbed trajectory and explicit parameter dependence of $q$) and a timing term (shift $\beta_1$ in the powerstroke's share of the cycle). The lTRC boundary condition normalizes $\eta_i$ so that moving the exit point along the flow by one unit of time reduces the remaining time by one. Because $S$ is linear in the iSRC and lTRC, which depend on the feedback pathway through $F$, the formulas compare candidate sensory feedback functions without simulating each perturbed cycle.

## Sources

- Z. Yu, P. J. Thomas, "Variational analysis of sensory feedback mechanisms in powerstroke-recovery systems", Biological Cybernetics 118 (2024) 277–309, Equations (2)–(12) and Appendix C, <https://doi.org/10.1007/s00422-024-00996-x>, PMCID PMC11588830.
