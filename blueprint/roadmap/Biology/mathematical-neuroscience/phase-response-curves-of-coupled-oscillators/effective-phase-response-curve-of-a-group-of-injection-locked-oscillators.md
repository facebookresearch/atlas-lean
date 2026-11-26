# Effective phase response curve of a group of injection-locked oscillators

**Phase macromodel.** An oscillator $\frac{d}{dt}\mathbf{q}(\mathbf{x}) + \mathbf{f}(\mathbf{x}) + \mathbf{b}(t) = \mathbf{0}$ (an ODE or DAE) with an orbitally stable $T$-periodic solution, driven by a small input $\mathbf{b}(t)$, has a phase shift $\alpha(t)$ that obeys

$$ \dot\alpha(t) = \mathbf{v}_1^{\mathsf T}\big(t + \alpha(t)\big)\cdot\mathbf{b}(t), $$

where the $T$-periodic vector $\mathbf{v}_1$ is the **phase response curve** (PRC), also called the perturbation projection vector (PPV). It is the left Floquet eigenvector associated with the unit multiplier. In normalized phase $\phi = f(t + \alpha)$, with frequency $f = 1/T$ and $1$-periodic PRC $\mathbf{p}$, this reads $\dot\phi = f + f\,\mathbf{p}^{\mathsf T}(\phi)\cdot\mathbf{b}(t)$.

**Coupled phase system.** Take $N \ge 2$ oscillators $i = 1,\dots,N$ with frequencies $f_i$ and PRCs $\mathbf{p}_i$. Each receives an external input $\mathbf{a}_i(t)$ and $1$-periodic couplings $\mathbf{b}_{ij}(\phi_j)$ from the others:

$$ \dot\phi_i = f_i + f_i\,\mathbf{p}_i^{\mathsf T}(\phi_i)\cdot\Big(\mathbf{a}_i(t) + \sum_{j\ne i}\mathbf{b}_{ij}(\phi_j)\Big), \qquad\text{that is,}\qquad \dot{\boldsymbol\phi} = \mathbf{g}_\phi(\boldsymbol\phi) + \mathbf{b}_\phi(\boldsymbol\phi,t). $$

Assume that without external input the group locks stably to a common frequency $f^* = 1/T^*$, with phase $\boldsymbol\phi^*(t)$ such that $\boldsymbol\phi^*(t) - f^*t\,\mathbf{1}$ is $T^*$-periodic, and that the linearization of the system about $\boldsymbol\phi^*$ has exactly one Floquet multiplier equal to $1$.

**Basic facts.** Any time shift $\boldsymbol\phi^*(t - \tau)$ is again a locked solution. The linearized system has the $T^*$-periodic solution $\dot{\boldsymbol\phi}^*(t)$, so one multiplier is $1$, and stability gives $|\rho_i| \le 1$ for all multipliers.

**Theorem (hierarchical PRC).** Let $\mathbf{v}_1(t)$ be the $T^*$-periodic left Floquet vector of the linearized system for the unit multiplier, normalized by $\mathbf{v}_1^{\mathsf T}(t)\,\dot{\boldsymbol\phi}^*(t) \equiv 1$. If the external inputs are small and the scalar time shift $\hat\alpha(t)$ solves

$$ \dot{\hat\alpha}(t) = \mathbf{v}_1^{\mathsf T}\big(t + \hat\alpha(t)\big)\cdot\mathbf{b}_\phi\big(\boldsymbol\phi^*(t + \hat\alpha(t)),\,t\big), $$

then the solution of the coupled system is

$$ \boldsymbol\phi(t) = \boldsymbol\phi^*\big(t + \hat\alpha(t)\big) + \Delta\boldsymbol\phi(t), $$

with $\Delta\boldsymbol\phi(t)$ small and bounded for all $t$. The whole locked group therefore responds to small perturbations as a single oscillator, with one effective PRC $\mathbf{v}_1$, and the reduction can be applied recursively to groups of groups.

## Expansion

Linearizing naively about $\boldsymbol\phi^*(t)$ fails, because the neutral direction (multiplier $1$) lets phase errors grow secularly. Linearizing instead about the time-shifted orbit $\boldsymbol\phi^*(t + \hat\alpha(t))$ gives a linear periodically time-varying system. Its Floquet solution has a coefficient along the neutral mode that can blow up. The equation for $\hat\alpha$ is chosen exactly so that this coefficient vanishes. The remaining modes have multipliers strictly inside the unit circle, so their response to small forcing stays bounded. This is Winfree's phase reduction applied one level up, with the locked group as the oscillator.

## Sources

- Jaijeet Roychowdhury, "Hierarchical Abstraction of Phase Response Curves of Synchronized Systems of Coupled Oscillators", arXiv:1106.3247 (2011), Section 1 (PRC/PPV phase macromodels), Section 2 (coupled phase system, Assumptions 2.1–2.7, Lemmas 2.1–2.10 and the hierarchical PPV theorem), <https://doi.org/10.48550/arXiv.1106.3247>.
