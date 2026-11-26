# Minor-outbreak probabilities in a host–vector branching process

**Model (Ross).** Constant host and vector populations $H$ and $M$; $I$ infectious hosts recover at rate $\gamma$; infectious vectors $V$ infect hosts at rate $\alpha V S/H$; susceptible vectors $U$ acquire infection at rate $\beta U I/H$; vectors are born and die at rate $\mu$:

$$\dot S = -\alpha V\frac{S}{H} + \gamma I,\quad \dot I = \alpha V\frac{S}{H} - \gamma I,\quad \dot U = -\beta U\frac{I}{H} + \mu M - \mu U,\quad \dot V = \beta U\frac{I}{H} - \mu V \quad \text{(Eq. 8)}.$$

At the disease-free equilibrium $(H, 0, M, 0)$ the threshold quantity is

$$R_0 = \frac{\alpha}{\mu}\cdot\frac{\beta M/H}{\gamma} \qquad \text{(Eq. 10)},$$

the square of the spectral radius of $FV^{-1}$ for $F = \begin{pmatrix} 0 & \alpha \\ \beta M/H & 0\end{pmatrix}$, $V = \mathrm{diag}(\gamma, \mu)$.

**Branching approximation.** Near the disease-free equilibrium $(I, V)$ is a two-type branching process with offspring generating functions

$$f_1(u_1,u_2) = \frac{\gamma}{\gamma + \beta M/H} + \frac{\beta M/H}{\gamma + \beta M/H}\,u_1 u_2, \qquad f_2(u_1,u_2) = \frac{\mu}{\mu+\alpha} + \frac{\alpha}{\mu+\alpha}\,u_1u_2 \quad \text{(Eqs. 11–12)}.$$

**Proposition.** If $R_0 > 1$, the system $f_1(u) = u_1$, $f_2(u) = u_2$ has in $[0,1]^2$ the solutions $(1,1)$ and $(q_1, q_2)$ with

$$q_1 = \frac{\gamma}{\gamma + \beta M/H} + \frac{\beta M/H}{\gamma + \beta M/H}\cdot\frac{1}{R_0}, \qquad q_2 = \frac{\mu}{\mu+\alpha} + \frac{\alpha}{\mu+\alpha}\cdot\frac{1}{R_0} \quad \text{(Eqs. 13–14)},$$

and starting from $I(0) = i$, $V(0) = v$,

$$\mathbb{P}(\text{minor outbreak}) = \begin{cases} q_1^{\,i}\, q_2^{\,v}, & R_0 > 1,\\ 1, & R_0 < 1.\end{cases}$$

**Link to the next-generation matrix.** With $\mathbf{M}$ the Jacobian of $(f_1, f_2)$ at $(1,1)$ and $W = \mathrm{diag}(\gamma + \beta M/H,\ \mu + \alpha)$,

$$W(\mathbf{M} - I) = (F - V)^{\top} \qquad \text{(Eq. 15, up to the orientation convention for } \mathbf{M}),$$

so $\rho(\mathbf{M}) > 1 \iff R_0 > 1$.

## Depends on

- [Whittle's minor-outbreak probability for the stochastic SIR model](whittle-minor-outbreak-probability-for-the-stochastic-sir-model.md)

## Expansion

Write $a_1 = \gamma/(\gamma + \beta M/H)$ and $a_2 = \mu/(\mu + \alpha)$. Both fixed-point equations have the form $u_j = a_j + (1 - a_j)u_1u_2$, so at a fixed point $u_1 u_2 = (u_j - a_j)/(1 - a_j)$ for $j = 1, 2$. Substituting $q_1, q_2$ gives $q_1 q_2 = \gamma\mu/(\alpha\beta M/H) = 1/R_0$, which makes both equations hold. The value $q_1$ reads: an infectious host either recovers first, or infects a vector whose lineage then fails with probability $1/R_0$. Eq. 15 follows by multiplying each row of $\mathbf{M} - I$ by its total event rate: row 1 becomes $(-\gamma, \beta M/H)$ and row 2 becomes $(\alpha, -\mu)$. With $H = 100$, $M = 1000$, $\alpha = \beta = 0.2$, $\gamma = 0.1$, $\mu = 0.5$ one gets $R_0 = 8$, $q_1 = 1/6$, $q_2 = 3/4$.

## Sources

- L. J. S. Allen, "A primer on stochastic epidemic models: Formulation, numerical simulation, and analysis", Infectious Disease Modelling 2(2) (2017) 128–142, Sections 5–6, Eqs. 8–15, <https://doi.org/10.1016/j.idm.2017.03.001> (PMC6002090).
- L. J. S. Allen and P. van den Driessche, "Relations between deterministic and stochastic thresholds for disease extinction in continuous- and discrete-time infectious disease models", Math. Biosci. 243 (2013) 99–108.
