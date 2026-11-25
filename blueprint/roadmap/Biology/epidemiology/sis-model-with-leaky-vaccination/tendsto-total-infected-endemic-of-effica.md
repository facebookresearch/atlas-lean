# With zero efficacy and γ < β, an infection present at time 0 settles at the SIS level

Let $0 \le \gamma < \beta$ and $N > 0$, and let $(S_u, I_u, S_v, I_v)$ be a
[solution](is-solution.md) of the SIS model with leaky vaccination, with transmission rate $\beta$,
recovery rate $\gamma$, vaccine efficacy $0$ and population size $N$, with total population
$S_u(0) + S_v(0) + I_u(0) + I_v(0) = N$ and $I_u(0) + I_v(0) > 0$. Then the total infected converges
to the endemic level of the SIS model:

$$I_u(t) + I_v(t) \to N \Bigl(1 - \frac{\gamma}{\beta}\Bigr) \quad (t \to \infty).$$

This is the [endemic limit of the SIS model](../sis-epidemic-model/tendsto-infected-endemic.md)
applied to the totals.
