# Solution of the SIS model with leaky vaccination

For real numbers $\beta$, $\gamma$, $\varepsilon$ and $N$, functions
$S_u, I_u, S_v, I_v : \mathbb{R} \to \mathbb{R}$ solve the SIS model with leaky vaccination, with
transmission rate $\beta$, recovery rate $\gamma$, vaccine efficacy $\varepsilon$ and population
size $N$, if at every time $t \ge 0$ they have two-sided derivatives with

$$
\begin{aligned}
S_u' &= -\frac{\beta S_u (I_u + I_v)}{N} + \gamma I_u, &
I_u' &= \frac{\beta S_u (I_u + I_v)}{N} - \gamma I_u, \\
S_v' &= -\frac{(1 - \varepsilon) \beta S_v (I_u + I_v)}{N} + \gamma I_v, &
I_v' &= \frac{(1 - \varepsilon) \beta S_v (I_u + I_v)}{N} - \gamma I_v,
\end{aligned}
$$

where the quotients by $N$ are read as $0$ when $N = 0$. The indices $u$ and $v$ are the
unvaccinated and vaccinated groups: a vaccinated susceptible is infected at $1 - \varepsilon$ times
the unvaccinated rate, and recovery returns an individual to the susceptible class of its group.
Nothing else is required: the functions need not be nonnegative, and the parameters are not
restricted. The epidemiological domain is $\beta \ge 0$, $\gamma > 0$, $0 \le \varepsilon \le 1$ and
$N > 0$.
