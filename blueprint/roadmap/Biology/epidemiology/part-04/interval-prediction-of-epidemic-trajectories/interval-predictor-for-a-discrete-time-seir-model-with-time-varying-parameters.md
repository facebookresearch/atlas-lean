# Interval predictor for a discrete-time SEIR model with time-varying parameters

**Bounding lemma.** For $A \in \mathbb R^{m \times n}$ write $A^+ = \max\{0, A\}$ and $A^- = A^+ - A$ elementwise. If $\underline x \le x \le \overline x$ in $\mathbb R^n$, then for a constant matrix $A$

$$A^+ \underline x - A^- \overline x \le A x \le A^+ \overline x - A^- \underline x .$$

In the scalar positive case $x_{t+1} = a_t x_t + d_t$ with $x_t, a_t \ge 0$, $x_0 \in [\underline x_0, \overline x_0]$, $a_t \in [\underline a_t, \overline a_t]$, $d_t \in [\underline d_t, \overline d_t]$, the recursions $\underline x_{t+1} = \underline a_t \underline x_t + \underline d_t$ and $\overline x_{t+1} = \overline a_t \overline x_t + \overline d_t$ give $\underline x_t \le x_t \le \overline x_t$ for all $t$. The bounds stay bounded if $\overline a_t \le 1 - \epsilon$.

**Model.** Consider the daily SEIR model with deaths on a population of size $N = S + E + I + R + D$,

$$\begin{aligned}
S_{t+1} &= S_t - b\,\frac{p_{t-\tau_p} I_t + r_{t-\tau_r} E_t}{N}\, S_t, &
E_{t+1} &= \bigl(1 - (1+\kappa)\sigma\bigr) E_t + b\,\frac{p_{t-\tau_p} I_t + r_{t-\tau_r} E_t}{N}\, S_t, \\
I_{t+1} &= (1 - \gamma - \mu) I_t + \sigma E_t, &
R_{t+1} &= R_t + \gamma I_t + \kappa\sigma E_t, \qquad D_{t+1} = D_t + \mu I_t,
\end{aligned}$$

where $b$ is the transmission rate, $p_t \le r_t$ are daily contact numbers of infectious and exposed individuals (lowered by confinement) acting with delays $\tau_p, \tau_r$, $\sigma$ and $\kappa\sigma$ are the rates at which the exposed become symptomatic or recover without symptoms, and $\gamma, \mu$ are recovery and death rates. Suppose that $\sigma, \gamma, \mu, b, p_t, r_t$ may vary in time within known nonnegative intervals, and that the initial states lie in known intervals.

**Theorem.** Define the lower predictor

$$\begin{aligned}
\underline S_{t+1} &= \Bigl(1 - \overline b\,\tfrac{\overline p_{t-\tau_p} \overline I_t + \overline r_{t-\tau_r} \overline E_t}{N}\Bigr)\underline S_t, &
\underline E_{t+1} &= \Bigl(1 - (1+\kappa)\overline\sigma + \underline b\,\tfrac{\underline r_{t-\tau_r}}{N}\underline S_t\Bigr)\underline E_t + \underline p_{t-\tau_p}\underline b\,\tfrac{\underline I_t \underline S_t}{N}, \\
\underline I_{t+1} &= (1 - \overline\gamma - \overline\mu)\underline I_t + \underline\sigma\, \underline E_t, &
\underline R_{t+1} &= \underline R_t + \underline\gamma\, \underline I_t + \kappa\underline\sigma\, \underline E_t, \qquad \underline D_{t+1} = \underline D_t + \underline\mu\, \underline I_t,
\end{aligned}$$

and the upper predictor by exchanging all lower and upper bounds, with the right-hand sides of $\overline E, \overline I, \overline R, \overline D$ capped at $N$. If

$$2\,\overline b\, \sup_t \overline r_t \le 1, \qquad \overline\sigma \le \frac{1}{1+\kappa}, \qquad \overline\gamma + \overline\mu \le 1, \tag{10}$$

then for all $t \in \mathbb N$ every state lies within its predicted interval, e.g. $S_t \in [\underline S_t, \overline S_t]$, and all predicted bounds lie in $[0, N]$.

## Expansion

The lemma follows by splitting $A$ into its positive and negative parts and bounding each term monotonically. For the scalar recursion, the errors $\underline e_t = x_t - \underline x_t$ and $\overline e_t = \overline x_t - x_t$ obey recursions with nonnegative inputs, so nonnegativity propagates by induction. For the SEIR model, each product of an uncertain rate with a nonnegative state is bounded the same way. Conditions (10) keep every coefficient multiplying a state in the predictor nonnegative. In particular the infection factor in $\underline S_{t+1}$ is at most $1$, since $p \le r$ and $\overline I_t + \overline E_t \le 2N$. Hence the order relations $0 \le \underline X_t \le X_t \le \overline X_t$ pass from $t$ to $t+1$. Boundedness of the lower predictor follows from the nonincreasing linear Lyapunov function $\underline V_t = \underline S_t + \underline E_t + \underline I_t + \underline R_t + \underline D_t$, and the caps at $N$ bound the upper one. Without the caps the upper bounds can grow without limit, because the interval widths enter the upper recursion with positive sign. Fitted to COVID-19 counts in several countries, with parameters taken as nominal values $\pm\delta\%$, the intervals enclosed later observations used for verification.

## Sources

- D. Efimov, R. Ushirobira, "On an interval prediction of COVID-19 development based on a SEIR epidemic model", *Annual Reviews in Control* (2021), Section 2 (model (1a)–(1e)), Section 5.1 (Lemma 1, Eqs. (5)–(6), scalar predictor) and Section 5.2 (Eqs. (7)–(10), Theorem 1 with proof), <https://doi.org/10.1016/j.arcontrol.2021.01.006> (PMC7891093).
