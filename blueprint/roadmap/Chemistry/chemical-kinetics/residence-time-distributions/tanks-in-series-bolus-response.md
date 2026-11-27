# Bolus response of equal stirred tanks in series

Let $n$ be a positive integer and let $n$ well-mixed tanks of constant density, each of the same volume
$V_R/n$ with $V_R > 0$, be connected in series and carry a common volumetric flowrate $Q_f > 0$; put
$\tau = V_R / Q_f$ and $a = n/\tau$. At time $0$ the first tank holds an amount $m_0 > 0$ of a
conservative tracer, the other tanks hold none, and no further tracer enters. The tracer amounts are
functions $N_1, \dots, N_n$ on $\mathbb{R}$, with an ordinary derivative at every $t \ge 0$ (including
at zero), that satisfy, for $t \ge 0$,

$$N_1' = -a N_1, \qquad N_j' = a (N_{j-1} - N_j) \ (2 \le j \le n),$$

$$N_1(0) = m_0, \qquad N_j(0) = 0 \ (2 \le j \le n),$$

and this initial-value problem has the unique solution

$$N_j(t) = m_0 \, \frac{(a t)^{j-1}}{(j-1)!} \, e^{-a t}, \qquad t \ge 0,\ 1 \le j \le n .$$

The tracer leaves the last tank at rate $a N_n(t)$, so the effluent rate normalized by $m_0$, extended
by $0$ to negative times,

$$p(\theta) = \begin{cases} 0, & \theta < 0, \\
\left(\dfrac{n}{\tau}\right)^{n} \dfrac{\theta^{\,n-1}}{(n-1)!} \, e^{-n\theta/\tau}, & \theta \ge 0, \end{cases}$$

is a probability density on $\mathbb{R}$: the residence-time distribution of $n$ equal stirred tanks
in series of total residence time $\tau$. For $n = 1$ the density is $\tau^{-1} e^{-\theta/\tau}$
for $\theta \ge 0$. The formula fixes the total residence time $\tau$, so each tank has residence
time $\tau/n$; if instead each tank has a fixed residence time $\tau_1$, substitute $\tau = n \tau_1$.
For example, with $n = 2$, tank volume $V_R/2 = 1$, $Q_f = 1$ and $m_0 = 1$, the amounts on
$t \ge 0$ are $e^{-t}$ and $t e^{-t}$, and the normalized outflow there is $t e^{-t}$. Normalizing
by the bolus requires $m_0 > 0$.

The displayed functions satisfy the equations by differentiation. Uniqueness follows by induction on
$j$ from the [uniqueness of the first-order solution](../rate-laws/first-order-sol-unique.md): $N_1$ solves $N_1' = -a N_1$
with $N_1(0) = m_0$, so $N_1(t) = m_0 e^{-at}$; and if two solutions agree in tank $j - 1$, the
difference $h$ of their tank-$j$ amounts satisfies $h' = -a h$ with $h(0) = 0$, so $h = 0$ on
$t \ge 0$. The differential equations and uniqueness claim apply only for $t \ge 0$. The ordinary
derivative at zero still requires a compatible left-hand extension of each amount profile. Only the
normalized outflow is extended by zero. The density is nonnegative and measurable, and its integral
is one by the gamma density normalization. The Lean statement represents the positive tank count
as a natural number plus one and indexes the amounts starting at zero.

## Sources

- J. B. Rawlings and J. G. Ekerdt, *Chemical Reactor Analysis and Design Fundamentals*, 2nd edition, paperback, seventh printing (November 2026), Nob Hill Publishing; freely distributed by the authors at <https://sites.engineering.ucsb.edu/~jbraw/chemreacfun/> (page numbers below are the printed ones): Section 8.2.5, "CSTRs in Series", Figure 8.7 and Equation 8.16 (p. 440): $n$ equal tanks of
  volume $V_R/n$, each with residence time $\tau/n$, and the effluent after an impulse at time zero.
