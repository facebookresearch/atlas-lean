# The step response of a stirred tank is the exponential distribution

Let a well-mixed tank of constant volume $V_R > 0$ and constant density carry a volumetric flowrate
$Q_f > 0$, and put $\tau = V_R / Q_f$. Suppose the tank initially holds no tracer and, from time $0$
on, the feed carries a conservative tracer (no reaction or loss) at constant concentration $c_f > 0$,
so that

$$\frac{dc}{dt} = \frac{Q_f}{V_R} (c_f - c), \qquad c(0) = 0 .$$

Then the effluent concentration is $c(t) = (1 - e^{-t/\tau})\, c_f$ for $t \ge 0$. The normalized
step response, extended by $0$ to negative times,

$$P(\theta) = \begin{cases} 0, & \theta < 0, \\ c(\theta)/c_f = 1 - e^{-\theta/\tau}, & \theta \ge 0, \end{cases}$$

is the cumulative distribution function of the exponential distribution with rate $1/\tau$. Take the
representative of its density given by $p(\theta) = \tau^{-1} e^{-\theta/\tau}$ for $\theta \ge 0$ and
$p(\theta) = 0$ for $\theta < 0$. For $\theta > 0$, $p(\theta) = P'(\theta)$. The chosen value $p(0)=1/\tau$
is the right derivative at zero, not an ordinary derivative: the left derivative there is zero. The
distribution is the residence-time distribution in this ideal model.

A positive first-order loss $k$ changes the inlet-normalized response. The concentration tends to
$Q_f c_f/(Q_f + k V_R) < c_f$, so the normalized response tends to $1/(1 + k\tau) < 1$ and cannot
be the CDF of a probability distribution.

Both responses are the [stirred-tank solution](../continuous-stirred-tank-reactor/solution.md) with inlet concentration $c_f$ and
initial concentration $0$, at rate constant $0$ and $k$ respectively. The endpoint and loss conclusions follow from these formulas.

## Sources

- J. B. Rawlings and J. G. Ekerdt, *Chemical Reactor Analysis and Design Fundamentals*, 2nd edition, paperback, seventh printing (November 2026), Nob Hill Publishing; freely distributed by the authors at <https://sites.engineering.ucsb.edu/~jbraw/chemreacfun/> (page numbers below are the printed ones): Section 8.2.3, Equation 8.8, its solution $c(t) = (1 - e^{-t/\tau}) c_f$ and
  $P(\theta) = 1 - e^{-\theta/\tau}$ (p. 435); the definition of $P$ as the probability that a feed
  molecule spends time $0$ to $\theta$ in the reactor (Section 8.2.1, p. 431).
