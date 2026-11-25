# Residence-time distributions of the ideal stirred tank and plug-flow reactor

Let a constant volumetric flowrate $Q_f > 0$ pass through a vessel whose volume swept by the flow is
$V_R > 0$, and put $\tau = V_R / Q_f$.

- **Stirred tank.** If the swept volume is well mixed, the residence time is exponentially
  distributed with rate $1/\tau$: its distribution has density $\tau^{-1} e^{-\theta/\tau}$ for
  $\theta \ge 0$ and $0$ for $\theta < 0$.
- **Plug flow.** If the swept volume is in plug flow, every feed element spends exactly the time
  $\tau$: the residence time has the point mass at $\tau$ as its distribution, with the
  right-continuous distribution function $F(\theta) = 0$ for $\theta < \tau$ and $F(\theta) = 1$
  for $\theta \ge \tau$. It has no Lebesgue density.

Both distributions have mean $\tau = V_R / Q_f$.

Only the swept volume enters. A part of the vessel disconnected from the flow (a dead volume) does not
change these distributions: a stirred tank of total volume $5$ whose swept volume is $2$, at
$Q_f = 1$, has mean residence time $2$, not $5$.

The stirred-tank distribution is the [tracer step response](step-response-of-a-stirred-tank-is-the-exponential-distribution.md); its mean is the
[mean of the exponential distribution](../../../Probability/distributions/continuous/exponential-distribution/integral-id-exp-measure.md) at rate $1/\tau$. The plug-flow
distribution follows from the tracer front, which moves at the flow speed and reaches the outlet at
time $V_R/Q_f$.

## Depends on

## Proof depends on

- [The step response of a stirred tank is the exponential distribution](step-response-of-a-stirred-tank-is-the-exponential-distribution.md), for the stirred-tank law
- [Mean of the exponential distribution](../../../Probability/distributions/continuous/exponential-distribution/integral-id-exp-measure.md), at rate $1/\tau$

## Sources

- J. B. Rawlings and J. G. Ekerdt, *Chemical Reactor Analysis and Design Fundamentals*, 2nd edition, paperback, seventh printing (November 2026), Nob Hill Publishing; freely distributed by the authors at <https://sites.engineering.ucsb.edu/~jbraw/chemreacfun/> (page numbers below are the printed ones): Section 8.2.3, Equation 8.10 and the computation of its mean (pp. 437–438); Section 8.2.4,
  the moving tracer front, $p(\theta) = \delta(\theta - V_R/Q_f)$ and Equation 8.15 (pp. 438–440).
  The book writes the plug-flow distribution function with a Heaviside function defined only away
  from $0$ (p. 439); the value $1$ at the atom is the right-continuous convention used above.
