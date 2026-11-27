# A constant-flow plug-flow reactor is a batch reactor in residence time

Let a plug-flow reactor of volume $V_R > 0$ carry a steady flow with constant volumetric flowrate
$Q > 0$, and let $R : \mathbb{R}^n \to \mathbb{R}^n$ give the production rates of $n$ species as a
function of their concentrations. Say that $c : [0, V_R] \to \mathbb{R}^n$ solves the steady
plug-flow balance if $c(0) = c_f$ and, at every $V \in [0, V_R]$, $c$ has derivative $c'(V)$ within
$[0, V_R]$ (one-sided at the two ends) with

$$Q \, c'(V) = R(c(V)) .$$

Then $c$ solves the steady plug-flow balance if and only if $C(\tau) = c(Q \tau)$ solves the
constant-volume batch equation on $[0, V_R / Q]$, in the same within-interval sense:

$$C(0) = c_f, \qquad C'(\tau) = R(C(\tau)) .$$

In particular the effluent concentration $c(V_R)$ is the batch state at time $\tau = V_R / Q$, and
the plug-flow balance has at most one solution whenever this batch initial-value problem has at most
one. For $V_R = 0$ there is no reactor volume and the effluent is the feed, $c(0) = c_f$.

The proof is the chain rule for the linear change of variables $V = Q\tau$, which maps
$[0, V_R/Q]$ onto $[0, V_R]$. The same argument works in any real normed vector space.
In that formulation the plug-flow derivative is $Q^{-1}R(c(V))$, and uniqueness means that
solutions agree on the physical interval. At zero volume the within-singleton derivative
imposes no restriction, so the feed condition is the entire balance.

## Sources

- J. B. Rawlings and J. G. Ekerdt, *Chemical Reactor Analysis and Design Fundamentals*, 2nd edition, paperback, seventh printing (November 2026), Nob Hill Publishing; freely distributed by the authors at <https://sites.engineering.ucsb.edu/~jbraw/chemreacfun/> (page numbers below are the printed ones): Section 4.6, Equation 4.66 (steady plug-flow balance $d(c_j Q)/dV = R_j$, p. 145) and
  Equation 4.74 with the remark after it ($dc_j/d\tau = R_j$ for constant flowrate with
  $\tau = V/Q$, identical to the constant-volume batch reactor of Equation 4.6, p. 147).
