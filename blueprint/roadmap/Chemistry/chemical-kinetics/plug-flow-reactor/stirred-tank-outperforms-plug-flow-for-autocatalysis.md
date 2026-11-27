# A stirred tank can outperform a plug-flow reactor for autocatalytic kinetics

Consider the isothermal, constant-density reaction $A + B \to 2B$ with rate $k\,c_A c_B$, rate constant $k = 1$, feed
concentrations $c_{Af} = 99/100$ and $c_{Bf} = 1/100$, and residence time $\tau = 1$, in consistent units.

- In a plug-flow reactor, $c_A + c_B = 1$ and $dc_A/d\tau = -c_A(1 - c_A)$, so the outlet concentration is
  $c_A = 99/(99 + e)$ and the conversion is $1 - c_A/c_{Af} = (e - 1)/(e + 99) < 0.017$.
- In a stirred tank, the steady balance $c_{Af} - c_A = \tau\,k\,c_A c_B$ with $c_B = c_{Bf} + c_{Af} - c_A$ reads
  $c_A^2 - 2c_A + 99/100 = 0$, whose only root in $[0, c_{Af}]$ is $c_A = 9/10$; the conversion is $1/11 > 0.09$.

So the stirred tank reaches the higher conversion at the same residence time, whereas for irreversible first-order
kinetics the plug-flow reactor always does: the first-order ordering does not extend to autocatalytic kinetics.

## Depends on

## Proof depends on

- [A constant-flow plug-flow reactor is a batch reactor in residence time](plug-flow-reactor-as-a-batch-reactor-in-residence-time.md), for the plug-flow outlet

## Sources

- J. B. Rawlings and J. G. Ekerdt, *Chemical Reactor Analysis and Design Fundamentals*, 2nd edition, paperback, seventh printing (November 2026), Nob Hill Publishing; freely distributed by the authors at <https://sites.engineering.ucsb.edu/~jbraw/chemreacfun/> (page numbers below are the printed ones): Section 4.3, Equation 4.40 (steady constant-density stirred tank, p. 128); Section 4.7, the comparisons of plug-flow and stirred-tank reactors for $n$th-order kinetics (pp. 156–160). The autocatalytic instance and its numbers are computed above.
