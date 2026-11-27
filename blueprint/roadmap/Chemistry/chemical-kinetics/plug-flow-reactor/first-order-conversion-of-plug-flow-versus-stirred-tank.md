# First-order conversion: plug flow beats a stirred tank of the same residence time

Consider the irreversible first-order reaction $A \to B$ with rate constant $k \ge 0$ in a liquid of
constant density, fed at concentration $c_{Af} > 0$ with residence time $\tau = V_R / Q_f > 0$. The
steady conversions $x = 1 - c_A / c_{Af}$ of a plug-flow reactor and of a continuous stirred-tank
reactor are

$$x_{\mathrm{PFR}} = 1 - e^{-k\tau}, \qquad x_{\mathrm{CSTR}} = \frac{k\tau}{1 + k\tau} .$$

For every Damköhler number $\mathrm{Da} = k\tau \ge 0$,

$$1 - e^{-\mathrm{Da}} \ \ge\ \frac{\mathrm{Da}}{1 + \mathrm{Da}},$$

with equality if and only if $\mathrm{Da} = 0$. So at equal residence time the plug-flow reactor
achieves at least the conversion of the stirred tank, strictly more whenever $k\tau > 0$.

The plug-flow conversion follows from the
[plug-flow/batch correspondence](plug-flow-reactor-as-a-batch-reactor-in-residence-time.md) and the
[uniqueness of the first-order solution](../rate-laws/first-order-sol-unique.md); the stirred-tank conversion is
$1 - c_{\mathrm{ss}}/c_{Af}$ for the
[steady stirred-tank concentration](../continuous-stirred-tank-reactor/steady.md). The inequality is equivalent to
$e^{\mathrm{Da}} \ge 1 + \mathrm{Da}$, strict for $\mathrm{Da} \ne 0$.

The ordering is a property of these kinetics, not of the two reactors. For the order $-1$ rate
$r(c) = k/c$ with $c_{Af} = 1$ and $k\tau = 1/4$, the plug-flow balance $dc/d\tau = -k/c$ gives the
outlet $c = 1/\sqrt{2}$, while the stirred-tank balance $c_{Af} - c = \tau\, r(c)$ gives
$c = 1/2$: the stirred tank converts more.

## Depends on

## Proof depends on

- [A constant-flow plug-flow reactor is a batch reactor in residence time](plug-flow-reactor-as-a-batch-reactor-in-residence-time.md), for the plug-flow outlet
- [Uniqueness of the first-order solution](../rate-laws/first-order-sol-unique.md), for the batch state $c_{Af} e^{-k\tau}$
- [Steady concentration of a continuous stirred-tank reactor](../continuous-stirred-tank-reactor/steady.md), for $c_{\mathrm{ss}} = c_{Af}/(1 + k\tau)$

## Sources

- J. B. Rawlings and J. G. Ekerdt, *Chemical Reactor Analysis and Design Fundamentals*, 2nd edition, paperback, seventh printing (November 2026), Nob Hill Publishing; freely distributed by the authors at <https://sites.engineering.ucsb.edu/~jbraw/chemreacfun/> (page numbers below are the printed ones): Section 4.7, "Some PFR-CSTR Comparisons" (pp. 156–159): the plug-flow reactor is more
  efficient for irreversible kinetics of positive order and the stirred tank for negative order
  (Figures 4.24 and 4.25, pp. 158–159); Example 4.8 (p. 159) states
  $x_{\mathrm{PFR}} = 1 - \exp(-k\tau)$ and $x_{\mathrm{CSTR}} = k\tau/(1 + k\tau)$ for
  first-order kinetics.
