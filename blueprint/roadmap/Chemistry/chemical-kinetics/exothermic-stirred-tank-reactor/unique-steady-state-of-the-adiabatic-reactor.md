# Unique steady state of the adiabatic reactor when $\beta b < 4$

For the dimensionless adiabatic reactor with $a \in \mathbb{R}$, $b > 0$ and $\beta \ge 0$, every steady temperature
lies in $[1, 1 + \beta]$. If $\beta b < 4$, the reactor has exactly one steady state; for $\beta = 0$ its temperature
is $T = 1$.

A steady temperature satisfies $T = 1 + \beta\,k(T)/(1 + k(T))$ with $0 < k/(1 + k) < 1$, which gives the interval.
For $T \ge 1$,

$$\frac{d}{dT}\,\frac{k(T)}{1 + k(T)} = \frac{b}{T^2}\,\frac{k(T)}{(1 + k(T))^2} \le \frac{b}{4},$$

so $g_\beta'(T) \le \beta b/4 - 1 < 0$ when $\beta b < 4$. Then $g_\beta$ is strictly decreasing on $[1, \infty)$, with
$g_\beta(1) \ge 0$ and $g_\beta(1 + \beta) \le 0$, so it has exactly one root there by the intermediate value theorem.
For example $a = 0$, $b = 1$, $\beta = 1$ has a steady temperature strictly between $1$ and $2$.

## Depends on

- [Steady states and an energy invariant of the dimensionless adiabatic reactor](steady-states-of-the-dimensionless-adiabatic-reactor.md), for the steady-state equation

## Proof depends on

## Sources

- J. B. Rawlings and J. G. Ekerdt, *Chemical Reactor Analysis and Design Fundamentals*, 2nd edition, paperback, seventh printing (November 2026), Nob Hill Publishing; freely distributed by the authors at <https://sites.engineering.ucsb.edu/~jbraw/chemreacfun/> (page numbers below are the printed ones): Section 6.3.1 (pp. 288–289), which shows that the adiabatic reactor can have up to three steady states; the sufficient condition $\beta b < 4$ is derived above.
