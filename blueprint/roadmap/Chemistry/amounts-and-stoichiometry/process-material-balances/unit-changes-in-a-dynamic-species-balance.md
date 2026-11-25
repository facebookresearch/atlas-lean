# Unit changes in a dynamic species balance

Let $I$ be an interval and let $n : I \to \mathbb{R}^S$ be differentiable with

$$n'(t) = F_{\mathrm{in}}(t) - F_{\mathrm{out}}(t) + g(t) \qquad (t \in I),$$

where $n$ holds the species amounts and $F_{\mathrm{in}}, F_{\mathrm{out}}, g$ are the inflow, outflow and generation rates in
amount per unit time. Let $\alpha > 0$ convert the amount unit (new amount $= \alpha \times$ old) and $\tau > 0$ the time unit
(old time $= \tau \times$ new time). Put $\tilde n(s) = \alpha\,n(\tau s)$ and $\tilde F(s) = \alpha\tau\,F(\tau s)$ for each of
the three rates. Then

$$\tilde n'(s) = \tilde F_{\mathrm{in}}(s) - \tilde F_{\mathrm{out}}(s) + \tilde g(s)$$

for every $s$ with $\tau s \in I$, and conversely, by the inverse factors. Every rate, being an amount per time, scales by the same
factor $\alpha\tau$, while the accumulation picks up the factor $\tau$ from the chain rule; mass balances behave in the same way
under a change of mass unit. Converting between a wet and a dry moisture basis changes the composition basis and is not a unit
change of this kind, and affine temperature scales such as Celsius are not admissible in laws stated for absolute temperature.

## Depends on

## Proof depends on

## Sources

- J. B. Rawlings and J. G. Ekerdt, *Chemical Reactor Analysis and Design Fundamentals*, 2nd edition, paperback, seventh printing (November 2026), Nob Hill Publishing; freely distributed by the authors at <https://sites.engineering.ucsb.edu/~jbraw/chemreacfun/> (page numbers below are the printed ones): Section 4.3, Equation 4.36, the species balance of a flow reactor in molar flow rates (p. 127).
