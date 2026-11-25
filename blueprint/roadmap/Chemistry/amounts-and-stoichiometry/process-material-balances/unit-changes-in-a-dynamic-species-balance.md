# Unit changes in a dynamic species balance

Let $I \subseteq \mathbb{R}$ be a time set (for example, an interval), and let
$n : I \to \mathbb{R}^S$ hold the species amounts. For every $t \in I$, suppose each species
coordinate has the indicated derivative within $I$:

$$n'(t) = F_{\mathrm{in}}(t) - F_{\mathrm{out}}(t) + g(t).$$

Here $F_{\mathrm{in}}, F_{\mathrm{out}}, g$ are the inflow, outflow, and generation rates in
amount per unit time. Let $\alpha > 0$ convert the amount unit (new amount $= \alpha \times$ old)
and $\tau > 0$ convert the time unit (old time $= \tau \times$ new time). Put
$\tilde n(s) = \alpha\,n(\tau s)$ and $\tilde F(s) = \alpha\tau\,F(\tau s)$ for each of the three rates.
Then each transformed species coordinate has the indicated derivative within
$\{s \mid \tau s \in I\}$ at every $s$ in that set:

$$\tilde n'(s) = \tilde F_{\mathrm{in}}(s) - \tilde F_{\mathrm{out}}(s) + \tilde g(s).$$

Conversely, the inverse factors recover the balance within $I$. Every rate, being an amount per
time, scales by the same factor $\alpha\tau$, while the accumulation picks up the factor $\tau$
from the chain rule; mass balances behave in the same way under a change of mass unit. Converting
between a wet and a dry moisture basis changes the composition basis and is not a unit change of
this kind, and affine temperature scales such as Celsius are not admissible in laws stated for
absolute temperature.

## Sources

- J. B. Rawlings and J. G. Ekerdt, *Chemical Reactor Analysis and Design Fundamentals*, 2nd edition, paperback, seventh printing (November 2026), Nob Hill Publishing; freely distributed by the authors at <https://sites.engineering.ucsb.edu/~jbraw/chemreacfun/> (page numbers below are the printed ones): Section 4.3, Equation 4.36, the species balance of a flow reactor in molar flow rates (p. 127).
