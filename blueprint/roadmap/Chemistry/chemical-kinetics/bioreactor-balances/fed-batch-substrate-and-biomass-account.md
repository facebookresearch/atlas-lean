# Fed-batch substrate and biomass account

A fed-batch bioreactor has no outflow, and its biomass suffers no death or maintenance. Let $I$ be an interval of times
containing $0$. The reactor is fed with medium of substrate concentration $S_{\mathrm{in}} \ge 0$, free of biomass and
as dense as the broth, at a feed rate $F(t)$ that may vary in time, with $F(t) \ge 0$ at the times $t \ge 0$ of $I$;
$F$ need not be continuous. Biomass $X$ grows on the substrate $S$ with yield $Y > 0$ at the Monod rate
$\mu(S) = \mu_m S / (K_s + S)$ with $\mu_m, K_s > 0$. Let $V$, $S$ and $X$ satisfy on $I$, with one-sided derivatives at
an endpoint of $I$,

$$V' = F, \qquad S' = \frac{F}{V}(S_{\mathrm{in}} - S) - \frac{\mu(S)X}{Y}, \qquad X' = \mu(S)X - \frac{F}{V}X ,$$

with initial volume $V_0 = V(0) > 0$ and $S(0), X(0) \ge 0$. Then at every time $t \ge 0$ of $I$: $V(t) \ge V_0$; the
stocks $m_S = VS$ and $m_X = VX$ satisfy $(m_S + m_X/Y)'(t) = F(t)\, S_{\mathrm{in}}$; and $S(t) \ge 0$ and $X(t) \ge 0$.

The volume grows because $V' = F \ge 0$. Differentiating the stocks, the growth terms $\pm\mu(S) V X / Y$ cancel and only
the substrate fed remains. Nonnegativity needs only signs: while $S > -K_s$, $\mu(S) < \mu_m$, so $X' \ge \mu_m X$
wherever $X < 0$; and wherever $S < 0$ and $X \ge 0$, both terms of $S'$ are nonnegative. So neither $X$ nor $S$ can
cross below zero, and $S$ never approaches the pole $-K_s$ of $\mu$.

## Sources

- J. B. Rawlings and J. G. Ekerdt, *Chemical Reactor Analysis and Design Fundamentals*, 2nd edition, paperback, seventh printing (November 2026), Nob Hill Publishing; freely distributed by the authors at <https://sites.engineering.ucsb.edu/~jbraw/chemreacfun/> (page numbers below are the printed ones): Section 4.4, the semi-batch reactor, Equation 4.44 (p. 131), the species balance $(c_j V_R)' = Q_f c_{jf} + R_j V_R$, here with $Q_f = F$, feed concentrations $S_{\mathrm{in}}$ and $0$, and production rates $R_S = -\mu(S)X/Y$ and $R_X = \mu(S)X$; Section 4.5, Equation 4.48 (p. 132), the total mass balance, which for a broth of constant density equal to the feed's and no outflow gives $V_R' = Q_f$.
