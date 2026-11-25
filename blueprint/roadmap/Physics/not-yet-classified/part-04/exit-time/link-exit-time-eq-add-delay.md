# Link exit time equals entry time plus virtual delay

Let $N_0 \ge 0$ be the number of vehicles on a link at time $0$, and $A$, $D : [0, \infty) \to [0, \infty)$ the cumulative arrival and departure counts. For an entry time $t \ge 0$, the exit time of the vehicle entering at $t$, $\inf\{s \ge t : D(s) \ge N_0 + A(t)\}$ (or $\infty$ if no such $s$), equals $t$ plus the network-calculus virtual delay $\inf\{\tau \ge 0 : N_0 + A(t) \le D(t + \tau)\}$, as an identity in $[0, \infty]$ with no further hypotheses. Both sides are $\infty$ exactly when $D$ never reaches $N_0 + A(t)$ at or after $t$.
