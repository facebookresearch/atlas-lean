# Offline optima under a simulation

Let $Y$ simulate $X$, translating every feasible trace $\tau$ of $X$ on a legal input into a feasible
trace of $Y$ on the same input of cost at most $d\,\mathrm{cost}_X(\tau) + q$. Then for every legal
input $\sigma$ of $X$, the offline optima satisfy $\mathrm{OPT}_Y(\sigma) \le d\,\mathrm{OPT}_X(\sigma) + q$
in $[0, \infty]$.
