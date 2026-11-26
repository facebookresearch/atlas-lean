# Certified bisection keeps the sign bracket

Bisection on a rational bracket $[l, u]$ with midpoint $m$ replaces it by $[l, m]$ on the decision true and by $[m, u]$ on the decision false; a run applies a list of decisions in order. Call the decisions sign-certified for $f$ when each decision true is taken only if $f(m) \ge 0$ and each decision false only if $f(m) \le 0$, at the current midpoint $m$. If the decisions are sign-certified and $f(l) \le 0 \le f(u)$, then the final bracket $[l', u']$ satisfies $f(l') \le 0 \le f(u')$.
