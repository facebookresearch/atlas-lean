# A bisection step keeps the bracket ordered and nested

Bisection on a rational bracket $[l, u]$ with midpoint $m$ replaces it by $[l, m]$ on the decision true and by $[m, u]$ on the decision false; a run applies a list of decisions in order. If $l \le u$, then after one step with either decision the new bracket $[l', u']$ satisfies $l \le l' \le u' \le u$.
