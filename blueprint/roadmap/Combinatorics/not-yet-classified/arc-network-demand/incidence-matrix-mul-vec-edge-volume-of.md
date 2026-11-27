# Origin-destination node balance

Let each route $p$ be a valid walk from its origin to its destination, and let real path flows $f$ meet the demand table: $\sum_{p : (\text{orig}(p), \text{dest}(p)) = w} f_p = r(w)$ for every pair $w$. With edge volume $x_e = \sum_p f_p \cdot (\text{number of uses of } e \text{ by } p)$, inflow minus outflow of $x$ at every node $v$ equals $\sum_o r(o, v) - \sum_d r(v, d)$; intrazonal demand $r(v, v)$ cancels.
