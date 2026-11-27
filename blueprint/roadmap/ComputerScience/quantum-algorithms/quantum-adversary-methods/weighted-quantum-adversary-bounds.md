# Weighted adversary bounds (Ambainis, Zhang)

Let $f$ be a function on $D \subseteq \{0,1\}^N$ with finite output set, and let $w$ be a nonnegative weight scheme, not identically zero, on pairs $(x, y)$ with $f(x) \ne f(y)$ and $w'$ nonnegative weights on triples $(x, y, i)$ with $x_i \ne y_i$ satisfying $w'(x,y,i)\, w'(y,x,i) \ge w(x,y)^2$ whenever $f(x) \ne f(y)$ and $x_i \ne y_i$ (so the loads in the minimum below are positive). With loads $v_x = \sum_y w(x,y)$ and $v_{x,i} = \sum_y w'(x, y, i)$, every algorithm computing $f$ with error $\varepsilon$ uses

$$T \ge \frac{1 - 2\sqrt{\varepsilon(1-\varepsilon)}}{2} \min_{\substack{x, y, i\\ w(x,y) > 0,\ x_i \ne y_i}} \sqrt{\frac{v_x\, v_y}{v_{x,i}\, v_{y,i}}}$$

queries (Zhang's strong weighted method, which contains Ambainis's weighted method). The unweighted Ambainis bound is the special case of $0/1$ weights with $w' = w$.

## Proof sketch

Run the weighted-progress argument with the weights $w$; the per-query decrease is bounded by Cauchy–Schwarz using the split $w(x,y) \le \sqrt{w'(x,y,i) w'(y,x,i)}$, which localizes the loss at each index to the loads $v_{x,i}$ and $v_{y,i}$.

## Depends on

- [Quantum query algorithms with phase and value oracles](quantum-query-algorithms.md)
- [Ambainis adversary bound](../quantum-query-lower-bounds/ambainis-adversary-bound.md)

## Sources

- A. Ambainis, "Polynomial Degree vs. Quantum Query Complexity", Journal of Computer and System Sciences 72(2), 2006.
- S. Zhang, "On the Power of Ambainis's Lower Bounds", Theoretical Computer Science 339(2-3), 2005, Theorem 11 and its proof (which gives the constant $(1-2\sqrt{\varepsilon(1-\varepsilon)})/2$).
