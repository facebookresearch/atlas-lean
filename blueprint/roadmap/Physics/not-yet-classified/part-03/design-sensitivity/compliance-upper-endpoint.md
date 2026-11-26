# Compliance at the upper endpoint of the design interval

Let $J(F, k) = F \cdot (F/k)$ be the compliance under end force $F$ at stiffness $k$. Let $F \in \mathbb{R} \setminus \{0\}$ and $0 < k_{\min} < k_{\max}$. Then:

- $k \mapsto J(F, k)$ has derivative $-F^2/k_{\max}^2$ at $k_{\max}$ within $[k_{\min}, k_{\max}]$;
- $-F^2/k_{\max}^2 < 0$;
- for every feasible direction $d$ at $k_{\max}$ (a $d$ such that for some $\varepsilon > 0$, $k_{\max} + t d \in [k_{\min}, k_{\max}]$ for all $t \in (0, \varepsilon]$), $-\frac{F^2}{k_{\max}^2} d \ge 0$, and $-\frac{F^2}{k_{\max}^2} d = 0$ implies $d = 0$.
