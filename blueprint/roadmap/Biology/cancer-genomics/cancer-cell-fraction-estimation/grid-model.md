# Grid model for the cancer cell fraction

Grid points $c_1, \dots, c_m$, prior weights $\pi_1, \dots, \pi_m$, purity $\alpha$ and copy number $q$ form a grid model if

- $0 < \alpha \le 1$ and $q > 0$;
- $0 \le c_k \le q$ and $c_k \le 1$ for every $k$;
- $\pi_k \ge 0$ for every $k$;
- some $k$ has $\pi_k > 0$ and $0 < f(c_k) < 1$, where $f(c) = \alpha c / (\alpha q + 2(1 - \alpha))$.
