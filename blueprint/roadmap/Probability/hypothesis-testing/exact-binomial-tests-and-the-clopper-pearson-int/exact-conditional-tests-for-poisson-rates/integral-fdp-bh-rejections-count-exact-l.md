# False discovery rate of exact count tests under arbitrary dependence

Test $m$ hypotheses with counts $X_g, Y_g$ on a probability space (measurable, exposures $s_1, s_2$ with $s_1 + s_2 > 0$) by their exact conditional p-values $p_g$. Suppose every null index $g \in H_0$ has independent $X_g \sim \mathrm{Poisson}(s_1r_g)$ and $Y_g \sim \mathrm{Poisson}(s_2r_g)$, and let $0 \le q \le 1$. Then the Benjamini–Hochberg procedure at level $q/H_m$, $H_m = \sum_{k=1}^m1/k$, has false discovery rate at most $q|H_0|/m$, whatever the dependence between hypotheses.
