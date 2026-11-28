# False discovery rate of independent exact count tests

Test $m$ hypotheses with counts $X_g, Y_g$ on a probability space (measurable, exposures $s_1, s_2$ with $s_1 + s_2 > 0$) by their exact conditional p-values $p_g$. Suppose every null index $g \in H_0$ has independent $X_g \sim \mathrm{Poisson}(s_1r_g)$ and $Y_g \sim \mathrm{Poisson}(s_2r_g)$, and let $0 \le q \le 1$. If moreover the pairs $(X_g, Y_g)$ are mutually independent across $g$, the Benjamini–Hochberg procedure at level $q$ has false discovery rate at most $q|H_0|/m$.
