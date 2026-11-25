# Output variance of a quadratic calibration under a finite scenario law

Let $\Omega$ be a finite set of scenarios with weights $p : \Omega \to \mathbb{R}$ and voltages $V : \Omega \to \mathbb{R}$, and let $a, b \in \mathbb{R}$. Assume $p_\omega \ge 0$ for all $\omega$, $\sum_\omega p_\omega = 1$, and $V_\omega \in [a, b]$ for all $\omega$. Let $v_0 \in [a, b]$ and $c_0, c_1, c_2 \in \mathbb{R}$, and set

$$f(v) = c_0 + c_1 v + c_2 v^2, \qquad f'(v_0) = c_1 + 2 c_2 v_0.$$

With $\operatorname{E}[X] = \sum_\omega p_\omega X_\omega$, $\operatorname{Var} X = \operatorname{E}[(X - \operatorname{E}X)^2]$ and $\operatorname{Cov}(X, Y) = \operatorname{E}[(X - \operatorname{E}X)(Y - \operatorname{E}Y)]$,

$$\operatorname{Var} f(V) = f'(v_0)^2 \operatorname{Var} V + c_2^2 \operatorname{Var}\big((V - v_0)^2\big) + 2\,f'(v_0)\,c_2\,\operatorname{Cov}\big(V, (V - v_0)^2\big),$$

and for every scenario $\omega$ the Taylor remainder satisfies

$$\big|c_2 (V_\omega - v_0)^2\big| \le \frac{2|c_2|}{2}\,(V_\omega - v_0)^2.$$
