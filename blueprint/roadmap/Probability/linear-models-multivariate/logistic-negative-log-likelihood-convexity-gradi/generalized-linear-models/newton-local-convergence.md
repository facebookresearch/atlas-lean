# Local convergence of the Newton–Raphson method

Let $E$ be a real normed space, $U : E \to E$ with $U(b) = 0$, and suppose $U$ has derivative $H(x)$ at every $x \in B(b, r)$ with $\|H(x) - H(y)\| \le L\|x - y\|$ there. Let $H(b)$ have a left inverse of norm at most $M$, and let $\varepsilon \le r$ with $2ML\varepsilon \le 1$. Let $T$ take Newton steps on $B(b, \varepsilon)$: $H(x)(T(x) - x) = -U(x)$. Then from every $\beta_0 \in B(b, \varepsilon)$ the iterates $\beta_n = T^n(\beta_0)$ stay in $B(b, \varepsilon)$, satisfy $\|\beta_{n+1} - b\| \le ML\|\beta_n - b\|^2$, $\|\beta_{n+1} - b\| \le \frac12\|\beta_n - b\|$ and $\|\beta_n - b\| \le 2^{-n}\|\beta_0 - b\|$, and converge to $b$.

## Sources

- J. E. Dennis and R. B. Schnabel, *Numerical Methods for Unconstrained Optimization and Nonlinear Equations*, Prentice-Hall (1983), Theorem 5.2.1.
