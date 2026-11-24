# For k ≥ kmin > 0 the residual bounds state and compliance errors

For $k_{\min} > 0$, a stiffness $k \ge k_{\min}$, an end force $F$ and a trial tip displacement $u$,
the residual $k u - F$ of the equilibrium $k\, u_{\mathrm{tip}} = F$ bounds the error of the state
$u_{\mathrm{tip}} = F / k$ and the error of the compliance:

$$
\left| \frac{F}{k} - u \right| \le \frac{|k u - F|}{k_{\min}}, \qquad
|J(F, k) - F u| \le \frac{|F|\, |k u - F|}{k_{\min}},
$$

with $J(F, k) = F^2 / k$ the [compliance](compliance.md) and $F u$ the load work of the trial
displacement. The factor $1 / k_{\min}$ is the stability constant.
