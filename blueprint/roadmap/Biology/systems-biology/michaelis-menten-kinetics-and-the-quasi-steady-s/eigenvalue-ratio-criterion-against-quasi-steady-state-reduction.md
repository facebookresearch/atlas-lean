# Eigenvalue-ratio criterion against quasi-steady-state reduction

**Setting.** For the irreversible Michaelis–Menten mechanism $E + S \rightleftharpoons C \to E + P$ with rate constants $k_1, k_{-1}, k_2$ and total enzyme $e_0$, the reduced $(s, c)$ system has the stationary point $(0,0)$, where the Jacobian has real negative eigenvalues $-\lambda_1, -\lambda_2$ with $0 < \lambda_1 \le \lambda_2$ and characteristic polynomial $\tau^2 + \sigma_1\tau + \sigma_2$,

$$\sigma_1 = k_{-1} + k_2 + k_1e_0, \qquad \sigma_2 = k_1k_2e_0 .$$

A quasi-steady-state (QSS) reduction of any kind requires timescale separation near the stationary point, i.e. a small ratio $\lambda_1/\lambda_2$.

**Lemma.** For $0 < \delta \le 1$ and a $2\times2$ matrix with real eigenvalues of equal sign,

$$\frac{\lambda_1}{\lambda_2} \ge \delta \iff \frac{\sigma_2}{\sigma_1^2 - 2\sigma_2} \ge \frac{\delta}{1+\delta^2},$$

since $\lambda_1/\lambda_2 + \lambda_2/\lambda_1 = (\sigma_1^2 - 2\sigma_2)/\sigma_2$ and $x \mapsto x + 1/x$ decreases on $(0,1]$.

**Proposition (local anti-QSS condition).** For $0 < \delta \le 1$,

$$\frac{\lambda_1}{\lambda_2} \ge \delta \iff k_1k_2e_0 \ge \frac{\delta}{1+\delta^2}\Big((k_{-1} + k_2 + k_1e_0)^2 - 2k_1k_2e_0\Big),$$

and the reverse inequalities are equivalent as well. The ratio is maximal ($\lambda_1 = \lambda_2$) if and only if $k_1e_0 = k_2$ and $k_{-1} = 0$. Informally, with $K_M = (k_{-1}+k_2)/k_1$ and $K = k_2/k_1$,

$$\frac{\lambda_1}{\lambda_2} \ll 1 \iff \frac{Ke_0}{(K_M + e_0)^2} \ll 1 ;$$

when this quantity is not small, no quasi-steady-state reduction (standard, total, or any other) can be valid, locally and hence globally.

## Depends on

- [Michaelis constant](michaelis-constant.md)

## Proof sketch

Any QSS reduction is a singular-perturbation statement: trajectories collapse quickly onto a slow invariant curve, which near the stationary point is the slow eigendirection. If the two eigenvalues are comparable there is no slow manifold to collapse onto, so the reduction fails irrespective of how it is formulated. Expressing the eigenvalue ratio through trace and determinant avoids square roots and gives an explicit polynomial inequality in the rate constants, complementing sufficient conditions for validity such as $e_0/(K_M + s_0) \ll 1$.

## Sources

- Justin Eilertsen, Santiago Schnell and Sebastian Walcher, "On the anti-quasi-steady-state conditions of enzyme kinetics", *Mathematical Biosciences* 350 (2022), 108870, <https://doi.org/10.1016/j.mbs.2022.108870>. Preprint version: arXiv:2112.04098 (2021), Lemma 1, Proposition 1 and Remark 2 (Section 3), <https://doi.org/10.48550/arXiv.2112.04098>.
