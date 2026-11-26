# Recursive least-squares estimates

For regressors $\varphi_k$, observations $y_{k+1}$, an initial estimate $\theta_0$ and an initial matrix $P_0$,
the recursive least-squares estimates $(\theta_t, P_t)$ are obtained by applying [one step of recursive least squares](rls-step.md) with
$(\varphi_k, y_{k+1})$ for $k = 0, \dots, t - 1$. The observation $y_{k+1}$ follows the regressor $\varphi_k$, as in
the model $y_{k+1} = \varphi_k^\top \theta + w_{k+1}$, so $\theta_t$ uses the data $(\varphi_k, y_{k+1})_{k < t}$.
