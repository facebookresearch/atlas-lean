# Omitted-variable formula for any short least-squares fit

Let $x, z, y$ be finite real samples with $S_{xx} = \sum_i(x_i - \bar x)^2 \ne 0$, write $\hat b(x, w) = S_{xw}/S_{xx}$ for the least-squares slope of $w$ on $x$, and let $\theta = (\theta_0, \theta_1, \theta_2)$ solve the normal equations $L^\top L\theta = L^\top y$ of the long regression of $y$ on $(1, x, z)$. If $\varphi = (\varphi_0, \varphi_1)$ solves the normal equations of the short regression of $y$ on $(1, x)$, then $\varphi_1 = \theta_1 + \theta_2\,\hat b(x, z)$.
