# Attenuation of correlation by measurement error

Let $X = T_x + E_x$ and $Y = T_y + E_y$ on a probability space with all four components square integrable, $\operatorname{Var}(T_x), \operatorname{Var}(T_y) > 0$, and $\operatorname{Cov}(T_x, E_x) = \operatorname{Cov}(T_y, E_y) = \operatorname{Cov}(E_x, E_y) = \operatorname{Cov}(T_x, E_y) = \operatorname{Cov}(E_x, T_y) = 0$. With reliabilities $\rho_X = \operatorname{Var}(T_x)/(\operatorname{Var}(T_x) + \operatorname{Var}(E_x))$ and $\rho_Y$ likewise,

$$\frac{\operatorname{Cov}(X, Y)}{\sqrt{\operatorname{Var}X\operatorname{Var}Y}} = \frac{\operatorname{Cov}(T_x, T_y)}{\sqrt{\operatorname{Var}T_x\operatorname{Var}T_y}}\sqrt{\rho_X\rho_Y}.$$
