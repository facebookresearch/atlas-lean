# Battery stored-energy flow

For efficiencies $\eta_c$, $\eta_d$ and schedules $\Delta t, P_c, P_d : \mathbb{N} \to \mathbb{R}$ (interval lengths and charge and discharge powers), the stored-energy flow of interval $k$ is

$$\Delta t_k \left(\eta_c P_{c,k} - \frac{P_{d,k}}{\eta_d}\right),$$

in joules when the powers are in watts and the times in seconds.

Real division uses $x/0 = 0$. As a formula it is defined for all real inputs; it is the stored-energy flow of the battery model when the interval lengths and powers are nonnegative and the efficiencies lie in $(0, 1]$.
