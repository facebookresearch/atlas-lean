# Kaplan–Meier jump at an observation time

For [grouped right-censored data](censored-data.md), the Kaplan–Meier jump at $t_j$ is

$$\hat S(t_j^-)\, \frac{d_j}{n_j} = \Big(\prod_{l < j} \Big(1 - \frac{d_l}{n_l}\Big)\Big) \frac{d_j}{n_j},$$

with $d_j/0 = 0$.
