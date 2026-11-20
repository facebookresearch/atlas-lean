# Kaplan–Meier jump as survival times the Nelson–Aalen jump

The jump $\hat S(t_j^-) \, d_j / Y_j$ of the Kaplan–Meier estimate at $t_j$ is $\hat S(t_j^-)$ times the
Nelson–Aalen jump:
$$\hat S(t_j^-) \, \frac{d_j}{Y_j} = \hat S(t_j^-) \bigl(\hat A(t_j) - \hat A(t_j^-)\bigr),$$
where $\hat S(t_j^-) = \prod_{l < j} (1 - d_l / Y_l)$ and $\hat A(t_j^-) = \sum_{l < j} d_l / Y_l$.
