# Overall survival from the competing-risks counts

In grouped competing-risks data, the overall survival just before $t_j$ is
$$\hat S(t_j^-) = \prod_{l < j} \Bigl(1 - \frac{\sum_c d_{l,c}}{Y_l}\Bigr),$$
where a ratio with denominator $0$ is taken to be $0$.
