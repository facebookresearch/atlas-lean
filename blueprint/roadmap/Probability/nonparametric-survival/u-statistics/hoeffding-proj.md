# Hoeffding projection of a kernel

Let $\mu$ be a measure on a measurable space $\alpha$, $h : \alpha^m \to \mathbb{R}$ a kernel of degree $m$ and $c \in \mathbb{N}$. Hoeffding's $c$-th projection of $h$ is the function on $\alpha^c$

$$h_c(y_1, \dots, y_c) = \int h(y_1, \dots, y_c, z_{c+1}, \dots, z_m)\, \mu^{\otimes (m - c)}(dz),$$

that is $h_c(y) = \mathbb{E}\, h(y_1, \dots, y_c, X_{c+1}, \dots, X_m)$ with $X_{c+1}, \dots, X_m$ i.i.d. with law $\mu$ when $\mu$ is a probability measure. The integral is read as $0$ when the integrand is not integrable; for $c \ge m$ no coordinate is integrated and $h_c(y) = h(y_1, \dots, y_m)$.

## Sources

- Wassily Hoeffding, *A class of statistics with asymptotically normal distribution*, Ann. Math. Statist. 19 (1948), no. 3, 293–325, DOI 10.1214/aoms/1177730196.
