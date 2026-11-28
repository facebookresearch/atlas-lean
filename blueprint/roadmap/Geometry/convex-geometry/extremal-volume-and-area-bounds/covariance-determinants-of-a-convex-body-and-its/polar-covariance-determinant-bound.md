# Klartag's covariance determinant bound for polar bodies

Conjecture (B. Klartag): there is a constant $C > 0$ such that for every $n \ge 1$ and every convex body $K \subseteq \mathbb{R}^n$ with barycenter at the origin,

$$\det\bigl(\operatorname{Cov}(K)\, \operatorname{Cov}(K^\circ)\bigr) \le \left(\frac{C}{n}\right)^{2n},$$

where $\operatorname{Cov}(S)$ is the $n \times n$ covariance matrix of the uniform probability measure on $S$ (Lebesgue measure restricted to $S$ and divided by $|S|$), with entries $\operatorname{Cov}(S)_{ij} = \mathbb{E}[(X_i - \mathbb{E}X_i)(X_j - \mathbb{E}X_j)]$ for $X$ uniform on $S$, and $K^\circ = \{y : \langle x, y\rangle \le 1 \text{ for all } x \in K\}$ is the polar of $K$. A convex body is a compact convex set with nonempty interior, and barycenter at the origin means $\int_K x \, dx = 0$.

## Sources

- B. Klartag, in Convex Geometry and its Applications, Oberwolfach Reports 15 (2018), no. 54, p. 3224, inequality (1), https://doi.org/10.4171/OWR/2018/54
