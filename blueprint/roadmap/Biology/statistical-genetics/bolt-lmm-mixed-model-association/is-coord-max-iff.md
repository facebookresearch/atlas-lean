# Stationary points of coordinate ascent

Let $X$ be a real $n \times m$ matrix, let $y \in \mathbb{R}^n$, let $\sigma_e^2 > 0$, let $\pi$ be a probability measure on $\mathbb{R}$ such that $b \mapsto b^2$ is $\pi$-integrable, let $q = (q_1, \dots, q_m)$ be measures on $\mathbb{R}$, and let $j \in \{1, \dots, m\}$ be such that $q_j$ is an [admissible factor](is-admissible.md) for $\pi$. Then the following are equivalent:

- $\mathrm{ELBO}(q[j \leftarrow q']) \le \mathrm{ELBO}(q)$ for every admissible factor $q'$ for $\pi$;
- $q_j = q_j^\ast$, the [coordinate-ascent update](cavi-update.md) of factor $j$.
