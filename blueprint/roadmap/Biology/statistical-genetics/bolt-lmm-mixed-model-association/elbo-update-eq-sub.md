# The CAVI update maximizes the ELBO over its factor, with exact gap

Let $X$ be a real $n \times m$ matrix, let $y \in \mathbb{R}^n$, let $\sigma_e^2 > 0$, let $\pi$ be a probability measure on $\mathbb{R}$ such that $b \mapsto b^2$ is $\pi$-integrable, let $q = (q_1, \dots, q_m)$ be measures on $\mathbb{R}$, let $j \in \{1, \dots, m\}$, and let $q'$ be an [admissible factor](is-admissible.md) for $\pi$. Then

$$\mathrm{ELBO}(q[j \leftarrow q']) = \mathrm{ELBO}(q[j \leftarrow q_j^\ast]) - \mathrm{KL}(q' \,\|\, q_j^\ast),$$

where $q_j^\ast$ is the [coordinate-ascent update](cavi-update.md), $q[j \leftarrow q_j^\ast]$ is the [coordinate-ascent step](cavi-step.md), $\mathrm{ELBO}$ is the [evidence lower bound](elbo.md), and an infinite divergence is counted as $0$.
