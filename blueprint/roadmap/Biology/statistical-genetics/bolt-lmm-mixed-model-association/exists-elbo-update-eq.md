# The ELBO as a function of one factor

Let $X$ be a real $n \times m$ matrix, let $y \in \mathbb{R}^n$, let $\sigma_e^2$ be real, let $\pi$ be a measure on $\mathbb{R}$, let $q = (q_1, \dots, q_m)$ be measures on $\mathbb{R}$, and let $j \in \{1, \dots, m\}$. Then there is a real constant $C$ such that for every [admissible factor](is-admissible.md) $q'$ for $\pi$,

$$\mathrm{ELBO}(q[j \leftarrow q']) = \int f_j\, dq' - \mathrm{KL}(q' \,\|\, \pi) + C,$$

where $q[j \leftarrow q']$ is $q$ with its $j$-th factor replaced by $q'$, $\mathrm{ELBO}$ is the [evidence lower bound](elbo.md) and $f_j$ the [coordinate-ascent potential](potential.md) of $q$.
