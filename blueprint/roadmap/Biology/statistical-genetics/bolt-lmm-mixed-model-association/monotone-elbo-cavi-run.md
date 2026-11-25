# The ELBO is nondecreasing along coordinate ascent

Let $X$ be a real $n \times m$ matrix, let $y \in \mathbb{R}^n$, let $\sigma_e^2 > 0$, let $\pi$ be a probability measure on $\mathbb{R}$ such that $b \mapsto b^2$ is $\pi$-integrable, and let $q = (q_1, \dots, q_m)$ consist of [admissible factors](is-admissible.md) for $\pi$. Then for every update schedule $s : \mathbb{N} \to \{1, \dots, m\}$, the sequence $t \mapsto \mathrm{ELBO}(q^{(t)})$ along [coordinate ascent](cavi-run.md) is nondecreasing.
