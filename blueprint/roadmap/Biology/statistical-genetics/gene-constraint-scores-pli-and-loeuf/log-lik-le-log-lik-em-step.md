# EM does not decrease the likelihood

Let $\iota$ be a finite nonempty set of classes, let $\lambda : \iota \to \mathbb{R}$ with $\lambda_c > 0$ for every $c$, and let $x_1, \dots, x_N$ be [gene data](gene-data.md) with $N > 0$. For [strictly positive weights](pos-weights.md) $w$ put

$$\ell(w) = \sum_{n=1}^{N} \log \sum_{z \in \iota} p_w(x_n, z),$$

where $p$ is the [joint likelihood](joint.md). Then $\ell(w) \le \ell(w^{\mathrm{new}})$ for every $w$, where $w^{\mathrm{new}}$ is the [EM update](em-step.md) of $w$.
