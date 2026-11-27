# The M-step maximizes the EM objective

Let $\iota$ be a finite nonempty set of classes, let $\lambda : \iota \to \mathbb{R}$ with $\lambda_c > 0$ for every $c$, and let $x_1, \dots, x_N$ be [gene data](gene-data.md) with $N > 0$. For [strictly positive weights](pos-weights.md) $w', w$ on $\iota$, put

$$Q(w' \mid w) = \sum_{n=1}^{N} \sum_{z \in \iota} P_w(z \mid x_n) \log p_{w'}(x_n, z),$$

where $p$ is the [joint likelihood](joint.md) and $P_w(z \mid x_n)$ the corresponding posterior. Then $Q(w' \mid w) \le Q(w^{\mathrm{new}} \mid w)$, where $w^{\mathrm{new}}$ is the [EM update](em-step.md) of $w$.
