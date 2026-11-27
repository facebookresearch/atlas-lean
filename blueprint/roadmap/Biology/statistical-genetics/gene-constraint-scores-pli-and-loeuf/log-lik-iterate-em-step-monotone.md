# Monotonicity of the log-likelihood along the class-weight EM iterates

Let $\iota$ be a finite nonempty set of classes, let $\lambda : \iota \to \mathbb{R}$ with $\lambda_c > 0$ for every $c$, let $x_1, \dots, x_N$ be [gene data](gene-data.md) with $N > 0$, and let $w^{(0)}$ be [strictly positive weights](pos-weights.md) on $\iota$. Let $w^{(k)}$ be obtained from $w^{(0)}$ by $k$ applications of the [EM update](em-step.md). Then $k \mapsto \ell(w^{(k)})$ is nondecreasing, where $\ell(w) = \sum_{n} \log \sum_{z} p_w(x_n, z)$ is the log-likelihood of the [joint model](joint.md).
