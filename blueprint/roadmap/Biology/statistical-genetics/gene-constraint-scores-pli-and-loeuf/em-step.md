# EM update of the Poisson mixture class weights

Let $\iota$ be a finite nonempty set of classes, let $\lambda : \iota \to \mathbb{R}$ with $\lambda_c > 0$ for every $c$, and let $x_1, \dots, x_N$ be [gene data](gene-data.md) with $N > 0$. For [strictly positive weights](pos-weights.md) $w$ on $\iota$, the EM update is the strictly positive weight vector

$$w'_z = \frac{1}{N} \sum_{n=1}^{N} P_w(z \mid x_n) = \frac{M_w(z)}{N},$$

where $P_w(z \mid x_n) = p_w(x_n, z) / \sum_{z'} p_w(x_n, z')$ is the posterior of class $z$ for gene $n$ under the [joint likelihood](joint.md) and $M_w$ is the [class mass](mass.md).
