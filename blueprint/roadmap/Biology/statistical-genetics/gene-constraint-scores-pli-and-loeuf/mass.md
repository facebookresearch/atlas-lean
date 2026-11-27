# Expected number of genes in a constraint class

Let $\iota$ be a finite set of classes, let $\lambda : \iota \to \mathbb{R}$ be class rates, let $x_1, \dots, x_N$ be [gene data](gene-data.md) with $x_n = (o_n, E_n)$, and let $w$ be [strictly positive weights](pos-weights.md) on $\iota$. The mass of class $z \in \iota$ is

$$M_w(z) = \sum_{n=1}^{N} \frac{w_z\, L(\lambda_z E_n, o_n)}{\sum_{z' \in \iota} w_{z'}\, L(\lambda_{z'} E_n, o_n)},$$

where $L$ is the [Poisson likelihood](poisson-lik.md), with the convention $x/0 = 0$. When the rates and the $E_n$ are nonnegative and every denominator is positive, it is the expected number of genes in class $z$ under the posteriors at weights $w$.
