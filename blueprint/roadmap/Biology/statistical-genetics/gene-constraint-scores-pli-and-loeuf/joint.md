# Joint likelihood of gene data and constraint class

Let $\iota$ be a finite set of classes, let $\lambda : \iota \to \mathbb{R}$ be class rates and $w$ [strictly positive weights](pos-weights.md) on $\iota$. The joint weight of [gene data](gene-data.md) $x = (o, E)$ and a class $z \in \iota$ is

$$p_w(x, z) = w_z\, L(\lambda_z E, o),$$

where $L$ is the [Poisson likelihood](poisson-lik.md). When the rates $\lambda$ and $E$ are nonnegative and the weights sum to $1$, it is the joint probability of the class $z$ and the observed count $o$.
