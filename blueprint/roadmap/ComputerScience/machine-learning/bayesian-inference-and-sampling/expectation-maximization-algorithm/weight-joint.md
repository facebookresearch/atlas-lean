# Weight-times-likelihood joint model

Let $Z$ be a finite set and let $f(x, z)$ be real numbers indexed by observations $x$ and latent values $z \in Z$. For [strictly positive weights](../../../../Biology/statistical-genetics/gene-constraint-scores-pli-and-loeuf/pos-weights.md) $w$ on $Z$, the weight-times-likelihood joint model with parameter $w$ is $p_w(x, z) = w(z)\,f(x, z)$. With $f(x, z)$ the likelihood of $x$ under component $z$, this is a finite mixture with mixing weights $w$ as the parameter.
