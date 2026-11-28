# Maximum likelihood parameters of Gaussian discriminant analysis

Consider a Gaussian discriminant model on $\mathbb{R}^\iota$, for a finite index set $\iota$, with a finite set of classes, a prior on classes, class means, and a shared precision matrix $S$. Let $(y_k, x_k)_{k < m}$ be labelled data. For a given precision matrix $S$, the estimate takes the class frequencies as the prior and the class sample means as the means.

When $S$ is positive definite, these estimates maximize the likelihood over all priors and means with precision $S$ ([Maximum likelihood estimation](likelihood-le-mle.md)).
