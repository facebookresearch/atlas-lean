# Posterior

Consider a Gaussian discriminant model on $\mathbb{R}^\iota$, for a finite index set $\iota$, with a finite set of classes. The posterior score of class $c$ at $x$ is the joint density of $(c, x)$ divided by $\sum_{c'}$ of the joint densities of $(c', x)$. It is the posterior probability of $c$ given $x$ when the denominator is positive, in particular for a positive definite precision matrix; when the denominator is $0$, the division by zero makes every score $0$.
