# Joint density in Gaussian discriminant analysis

Consider a Gaussian discriminant model on $\mathbb{R}^\iota$, for a finite index set $\iota$, with a finite set of classes, a prior on classes, class means, and a shared precision matrix $S$. If $S$ is positive definite and class $c$ has positive prior probability, then the joint density of class $c$ and feature vector $x$ factors as the class-independent term (the Gaussian density with mean $0$ and precision $S$ at $x$) times the exponential of the discriminant of $c$ at $x$.
