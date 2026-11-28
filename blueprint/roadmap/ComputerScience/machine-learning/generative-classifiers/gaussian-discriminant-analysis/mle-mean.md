# Maximum likelihood class means

Consider a Gaussian discriminant model on $\mathbb{R}^\iota$, for a finite index set $\iota$, with a finite set of classes, a prior on classes, class means, and a shared precision matrix $S$. Let $(y_k, x_k)_{k < m}$ be labelled data. The sample mean of class $c$ is the average $\frac{1}{|\{k : y_k = c\}|} \sum_{k : y_k = c} x_k$ of its examples, and $0$ for a class without examples.
