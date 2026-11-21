# The cross-entropy loss is the average negative log-likelihood

Let $f$ be a probabilistic
classifier, assigning to each input $x \in X$ a probability distribution $f(x)$ on a finite set
of labels, and let $D = ((x_1, y_1), \dots, (x_N, y_N))$ be a labelled sample. The cross-entropy
loss of $f$ on $D$ equals the average surprisal of the labels,

$$\Big(\sum_{n=1}^{N} s\big(f(x_n)(y_n)\big)\Big) / N,$$

where $s(q) = -\log_2 q$ is the surprisal of a probability $q$, with $s(0) = \infty$, and the
average is computed in $[0, \infty]$.
