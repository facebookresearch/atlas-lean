# Minimizing cross-entropy is maximum likelihood

Let $f$ and $g$ be probabilistic
classifiers, each assigning to every input $x \in X$ a probability distribution on a finite set of
labels, and let $D = ((x_1, y_1), \dots, (x_N, y_N))$ be a labelled sample with $N \ge 1$. Then
the cross-entropy loss of $f$ on $D$ is at most that of $g$ if and only if
$\prod_{n=1}^{N} g(x_n)(y_n) \le \prod_{n=1}^{N} f(x_n)(y_n)$, that is, $f$ gives the labels at
least as large a likelihood as $g$.

A label predicted to be impossible gives likelihood $0$ and loss $\infty$.
