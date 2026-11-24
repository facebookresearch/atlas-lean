# The cross-entropy loss is infinite exactly when a label is ruled out

Let $f$ be a
probabilistic classifier, assigning to each input $x \in X$ a probability distribution $f(x)$ on
a finite set of labels, and let $D = ((x_1, y_1), \dots, (x_N, y_N))$ be a labelled sample with
$N \ge 1$. The cross-entropy loss of $f$ on $D$ is $\infty$ if and only if $f(x_n)(y_n) = 0$ for
some $n$.
