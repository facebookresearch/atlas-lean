# Cross-entropy loss

Let $f$ be a probabilistic classifier, assigning to each input
$x \in X$ a probability distribution $f(x)$ on a finite set of labels, and let
$D = ((x_1, y_1), \dots, (x_N, y_N))$ be a labelled sample. The cross-entropy (log) loss of $f$
on $D$, in bits, is the value in $[0, \infty]$

$$\Big(\sum_{n=1}^{N} H\big(\delta_{y_n}, f(x_n)\big)\Big) / N,$$

where $H$ is the cross-entropy and $\delta_y$ is the point mass at $y$; it is $0$ when $N = 0$.
