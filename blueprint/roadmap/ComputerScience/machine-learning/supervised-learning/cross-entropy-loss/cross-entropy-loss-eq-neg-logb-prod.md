# Cross-entropy loss via the likelihood

Let $f$ be a probabilistic classifier, assigning
to each input $x \in X$ a probability distribution $f(x)$ on a finite set of labels, and let
$D = ((x_1, y_1), \dots, (x_N, y_N))$ be a labelled sample with $f(x_n)(y_n) \ne 0$ for every $n$.
Then the cross-entropy loss of $f$ on $D$ equals $-\log_2(L) / N$, where
$L = \prod_{n=1}^{N} f(x_n)(y_n)$ is the likelihood of the sample and the division is computed in
$[0, \infty]$, so that both sides are $0$ when $N = 0$.
