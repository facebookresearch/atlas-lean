# The left-endpoint Riemann–Stieltjes integral

For $f, h : \mathbb{R} \to \mathbb{R}$ and $a, b \in \mathbb{R}$, the left-endpoint Riemann–Stieltjes integral of $f$ against $h$ on $[a, b]$ is the limit, along refinement of partitions, of the left-endpoint sums $\sum f(u)\,(h(x) - h(u))$ over the cells $(u, x]$, when these sums converge. When they do not converge the value is unspecified: it is some real number, but the definition does not say which.

The partitions are those of the point sets formed by inserting both endpoints $a$ and $b$ into the points of a finite set that lie strictly between $a$ and $b$, ordered increasingly. For $a > b$ the interval $[a, b]$ is empty and every such point set is $\{b, a\}$, with the single cell $(b, a]$; the sums are then not those of an oriented integral. For example, from $a = 1$ to $b = 0$ with $f = 1$ and $h(x) = x$ the left-endpoint sum is $h(1) - h(0) = +1$, not $-1$ and not the empty sum.
