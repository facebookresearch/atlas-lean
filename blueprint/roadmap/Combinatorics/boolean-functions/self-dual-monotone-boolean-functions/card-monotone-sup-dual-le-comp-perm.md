# Monotone functions above $b \lor b^*$: the count is invariant under relabelling

Order $\{0,1\}$ by $0 < 1$, inputs in $\{0,1\}^n$ coordinatewise and Boolean functions on $\{0,1\}^n$ pointwise. For a Boolean function $b$ on $\{0,1\}^n$ let $b^*(x) = \lnot b(\bar x)$ be its dual, where $\bar x$ is the coordinatewise complement of $x$, and let $r(b)$ be the number of monotone Boolean functions $z$ on $\{0,1\}^n$ with $b \lor b^* \le z$, where $\lor$ is pointwise disjunction. For a permutation $\pi$ of the $n$ coordinates write $b^\pi$ for the function $x \mapsto b(x \circ \pi)$, where $(x \circ \pi)_i = x_{\pi(i)}$. Then $r(b^\pi) = r(b)$ for every Boolean function $b$, monotone or not, and every permutation $\pi$.

For monotone $b$, $r(b)$ is the summand in the [count of self-dual monotone functions on $n + 2$ variables](card-self-dual-monotone-add-two.md).
