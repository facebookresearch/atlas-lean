# Relabelling the variables preserves the weight

Let $b$ be a Boolean function on $\{0,1\}^n$, monotone or not, and let $\ell(b)$ be the number of inputs $x \in \{0,1\}^n$ with $b(x) = 1$. For a permutation $\pi$ of the $n$ coordinates write $b^\pi$ for the function $x \mapsto b(x \circ \pi)$, where $(x \circ \pi)_i = x_{\pi(i)}$. Then $\ell(b^\pi) = \ell(b)$.
