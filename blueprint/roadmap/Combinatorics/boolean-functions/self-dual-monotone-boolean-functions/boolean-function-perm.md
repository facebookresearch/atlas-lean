# Relabelling the variables of a Boolean function

For a natural number $n$ and a permutation $\pi$ of $\{0, \dots, n-1\}$, relabelling by $\pi$ sends a Boolean function $f$ on $\{0,1\}^n$ to $f^\pi \colon x \mapsto f(x \circ \pi)$, where $(x \circ \pi)_i = x_{\pi(i)}$. It is an order automorphism of the set of all Boolean functions on $\{0,1\}^n$, ordered pointwise with $0 < 1$: a bijection, with inverse $f \mapsto (x \mapsto f(x \circ \pi^{-1}))$, such that $f^\pi \le g^\pi$ if and only if $f \le g$.
