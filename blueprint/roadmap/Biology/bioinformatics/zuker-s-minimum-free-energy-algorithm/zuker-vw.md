# Zuker's recursion

Fix a sequence $s$, a complementarity relation, a minimum hairpin size $m$ and a [loop energy model](loop-energy.md). Values lie in $\mathbb{R} \cup \{+\infty\}$, with $+\infty$ absorbing in sums and a minimum over an empty range equal to $+\infty$. For the interval of length $n$ starting at $i$ (positions $i, \dots, j$ with $j = i + n - 1$, truncated at $0$), define $V(i, n)$ and $\mathrm{WM}(i, n)$ by recursion on $n$.

If $i + m < j$ and $i$ and $j$ [can pair](../mccaskill-partition-function-for-rna-folding/can-pair.md), then $V(i, n)$ is the least of

- $H(i, j)$;
- $I(i, j, i + u, i + u + v - 1) + V(i + u, v)$ over $u, v \ge 1$ with $u + v < n$ (inner pair $(i + u, i + u + v - 1)$);
- $a + \mathrm{WM}(i + 1, u) + \mathrm{WM}(i + u + 1, n - u - 2)$ over $u \ge 1$ with $u + 2 < n$ (the fragments $i + 1, \dots, i + u$ and $i + u + 1, \dots, j - 1$);

otherwise $V(i, n) = +\infty$.

$\mathrm{WM}(i, 0) = +\infty$ (an empty multiloop fragment is impossible), and for $n \ge 1$, $\mathrm{WM}(i, n)$ is the least of

- $V(i, n) + b$;
- $\mathrm{WM}(i + 1, n - 1) + c$ (base $i$ unpaired) and $\mathrm{WM}(i, n - 1) + c$ (base $j$ unpaired);
- $\mathrm{WM}(i, u) + \mathrm{WM}(i + u, n - u)$ over $1 \le u < n$.
