# Iterated forward shift inserts leading zeroes

Let $\mathbb{K}$ be $\mathbb{R}$ or $\mathbb{C}$ and let $s$ be the [forward shift](shift-fun.md) of sequences in $\mathbb{K}$, $s(x_0, x_1, \dots) = (0, x_0, x_1, \dots)$. For every $n \in \mathbb{N}$, every sequence $x$ and every $i \in \mathbb{N}$, the $n$-fold iterate inserts $n$ leading zeroes:

$$
(s^n x)_i = \begin{cases} 0, & i < n, \\ x_{i-n}, & i \ge n. \end{cases}
$$
