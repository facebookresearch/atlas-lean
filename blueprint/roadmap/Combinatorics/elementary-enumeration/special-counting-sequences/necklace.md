# Fixed-length necklaces

Let $A$ be a set and let $n \in \mathbb{N}$. For $n \ge 1$, a word
of length $n$ over $A$ is a tuple $(a_0, a_1, \dots, a_{n-1})$ of elements of $A$, and two words
$(a_0, \dots, a_{n-1})$ and $(b_0, \dots, b_{n-1})$ are rotationally equivalent if there is an
integer $r$ with $0 \le r < n$ such that $b_i = a_{(i+r) \bmod n}$ for $0 \le i < n$. A necklace of
length $n$ over $A$ is an equivalence class of words of length $n$ under rotational equivalence.
For $n = 0$ there is exactly one necklace over $A$, represented by the empty word.

Reflections are not identified.
