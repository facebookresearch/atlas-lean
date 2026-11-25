# Median of medians selects every one-based rank

Let $L$ be a list without repeated
entries over a linear order, of length $n$, and let $1 \le i \le n$. Then median-of-medians
selection on $L$ at zero-based rank $i - 1$ returns an element $x$ of $L$, and the set
$\{y \in L : y \le x\}$ has exactly $i$ elements.
