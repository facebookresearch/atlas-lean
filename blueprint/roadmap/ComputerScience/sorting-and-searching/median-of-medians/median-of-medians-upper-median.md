# Median of medians finds the upper median

Let $L$ be a nonempty list of length $n$ over a
linear order, and let $k = \lfloor n/2 \rfloor$. Then median-of-medians selection on $L$ at
zero-based rank $k$ returns an element $x$ of $L$ such that at most $k$ entries of $L$ are less
than $x$ and more than $k$ entries of $L$ are at most $x$, where entries are counted with
repetition.
