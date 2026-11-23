# Sum recursion with an empty second sequence

For a letter $a$, a sequence $x$ and a control state $q$, the [total weight](sum-dp.md) satisfies $T(q, a x, \text{empty}) = w(q, (a, -))\, T(\nu(q, (a, -)), x, \text{empty})$.
