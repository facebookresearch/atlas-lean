# Sum recursion with an empty first sequence

For a letter $b$, a sequence $y$ and a control state $q$, the [total weight](sum-dp.md) satisfies $T(q, \text{empty}, b y) = w(q, (-, b))\, T(\nu(q, (-, b)), \text{empty}, y)$.
