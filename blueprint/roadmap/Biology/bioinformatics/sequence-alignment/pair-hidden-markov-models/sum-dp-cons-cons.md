# Sum recursion on two nonempty sequences

For letters $a, b$, sequences $x, y$ and a control state $q$, the [total weight](sum-dp.md) satisfies

$$T(q, a x, b y) = w(q, (a, b))\, T(q_1, x, y) + w(q, (a, -))\, T(q_2, x, b y) + w(q, (-, b))\, T(q_3, a x, y),$$

with $q_1 = \nu(q, (a, b))$, $q_2 = \nu(q, (a, -))$ and $q_3 = \nu(q, (-, b))$.
