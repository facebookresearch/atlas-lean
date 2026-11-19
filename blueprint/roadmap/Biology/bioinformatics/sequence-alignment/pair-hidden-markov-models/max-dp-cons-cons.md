# Max recursion on two nonempty sequences

For letters $a, b$, sequences $x, y$ and a control state $q$, the [max-recursion value](max-dp.md) satisfies

$$U(q, a x, b y) = \max\bigl(w(q, (a, b))\, U(q_1, x, y),\ w(q, (a, -))\, U(q_2, x, b y),\ w(q, (-, b))\, U(q_3, a x, y)\bigr),$$

with $q_1 = \nu(q, (a, b))$, $q_2 = \nu(q, (a, -))$ and $q_3 = \nu(q, (-, b))$.
