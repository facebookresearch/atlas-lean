# Self-dual monotone concatenations on n + 4 variables

Order $\{0,1\}$ by $0 < 1$, inputs coordinatewise and Boolean functions pointwise, with $\lor$ the pointwise disjunction; let $f^*(x) = \lnot f(\bar x)$ be the dual of $f$, where $\bar x$ is the coordinatewise complement of $x$, and call a Boolean function self-dual monotone when it is monotone and equals its dual. Let $a, b, c, d, e, f, g, h$ be monotone Boolean functions on $\{0,1\}^n$ with $a \lor b \lor c \le d \le h$, $a \lor b^* \lor c^* \le e \le h$, $b \lor a^* \lor c^* \le f \le h$ and $c \lor a^* \lor b^* \le g \le h$. Then the concatenation

$$h^* \cdot g^* \cdot f^* \cdot a \cdot e^* \cdot b \cdot c \cdot d \cdot d^* \cdot c^* \cdot b^* \cdot e \cdot a^* \cdot f \cdot g \cdot h$$

is a self-dual monotone Boolean function on $\{0,1\}^{n+4}$. Here the concatenation $W_0 \cdot W_1 \cdots W_{15}$ sends $(x, y_0, y_1, y_2, y_3)$, with $x \in \{0,1\}^n$, to $W_i(x)$, where $i = y_0 + 2y_1 + 4y_2 + 8y_3$. No bound $a \lor b \lor c \lor a^* \lor b^* \lor c^* \le h$ is assumed; it follows from the others.
