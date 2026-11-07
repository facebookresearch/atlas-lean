# Self-dual monotone functions on $n+4$ variables, interval form (Theorem 14)

Order
$\{0,1\}$ by $0 < 1$, inputs coordinatewise and Boolean functions pointwise, with $\vee$ the
pointwise maximum. Let $D_n$ be the set of monotone Boolean functions on $\{0,1\}^n$, and let
$f^*(x) = \lnot f(\bar x)$ be the dual of $f$, where $\bar x$ is the coordinatewise complement of
$x$; a Boolean function $F$ is self-dual monotone if it is monotone and $F^* = F$. The
concatenation $W_0 \cdot W_1 \cdots W_{15}$ of Boolean functions on $\{0,1\}^n$ is the Boolean
function on $\{0,1\}^{n+4}$ sending $(x, y_0, y_1, y_2, y_3)$, with $x \in \{0,1\}^n$, to
$W_i(x)$, where $i = y_0 + 2y_1 + 4y_2 + 8y_3$. Let $a, b, c, d, e, f, g, h \in D_n$ satisfy
$h^* \le h$, $h^* \le a \le h$, $h^* \le b \le h$, $h^* \le c \le h$,
$a \vee b \vee c \le d \le h$, $a \vee b^* \vee c^* \le e \le h$,
$b \vee a^* \vee c^* \le f \le h$ and $c \vee a^* \vee b^* \le g \le h$. Then the concatenation

$$h^* \cdot g^* \cdot f^* \cdot a \cdot e^* \cdot b \cdot c \cdot d \cdot
d^* \cdot c^* \cdot b^* \cdot e \cdot a^* \cdot f \cdot g \cdot h$$

is a self-dual monotone Boolean function on $\{0,1\}^{n+4}$. Conversely, every self-dual
monotone Boolean function on $\{0,1\}^{n+4}$ equals this concatenation for some
$a, b, c, d, e, f, g, h \in D_n$ satisfying these inequalities.

## Sources

- Bartłomiej Pawelski and Andrzej Szepietowski, *Counting Self-Dual Monotone Boolean Functions*, Journal of Integer Sequences 28 (2025), Article 25.6.5, Theorem 14 (`jis-2025-25.6.5-thm-14`).
