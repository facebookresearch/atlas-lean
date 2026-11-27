# Novikoff's mistake bound over an ordered field

Let $F$ be a linearly ordered field,
$\iota$ a finite type, $v \cdot w = \sum_{i \in \iota} v_i w_i$ the dot product on $F^\iota$,
$u \in F^\iota$, and $\gamma, R \in F$ with $\gamma > 0$. Let $L$ be a finite list of labelled
examples $(x, y)$ with $x \in F^\iota$ and $y$ a Boolean, such that every example in $L$ satisfies
$\gamma \le \operatorname{sign}(y)\,(u \cdot x)$ and $x \cdot x \le R^2$. If the perceptron run
over $L$ from the zero weights with $0$ mistakes so far ends with mistake count $k$, then
$k \le (u \cdot u) R^2 / \gamma^2$; for a unit vector $u$ this is the textbook bound
$R^2 / \gamma^2$.
