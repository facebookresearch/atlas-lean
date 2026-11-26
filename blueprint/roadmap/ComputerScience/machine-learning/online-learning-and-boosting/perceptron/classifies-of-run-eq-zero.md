# A mistake-free pass classifies every example

Let $K$ be a commutative ring with a linear
order, $\iota$ a finite type, and $v \cdot w = \sum_{i \in \iota} v_i w_i$ the dot product on
$K^\iota$. Let $L$ be a finite list of labelled examples $(x, y)$ with $x \in K^\iota$ and $y$ a
Boolean, and let $w \in K^\iota$. If the perceptron run over $L$ from weights $w$ with $0$ mistakes
so far ends with mistake count $0$, then every example $(x, y)$ in $L$ satisfies
$0 < \operatorname{sign}(y)\,(w \cdot x)$.
