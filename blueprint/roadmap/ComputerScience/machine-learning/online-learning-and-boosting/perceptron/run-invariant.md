# Invariant of the perceptron run

Let $K$ be a linearly ordered commutative ring, $\iota$ a
finite type, $v \cdot w = \sum_{i \in \iota} v_i w_i$ the dot product on $K^\iota$, $u \in K^\iota$
and $\gamma, R \in K$. Let $L$ be a finite list of labelled examples $(x, y)$ with $x \in K^\iota$
and $y$ a Boolean, such that every example in $L$ satisfies
$\gamma \le \operatorname{sign}(y)\,(u \cdot x)$ and $x \cdot x \le R^2$. Let $w \in K^\iota$ and
$m \in \mathbb{N}$ satisfy $m \gamma \le u \cdot w$ and $w \cdot w \le m R^2$, and let the
perceptron run over $L$ from $w$ with $m$ mistakes so far end with weights $w'$ and mistake count
$m'$. Then $m' \gamma \le u \cdot w'$ and $w' \cdot w' \le m' R^2$.
