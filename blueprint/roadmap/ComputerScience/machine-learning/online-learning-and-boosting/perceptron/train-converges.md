# The perceptron converges

Let $K$ be a linearly ordered commutative ring, let $\iota$ be a
finite index type, write $a \cdot b = \sum_{j \in \iota} a_j b_j$ for $a, b \in K^\iota$, and let
the label sign $s(y)$ be $1$ if the Boolean $y$ is true and $-1$ otherwise. Let $D$ be a finite
list of examples $(x, y)$ with $x \in K^\iota$ and $y$ a Boolean, and let $u \in K^\iota$ and
$\gamma, R \in K$ with $\gamma > 0$ be such that every example $(x, y)$ of $D$ satisfies
$\gamma \le s(y)\,(u \cdot x)$ and $x \cdot x \le R^2$. Then for every natural number $n$ with
$(u \cdot u) R^2 < n \gamma^2$, perceptron training on $D$ from the zero weights with at most $n$
passes returns some weights $v$, and $0 < s(y)\,(v \cdot x)$ for every example $(x, y)$ of $D$.
