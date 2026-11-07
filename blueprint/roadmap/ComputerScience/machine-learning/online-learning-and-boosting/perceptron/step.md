# Perceptron step

Let $K$ be a commutative ring with a linear order, $\iota$ a finite type,
and $v \cdot w = \sum_{i \in \iota} v_i w_i$ the dot product on $K^\iota$. One perceptron step
takes a state $(w, m)$, made of weights $w \in K^\iota$ and a mistake count $m \in \mathbb{N}$, and
a labelled example $(x, y)$ with $x \in K^\iota$ and $y$ a Boolean. If
$\operatorname{sign}(y)\,(w \cdot x) \le 0$, that is, $w$ does not classify the example strictly
correctly, the step returns $(w + \operatorname{sign}(y)\,x,\ m + 1)$ and counts a mistake;
otherwise it returns $(w, m)$ unchanged.
