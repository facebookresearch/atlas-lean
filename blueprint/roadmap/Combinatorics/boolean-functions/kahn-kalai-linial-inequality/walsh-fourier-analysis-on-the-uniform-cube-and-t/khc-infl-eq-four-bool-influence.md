# Influence of an event is four times its quarter-square influence

Let $\iota$ be a finite set, $e : \iota \to \{1, \dots, n\}$ a bijection, $f = 1_A$ the indicator of a set $A \subseteq \{0, 1\}^\iota$, and $f^e(y) = f(y \circ e)$ for $y \in \{0, 1\}^n$. For every $i \in \iota$,

$$\mathbb{E}\big\lvert f(x^{i \to 1}) - f(x^{i \to 0})\big\rvert = 4\, \mathbb{E}\Big[\Big(\frac{f^e(y) - f^e(y^{\oplus e(i)})}{2}\Big)^2\Big],$$

where both expectations are under the uniform measure and $y^{\oplus j}$ is $y$ with coordinate $j$ flipped. The left side is the [influence](../../osss-inequality-for-decision-trees/infl.md) of $i$ on $A$; the right side is four times the quarter-square influence of $e(i)$ on $f^e$.
