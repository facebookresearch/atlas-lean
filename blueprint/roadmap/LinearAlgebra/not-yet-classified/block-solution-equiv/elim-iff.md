# Block system is equivalent to Schur-reduced system

Let $m, n, p$ be finite index sets, $A \in \mathbb{R}^{m \times n}$, $B \in \mathbb{R}^{m \times p}$, $C \in \mathbb{R}^{p \times n}$ and $D \in \mathbb{R}^{p \times p}$ invertible, and let $S = A - B D^{-1} C$ be the Schur complement of $D$. Let $x \in \mathbb{R}^n$, $u \in \mathbb{R}^m$, $v \in \mathbb{R}^p$. For every $y \in \mathbb{R}^p$,

$$\big(A x + B y = u \ \text{and}\ C x + D y = v\big) \iff \big(S x = u - B D^{-1} v \ \text{and}\ y = D^{-1}(v - C x)\big).$$
