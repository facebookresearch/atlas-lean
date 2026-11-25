# Schur elimination: block system implies reduced system

Let $m, n, p$ be finite index sets, $A \in \mathbb{R}^{m \times n}$, $B \in \mathbb{R}^{m \times p}$, $C \in \mathbb{R}^{p \times n}$ and $D \in \mathbb{R}^{p \times p}$ invertible, and let $S = A - B D^{-1} C$ be the Schur complement of $D$. Let $x \in \mathbb{R}^n$, $u \in \mathbb{R}^m$, $v \in \mathbb{R}^p$. If $y \in \mathbb{R}^p$ satisfies

$$A x + B y = u, \qquad C x + D y = v,$$

then

$$S x = u - B D^{-1} v \qquad\text{and}\qquad y = D^{-1}(v - C x).$$
