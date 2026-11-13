# Expansion of the residual sum of squares

Let $X$ be a real design matrix with $m$ rows
and columns indexed by a finite type $\iota$, let $y \in \mathbb{R}^m$, and write
$S(\theta) = (y - X\theta) \cdot (y - X\theta)$ for the residual sum of squares. Then for all
$\theta, v \in \mathbb{R}^\iota$,

$$S(\theta + v) = S(\theta) - 2\, v \cdot \bigl(X^\top (y - X\theta)\bigr) + (Xv) \cdot (Xv).$$
