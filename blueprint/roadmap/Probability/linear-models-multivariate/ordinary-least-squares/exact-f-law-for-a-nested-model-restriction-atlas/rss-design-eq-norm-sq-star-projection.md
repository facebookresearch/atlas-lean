# Residual sum of squares as a projection norm

Let $X$ be a real $n \times p$ design matrix with $X^\top X$ invertible, and $y \in \mathbb{R}^n$. The residual sum of squares $\|y - X\hat\beta\|^2$ of the least-squares fit $\hat\beta = (X^\top X)^{-1}X^\top y$ equals $\|P_{U^\perp}\, y\|^2$, the squared norm of the orthogonal projection of $y$ onto the orthogonal complement of the column space $U = \operatorname{col}(X)$.
