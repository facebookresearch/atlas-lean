# Difference of nested residual sums of squares as a projection norm

Let $X$ be a real $n \times p$ design and $X_0$ a real $n \times p_0$ design with $X^\top X$ and $X_0^\top X_0$ invertible, and suppose the column spaces are nested: $R = \operatorname{col}(X_0) \subseteq U = \operatorname{col}(X)$. For every $y \in \mathbb{R}^n$,

$$\mathrm{RSS}(X_0, y) - \mathrm{RSS}(X, y) = \big\|P_{R^\perp \cap U}\, y\big\|^2,$$

the squared norm of the orthogonal projection of $y$ onto the orthogonal complement of $R$ inside $U$.
