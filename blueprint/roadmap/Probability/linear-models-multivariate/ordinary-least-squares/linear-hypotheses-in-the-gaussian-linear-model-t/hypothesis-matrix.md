# Hypothesis matrix of a linear hypothesis

Let $X$ be a real $m \times k$ design matrix and $C$ a real $r \times k$ matrix encoding the linear hypothesis $C\beta = c$. With $B = (X^\top X)^{-1}X^\top$, the hypothesis matrix is

$$H_C = B^\top C^\top\big(C(X^\top X)^{-1}C^\top\big)^{-1} C B,$$

with matrix inverses (the zero matrix when singular). If $X^\top X$ is invertible, $y = X\beta + \varepsilon$ and $C\beta = c$, then $\hat\beta = By$ satisfies $(C\hat\beta - c)^\top\big(C(X^\top X)^{-1}C^\top\big)^{-1}(C\hat\beta - c) = \varepsilon^\top H_C\varepsilon$, which is $r$ times the numerator of the $F$ statistic.
