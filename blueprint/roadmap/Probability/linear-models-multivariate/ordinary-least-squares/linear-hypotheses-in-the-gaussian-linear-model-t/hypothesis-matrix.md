# Hypothesis matrix of a linear hypothesis

Let $X$ be a real $m \times k$ design matrix and $C$ a real $r \times k$ matrix encoding the linear hypothesis $C\beta = c$. With $B = (X^\top X)^{-1}X^\top$, the hypothesis matrix is

$$H_C = B^\top C^\top\big(C(X^\top X)^{-1}C^\top\big)^{-1} C B,$$

with matrix inverses (the zero matrix when singular). Under $C\beta = c$ the numerator of the $F$ statistic is $\varepsilon^\top H_C\varepsilon$. Matrix inverses are taken as $0$ for singular matrices.
