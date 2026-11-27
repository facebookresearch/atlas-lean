# Residuals from the residual-maker matrix

For every design matrix $X$ and observations $y$, $y - X\hat\beta = M y$, where $\hat\beta$ is the ordinary
least-squares estimate and $M$ the residual-maker matrix, both defined with the inverse of a singular
$X^\top X$ taken to be $0$. When $X^\top X$ is invertible, $y - X\hat\beta$ is the vector of
least-squares residuals; when it is singular, $\hat\beta = 0$ and $M y = y$.
