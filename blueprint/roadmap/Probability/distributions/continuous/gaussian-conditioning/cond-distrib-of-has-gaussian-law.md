# Gaussian conditioning

Let $E$ and $F$ be finite-dimensional real inner product spaces,
and let $X$ and $Y$ be measurable random vectors in $E$ and $F$ on a probability space such that
$(X, Y)$ is jointly Gaussian. Let $A \colon F \to E$ be a linear map whose residual $X - A Y$ is
uncorrelated with $Y$ (the normal equations): for all $u \in E$ and $w \in F$,
$\operatorname{Cov}(\langle u, X - A Y \rangle, \langle w, Y \rangle) = 0$. Then $X - A Y$ is
Gaussian and independent of $Y$, and for almost every $y$ with respect to the law of $Y$, the
conditional distribution of $X$ given $Y = y$ is the law of $A y + (X - A Y)$.
