# One Runge–Kutta step

Let $E$ be a real normed vector space and $f(t, y)$ a vector
field $\mathbb{R} \times E \to E$. For an explicit Runge–Kutta method with weights $b$, a
time $t$, a state $y \in E$ and a step size $h \in \mathbb{R}$, one step of the method
is $y + h \sum_i b_i k_i$, where $k_i$ is the $i$-th stage of the method for $f$, $t$, $y$
and $h$, and the sum runs over the stages.
