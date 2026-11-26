# Delta method with a moving centre

Let $E$ and $F$ be second-countable normed real vector spaces with their Borel σ-algebras, and take limits along a countably generated filter on an index set, with the random variables on probability spaces. Let the scalars $r_n$ tend to $\infty$, let the deterministic centres $c_n \in E$ converge to $\theta$, and let $X_n$ be $E$-valued random variables with $X_n$ and $g(X_n)$ almost everywhere measurable. Suppose $r_n (X_n - c_n)$ converges in distribution to $Z$ and $g : E \to F$ is strictly differentiable at $\theta$ with derivative $L$. Then $r_n (g(X_n) - g(c_n))$ converges in distribution to $L Z$.

Strict differentiability is needed because the increment $g(X_n) - g(c_n)$ is taken between two points that both move towards $\theta$; plain differentiability at $\theta$ controls only increments based at $\theta$. This is the form used for the bootstrap, with $X_n$ the bootstrap statistic and $c_n$ the observed one.
