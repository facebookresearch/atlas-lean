# Monotonicity of the posterior in a feature value

In a [naive Bayes model](naive-bayes.md) with finitely many features, let $j$ be a feature and $g : X_j \to \mathbb{R}$ such that $g(v) \le g(v')$ implies $D_j(v)/B_j(v) \le D_j(v')/B_j(v')$. Then for all feature values $x$ and $v, v' \in X_j$ with $g(v) \le g(v')$, the [posterior](posterior.md) of $x$ with $x_j$ replaced by $v$ is at most that with $x_j$ replaced by $v'$.
