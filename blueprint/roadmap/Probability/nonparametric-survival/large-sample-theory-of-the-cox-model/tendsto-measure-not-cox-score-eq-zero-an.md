# The Cox estimator is eventually a root of the score near the truth

Let $\ell_n$ be the scalar Cox log partial likelihood of the first $n$ subjects, with score $U_n$ and observed information $I_n$, and $\hat\beta_n$ a maximizer whenever one exists. Suppose $U_n(\beta_0)/\sqrt n \Rightarrow Z$, and $I_n(b)/n \to i(b)$ uniformly in probability near $\beta_0$, with $i$ continuous at $\beta_0$ and $i(\beta_0) = v \ne 0$. Then for every $\varepsilon > 0$, the probability that $\hat\beta_n$ is not a root of $U_n$ within $\varepsilon$ of $\beta_0$ tends to $0$.
