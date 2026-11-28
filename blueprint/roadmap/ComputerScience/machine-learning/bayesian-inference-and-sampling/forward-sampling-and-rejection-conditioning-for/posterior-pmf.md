# Posterior law of a Bayesian network given evidence

Let $B$ be a Bayesian network on the nodes $0, \dots, n-1$ with values in a finite nonempty type $\alpha$ and joint distribution $P$. Let $E$ be a set of evidence nodes and $e$ an evidence assignment with $P(X_E = e_E) = \sum_{x : x_k = e_k\, \forall k \in E} P(x) \ne 0$. The posterior is the probability mass function on $\alpha^n$

$$x \mapsto \begin{cases} \dfrac{P(x)}{P(X_E = e_E)} & \text{if } x_k = e_k \text{ for all } k \in E, \\[1ex] 0 & \text{otherwise.} \end{cases}$$
