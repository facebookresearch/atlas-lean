# Counterfactual probability given evidence

**Counterfactual probability given evidence** (Pearl, *Statistics Surveys* 2009, §3.4, the
computation of $P(Y_{x_1} = y_1 \mid Y = y_0, X = x_0)$ following eq. (28)): let $M$ be a
Markovian structural causal model on the nodes $0, \dots, n - 1$ with values in a finite set
$\alpha$, disturbances in a finite set $\beta$ with product law
$\pi(u) = \prod_k \pi_k(u_k)$, solution $X(u)$ and law $P$. For a finite set $W$ of nodes,
$w \in \alpha^n$, an event $E \subseteq \alpha^n$ with $P(E) > 0$ and an event
$Y \subseteq \alpha^n$, the counterfactual probability of $Y$ under $\mathrm{do}(X_W = w)$ given
$E$ is

$$\frac{\sum_{u \in \beta^n} \pi(u) \, \mathbf{1}[X(u) \in E] \, \mathbf{1}[X_{W \leftarrow w}(u) \in Y]}{\sum_{u \in \beta^n} \pi(u) \, \mathbf{1}[X(u) \in E]},$$

the probability that $Y$ holds for the [counterfactual values](counterfactual.md)
$X_{W \leftarrow w}(u)$, under the law of the disturbances conditioned on the event that the
factual values $X(u)$ lie in $E$.
