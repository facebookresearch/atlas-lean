# Linear bandits

In a stochastic linear bandit the learner chooses in each round an action $A_t \in \mathbb{R}^d$ and observes a reward with mean $\langle \theta^*, A_t \rangle$ for an unknown parameter $\theta^*$. Optimistic algorithms such as LinUCB act on a confidence ellipsoid around the regularized least-squares estimate of $\theta^*$, whose shape is given by the Gram matrix $V_t = V_0 + \sum_{s \le t} A_s A_s^{\mathsf T}$ of the actions. The elliptical potential lemma bounds the sum over the rounds of $\min(1, \lVert A_t \rVert_{V_{t-1}^{-1}}^2)$ by twice the logarithm of the determinant ratio $\det V_n / \det V_0$; it is a main step of the regret bound of LinUCB (Lattimore and Szepesvári, *Bandit Algorithms*, 2020, Chapters 19 and 20).

The lemma's page numbers the actions from $1$, as the book does. The pages on the Gram matrix and its potentials number them from $0$: their $a_k$ is the action of round $k + 1$, and their $V_k = V_0 + \sum_{j < k} a_j a_j^{\mathsf T}$ is the Gram matrix of the actions before $a_k$.

- [Elliptical potential lemma](elliptical-potential-lemma.md)
- [Stochastic linear bandits and LinUCB regret](stochastic-linear-bandits-and-linucb-regret.md)

## Related topics

- [The information matrix is positive definite](../../../../../Analysis/control-theory/recursive-least-squares/pos-def-rls-information.md): with $P_0 = V_0^{-1}$ its information matrix is the Gram matrix $V_t$, so it also states that $V_t$ is positive definite when $V_0$ is.
