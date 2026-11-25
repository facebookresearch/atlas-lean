# Uniform convergence property and eps-representative samples

Fix a hypothesis class $H$, a loss $\ell$ and a distribution $D$. A sample $S$ of size $m \ge 1$ is
$\varepsilon$-representative if $\sup_{h \in H} \lvert L_S(h) - L_D(h) \rvert \le \varepsilon$. The class $H$ has the uniform
convergence property with sample complexity $m^{UC}_H : (0,1)^2 \to \mathbb{N}$ if for all $\varepsilon, \delta \in (0,1)$,
every distribution $D$ and every $m \ge m^{UC}_H(\varepsilon, \delta)$, the probability over $S \sim D^m$ that $S$ is
$\varepsilon$-representative is at least $1 - \delta$. The event is assumed measurable, or the probability is read as
an inner probability, by a stated convention.

## Depends on

- [Expected risk](../../generalization-bounds-and-concentration/risk.md)
- [Empirical risk](../../generalization-bounds-and-concentration/empirical-risk.md)

## Sources

- S. Shalev-Shwartz and S. Ben-David, *Understanding Machine Learning: From Theory to Algorithms*, Cambridge University Press, 2014 (author copy), Definitions 4.1 and 4.3. <https://www.cs.huji.ac.il/~shais/UnderstandingMachineLearning/understanding-machine-learning-theory-algorithms.pdf>
