# Generalization bound for norm-bounded linear predictors with Lipschitz loss

Let $\mathcal{H} = \{w : \|w\|_2 \le B\}$ and let $\mathcal{D}$ be a distribution with $\|x\|_2 \le R$ almost surely.
Let the loss have the form $\ell(w,(x,y)) = \phi(\langle w,x\rangle, y)$ for a function $\phi : \mathbb{R} \times \mathcal{Y} \to \mathbb{R}$, where $a \mapsto \phi(a,y)$ is $\rho$-Lipschitz for every
$y$ and $|\phi(a,y)| \le c$ for all $a \in [-BR, BR]$. Then for every $\delta \in (0,1)$, with probability at least
$1-\delta$ over a sample $S$ of $m \ge 1$ independent examples from $\mathcal{D}$, for all $w \in \mathcal{H}$,

$$L_\mathcal{D}(w) \le L_S(w) + \frac{2\rho B R}{\sqrt{m}} + c\sqrt{\frac{2\ln(2/\delta)}{m}}.$$


## Expansion

This node states a precise result. A good expansion adds a page for each of the following
prerequisites and links it under the dependency sections below:

- Proof prerequisite: the uniform convergence bound $L_\mathcal{D}(w) \le L_S(w) + 2\,\mathbb{E}\,\mathcal{R}(\ell \circ \mathcal{H} \circ S) + c\sqrt{2\ln(2/\delta)/m}$ for losses bounded by $c$, from McDiarmid's inequality, for the uncountable norm-ball class (including the measurability step from countable classes).

## Proof depends on

- [The contraction lemma](rademacher-complexity/rademacher-complexity-coord-map-le.md)
- [Rademacher average of a ball of linear predictors](rademacher-average-linear-ball-le.md)

## Sources

- S. Shalev-Shwartz and S. Ben-David, *Understanding Machine Learning: From Theory to Algorithms*, Cambridge University Press, 2014 (author copy), Theorem 26.12. <https://www.cs.huji.ac.il/~shais/UnderstandingMachineLearning/understanding-machine-learning-theory-algorithms.pdf>
