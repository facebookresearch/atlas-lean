# Fixed-margin Rademacher generalization bound

Let $\alpha$ be a finite set, $D$ a probability distribution on $\alpha \times \{\pm 1\}$, and $H$ a uniformly bounded class of functions $\alpha \to \mathbb{R}$. For a margin $\rho > 0$ let $\Phi_\rho(u) = \min(1, \max(0, 1 - u/\rho))$ be the $\rho$-margin loss and $\hat{R}_{S,\rho}(h) = \frac{1}{m}\sum_i \Phi_\rho(y_i h(x_i))$ the empirical margin loss on $S = ((x_i, y_i))_{i \le m}$; $R_m(H)$ is the Rademacher complexity of $H$ under the marginal of $D$ on $\alpha$ and $\hat{R}_{S_X}(H)$ its empirical Rademacher complexity on the unlabelled points of $S$.
The $\rho$-margin loss satisfies $[u \le 0] \le \Phi_\rho(u) \le [u \le \rho]$ and is $1/\rho$-Lipschitz, so by the contraction lemma the margin-loss class $\{(x,y) \mapsto \Phi_\rho(y h(x)) : h \in H\}$ has (empirical) Rademacher complexity at most $1/\rho$ times that of $H$. For $m > 0$ and $\delta \in (0,1)$, with probability at least $1-\delta$ over $S \sim D^m$, every $h \in H$ satisfies

$$
\Pr_{D}[y\,h(x) \le 0] \le \hat{R}_{S,\rho}(h) + \frac{2}{\rho}R_m(H) + \sqrt{\frac{\ln(1/\delta)}{2m}},
$$

and also the data-dependent bound with $\frac{2}{\rho}\hat{R}_{S_X}(H) + 3\sqrt{\ln(2/\delta)/(2m)}$. For a finite class with values in $[-B, B]$ the complexity term may be replaced by $\frac{2B}{\rho}\sqrt{2\ln|H|/m}$, and for linear predictors $x \mapsto \langle w, \phi(x)\rangle$ with $\|w\| \le B$ and $\|\phi(x)\| \le R$ by $\frac{2BR}{\rho\sqrt{m}}$.

## Proof sketch

Apply the Rademacher generalization bound to the $[0,1]$-valued margin-loss class, bound its complexity by the contraction lemma with Lipschitz constant $1/\rho$, and use $[u \le 0] \le \Phi_\rho(u)$ on the left side. The finite and linear cases plug in Massart's lemma and the Cauchy-Schwarz bound $BR/\sqrt{m}$.

## Depends on

- [The ramp cost](../rademacher-complexity/ramp.md)
- [The contraction lemma](../rademacher-complexity/rademacher-complexity-coord-map-le.md)
- [Rademacher generalization bound for bounded function classes](rademacher-generalization-bound.md)
- [Rademacher average of a ball of linear predictors](../rademacher-average-linear-ball-le.md)

## Proof depends on

- [Rademacher generalization bound for bounded function classes](rademacher-generalization-bound.md)
- [The contraction lemma](../rademacher-complexity/rademacher-complexity-coord-map-le.md)
- [Massart's finite-class lemma](../rademacher-complexity/rademacher-complexity-le-of-finite.md)
- [Rademacher average of a ball of linear predictors](../rademacher-average-linear-ball-le.md)

## Sources

- M. Mohri, A. Rostamizadeh and A. Talwalkar, "Foundations of Machine Learning", 2nd edition, MIT Press, 2018.
- V. Koltchinskii and D. Panchenko, "Empirical Margin Distributions and Bounding the Generalization Error of Combined Classifiers", The Annals of Statistics, 2002.
