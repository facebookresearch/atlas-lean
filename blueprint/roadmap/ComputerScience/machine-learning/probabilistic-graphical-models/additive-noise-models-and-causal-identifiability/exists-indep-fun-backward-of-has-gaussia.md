# A linear Gaussian additive noise model has a backward model

**A linear Gaussian additive noise model has a backward model** (Peters, Mooij, Janzing and
Schölkopf, *Causal discovery with continuous additive noise models*, JMLR 15 (2014),
Example 12 and the "if" direction of Proposition 13). Let $X$ and $N$ be independent real random
variables with Gaussian laws (possibly degenerate), let $\varphi \in \mathbb{R}$ and
$Y = \varphi X + N$. Then there is $\psi \in \mathbb{R}$ such that $\tilde N = X - \psi Y$ is
independent of $Y$; one can take $\psi = \mathrm{Cov}(X, Y) / \mathrm{Var}(Y)$.
