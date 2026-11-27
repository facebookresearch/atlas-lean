# Normed vector space

Let $\mathbb{K}$ be a normed field, for instance $\mathbb{R}$ or $\mathbb{C}$ with the absolute value, let $X$ be a vector space over $\mathbb{K}$, and let $\|\cdot\| \colon X \to \mathbb{R}$ be a function. The function $\|\cdot\|$ is a *norm* on $X$, and $(X, \|\cdot\|)$ is a *normed space* over $\mathbb{K}$, if the following hold for all $x, y \in X$ and $\alpha \in \mathbb{K}$:

- $\|x\| \ge 0$;
- $\|\alpha x\| = |\alpha| \, \|x\|$;
- $\|x + y\| \le \|x\| + \|y\|$;
- $\|x\| = 0$ only when $x = 0$.

Completeness is not required.

## Sources

- John B. Conway, A Course in Functional Analysis, 2nd ed., Graduate Texts in Mathematics 96, Springer, 1990.
- The mathlib Community, *mathlib4* at revision fc4f59e577feb1a4956671bc04ac18aaaf8cd842, for nonnegativity, the scaling identity and the triangle inequality: `SeminormedSpace.Core`, https://github.com/leanprover-community/mathlib4/blob/fc4f59e577feb1a4956671bc04ac18aaaf8cd842/Mathlib/Analysis/Normed/Module/Basic.lean#L573-L580.
- The mathlib Community, *mathlib4* at revision fc4f59e577feb1a4956671bc04ac18aaaf8cd842, for the condition that only the zero vector has norm $0$: `NormedSpace.Core`, https://github.com/leanprover-community/mathlib4/blob/fc4f59e577feb1a4956671bc04ac18aaaf8cd842/Mathlib/Analysis/Normed/Module/Basic.lean#L697-L703.
