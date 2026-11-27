# A map between seminormed spaces is linear and continuous if and only if it is linear and bounded

Let $X$ and $Y$ be seminormed vector spaces over a nontrivially normed field $\mathbb{K}$, for instance normed spaces over $\mathbb{R}$ or $\mathbb{C}$, and let $T \colon X \to Y$ be a map. Then $T$ is linear and continuous, for the topologies that the seminorms induce, if and only if $T$ is linear and bounded: there is a real number $M > 0$ with $\|Tx\| \le M\|x\|$ for all $x \in X$.

## Sources

- John B. Conway, A Course in Functional Analysis, 2nd ed., Graduate Texts in Mathematics 96, Springer, 1990.
- The mathlib Community, *mathlib4* at revision fc4f59e577feb1a4956671bc04ac18aaaf8cd842, for bounded linear maps: `IsBoundedLinearMap`, https://github.com/leanprover-community/mathlib4/blob/fc4f59e577feb1a4956671bc04ac18aaaf8cd842/Mathlib/Analysis/Normed/Operator/BoundedLinearMaps.lean#L81-L84.
