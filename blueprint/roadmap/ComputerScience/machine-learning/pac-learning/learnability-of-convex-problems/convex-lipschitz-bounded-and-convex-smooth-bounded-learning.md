# Convex-Lipschitz-bounded and convex-smooth-bounded learning problems

This node collects the classes of convex learning problems used for learnability by regularized loss
minimization and stochastic gradient descent.

## Expansion

A sound expansion has separate pages for:

1. **Convex-Lipschitz-bounded problems.** $(H, Z, \ell)$ with $H$ a convex subset of $\mathbb{R}^d$ contained in
   $\{w : \lVert w \rVert \le B\}$ and, for every $z$, $w \mapsto \ell(w, z)$ convex and $\rho$-Lipschitz.
2. **Convex-smooth-bounded problems.** The same bounded convex $H$, with $w \mapsto \ell(w, z)$ convex,
   nonnegative and $\beta$-smooth for every $z$.
3. **Learnability.** For a convex-Lipschitz-bounded problem, regularized loss minimization with
   $\lambda = \sqrt{2\rho^2/(B^2 m)}$ satisfies $\mathbb{E}_S[L_D(A(S))] \le \min_{w \in H} L_D(w) + \rho B\sqrt{8/m}$, so
   $m \ge 8\rho^2 B^2/\varepsilon^2$ samples give excess expected risk at most $\varepsilon$ for every distribution; the
   convex-smooth-bounded case has the analogous guarantee of the source with $\beta B^2$ in place of $\rho^2 B^2$.
   Boundedness is needed: there are convex problems that are not learnable without it.

## Depends on

- [Expected risk](../../generalization-bounds-and-concentration/risk.md)

## Sources

- S. Shalev-Shwartz and S. Ben-David, *Understanding Machine Learning: From Theory to Algorithms*, Cambridge University Press, 2014 (author copy), Section 12.2: Definitions 12.12 and 12.13, the example of a non-learnable convex problem, and Corollaries 13.9–13.11 (learnability by regularized loss minimization; Chapter 14 gives the SGD analogue). <https://www.cs.huji.ac.il/~shais/UnderstandingMachineLearning/understanding-machine-learning-theory-algorithms.pdf>
