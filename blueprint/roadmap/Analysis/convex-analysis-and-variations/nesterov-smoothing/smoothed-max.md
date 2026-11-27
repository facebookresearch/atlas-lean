# Nesterov's smoothed max-type function

Let $E, F$ be real inner product spaces, $A : E \to F$ a continuous linear map, $Q \subseteq F$, $\varphi, d : F \to \mathbb{R}$ and $\mu \ge 0$. The smoothed max-type function is

$$
f_\mu(x) = \sup_{u \in Q} \big(\langle A x, u\rangle - \varphi(u) - \mu\, d(u)\big),
$$

and $f_0(x) = \sup_{u \in Q} (\langle A x, u\rangle - \varphi(u))$ is the nonsmooth function it approximates. In the source, $Q$ is bounded, closed and convex, $\varphi$ is continuous and convex, and $d$ is a prox-function of $Q$ (continuous and strongly convex, with minimum $0$), so the supremum is a maximum. The supremum is taken in $\mathbb{R}$, where an empty set or a set unbounded above has supremum $0$: it is meaningful only when the values are bounded above (for instance $Q$ compact with $\varphi, d$ continuous on $Q$). The source uses general norms and their duals on finite-dimensional spaces; the definition above uses inner products.

Many nonsmooth convex functions have this form, for example $\|x\|_1 = \max_{\|u\|_\infty \le 1} \langle x, u\rangle$ and $\max_i x_i = \max_{u \in \Delta} \langle x, u\rangle$ over the simplex; with $d(u) = \frac{1}{2}\|u\|^2$ the first gives a sum of Huber functions.

## Sources

- Yu. Nesterov, *Smooth minimization of non-smooth functions*, Math. Program. 103 (2005) 127–152, Section 2: the model (2.2), the prox-function (2.4) and the function $f_\mu$ of (2.5), which this page defines.
