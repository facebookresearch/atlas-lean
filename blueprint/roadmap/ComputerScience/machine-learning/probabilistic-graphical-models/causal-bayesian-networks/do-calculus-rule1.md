# Rule 1 of the do-calculus

**Rule 1 of the do-calculus** (insertion and deletion of observations; Pearl 1995,
Theorem 3, eq. (10)): let $B$ be a Bayesian network on the nodes $0, \dots, n - 1$ with values in
a finite nonempty type $\alpha$, let $X, Y, Z, W$ be pairwise disjoint finite sets of nodes and
$x \in \alpha^n$ an assignment, and let $P_x$ be the joint distribution of the
[mutilated network](mutilate-set.md) of $\mathrm{do}(X = x)$, whose graph is $G_{\bar X}$. Write
$P_x(x_U)$ for the sum of $P_x(x')$ over the configurations $x'$ that agree with $x$ on $U$. If
$X \cup W$ d-separates $Y$ from $Z$ in $G_{\bar X}$, $P_x(x_{Z \cup W}) \ne 0$ and
$P_x(x_W) \ne 0$, then

$$\frac{P_x(x_{Y \cup Z \cup W})}{P_x(x_{Z \cup W})} = \frac{P_x(x_{Y \cup W})}{P_x(x_W)},$$

that is, $P(y \mid \mathrm{do}(x), z, w) = P(y \mid \mathrm{do}(x), w)$, with all values read off
the single assignment $x$.

The proof is the global Markov property applied to the mutilated network of
$\mathrm{do}(x)$, whose graph is $G_{\bar X}$ (Pearl 1995, Appendix: deleting equations leaves a
recursive model with independent disturbances, in which d-separation remains valid).
Conditioning on $X$ as well is harmless because the interventional law puts all its mass on
$X = x$.

## Background

- [The back-door adjustment](backdoor-adjustment.md) and
  [the front-door adjustment](frontdoor-adjustment.md): identification formulas of the kind
  that the calculus derives step by step (Pearl 1995, §4).
