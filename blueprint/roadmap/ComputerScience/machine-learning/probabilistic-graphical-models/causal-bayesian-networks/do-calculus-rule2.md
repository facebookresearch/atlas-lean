# Rule 2 of the do-calculus

**Rule 2 of the do-calculus** (action/observation exchange; Pearl 1995, Theorem 3,
eq. (11)): let $B$ be a Bayesian network on the nodes $0, \dots, n - 1$ with values in a finite
nonempty type $\alpha$, let $X, Y, Z, W$ be pairwise disjoint finite sets of nodes and
$x \in \alpha^n$ an assignment. Let $P_x$ and $P_{x,z}$ be the joint distributions of the
[mutilated networks](mutilate-set.md) of $\mathrm{do}(X = x)$ and of
$\mathrm{do}(X \cup Z = x)$, and write $Q(x_U)$ for the sum of $Q(x')$ over the configurations
$x'$ that agree with $x$ on $U$. If $X \cup W$ d-separates $Y$ from $Z$ in
$G_{\bar X \underline Z}$ (the graph of $B$ with the arrows into $X$ and out of $Z$ deleted),
$P_{x,z}(x_W) \ne 0$ and $P_x(x_{Z \cup W}) \ne 0$, then

$$\frac{P_{x,z}(x_{Y \cup W})}{P_{x,z}(x_W)} = \frac{P_x(x_{Y \cup Z \cup W})}{P_x(x_{Z \cup W})},$$

that is, $P(y \mid \mathrm{do}(x), \mathrm{do}(z), w) = P(y \mid \mathrm{do}(x), z, w)$, with all
values read off the single assignment $x$.

Pearl's proof (Pearl 1995, Appendix, proof of Theorem 3) adds to the diagram an intervention node
$F_z \to z$ for each $z \in Z$ and applies the validity of d-separation in the submodel of
$\mathrm{do}(x)$ to this augmented diagram.

## Background

- [Rule 1 of the do-calculus](do-calculus-rule1.md) and [Rule 3 of the do-calculus](do-calculus-rule3.md):
  the other two rules of the calculus.
