# Rule 3 of the do-calculus

**Rule 3 of the do-calculus** (insertion and deletion of actions; Pearl 1995, Theorem 3,
eq. (12)): let $B$ be a Bayesian network on the nodes $0, \dots, n - 1$ with values in a finite
nonempty type $\alpha$, let $X, Y, Z, W$ be pairwise disjoint finite sets of nodes and
$x \in \alpha^n$ an assignment. Let $P_x$ and $P_{x,z}$ be the joint distributions of the
[mutilated networks](mutilate-set.md) of $\mathrm{do}(X = x)$ and of
$\mathrm{do}(X \cup Z = x)$, and write $Q(x_U)$ for the sum of $Q(x')$ over the configurations
$x'$ that agree with $x$ on $U$. Let $Z(W)$ be the set of nodes of $Z$ that are not ancestors of
any node of $W$ in $G_{\bar X}$. If $X \cup W$ d-separates $Y$ from $Z$ in
$G_{\bar X, \overline{Z(W)}}$ (arrows into $X$ and into $Z(W)$ deleted), $P_{x,z}(x_W) \ne 0$ and
$P_x(x_W) \ne 0$, then

$$\frac{P_{x,z}(x_{Y \cup W})}{P_{x,z}(x_W)} = \frac{P_x(x_{Y \cup W})}{P_x(x_W)},$$

that is, $P(y \mid \mathrm{do}(x), \mathrm{do}(z), w) = P(y \mid \mathrm{do}(x), w)$, with all
values read off the single assignment $x$.

Pearl's proof (Pearl 1995, Appendix, proof of Theorem 3) adds to the diagram an intervention node
$F_z \to z$ for each $z \in Z$ and applies the validity of d-separation in the submodel of
$\mathrm{do}(x)$ to this augmented diagram.

## Informally uses

- [The global Markov property](../bayesian-networks/cond-indep-of-d-separated.md): d-separation
  in the augmented diagram implies the conditional independence that equates the two sides.

## Background

- [The truncated factorization for a set of nodes](joint-mutilate-set.md): the law of the
  submodels of $\mathrm{do}(x)$ and of $\mathrm{do}(x, z)$ that the rule compares.
