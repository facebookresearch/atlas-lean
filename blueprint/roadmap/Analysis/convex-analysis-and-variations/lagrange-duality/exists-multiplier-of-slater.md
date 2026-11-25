# Slater's theorem, multiplier form

Throughout, $E$ is a real vector space, $D \subseteq E$, $\iota$ is a finite index set, and the problem is to minimize $f_0(x)$ subject to $x \in D$ and $f_i(x) \le 0$ for $i \in \iota$, with $f_0, f_i \colon E \to \mathbb{R}$. Suppose the problem is convex: $f_0$ and every $f_i$ are convex on $D$ (in particular $D$ is convex). Suppose Slater's condition holds: some $\tilde x \in D$ has $f_i(\tilde x) < 0$ for all $i$. If $p \in \mathbb{R}$ satisfies $p \le f_0(x)$ for every feasible $x$, then there is $\mu \ge 0$ with $p \le L(x, \mu)$ for every $x \in D$, i.e. $p \le g(\mu)$.

Proof: the set $\mathcal{A} = \{(u, t) : \exists x \in D,\ f_i(x) \le u_i \text{ for all } i,\ f_0(x) \le t\}$ is convex and disjoint from the open convex set $\{(u, t) : u < 0,\ t < p\}$, so a nonzero linear functional $(u, t) \mapsto \nu^{\mathsf T} u + \mu_0 t$ separates them. Upward closedness of $\mathcal{A}$ gives $\nu, \mu_0 \ge 0$; Slater's point rules out $\mu_0 = 0$; and $\mu = \nu / \mu_0$ works. Unlike Boyd–Vandenberghe's version, no relative-interior condition on $D$ is needed because there are no equality constraints.

## Background

- [Separation of convex sets by a hyperplane](../../banach-spaces/duality-and-weak-topologies/hahn-banach-theorem/convex-bodies-separated-by-hyperplane.md): background, the geometric Hahn–Banach theorem that the proof applies in the finite-dimensional space of constraint and objective values.

## Sources

- S. Boyd and L. Vandenberghe, *Convex Optimization*, Cambridge University Press, 2004 (https://web.stanford.edu/~boyd/cvxbook/), §5.2.3 (Slater's condition, eq. (5.26)) and §5.3.2 (proof of strong duality via a separating hyperplane), specialized to problems without equality constraints.
