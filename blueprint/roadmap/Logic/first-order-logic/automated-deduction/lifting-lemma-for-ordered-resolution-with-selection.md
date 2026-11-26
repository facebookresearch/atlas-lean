# Lifting lemma for ordered resolution with selection

Let $\succ$ and $\mathrm{sel}$ be as in [ordered resolution with selection](ordered-resolution-with-selection.md), and let $D$ and $C$ be clauses without common variables, and $\theta_1$, $\theta_2$ substitutions such that $D\theta_1$ and $C\theta_2$ are ground. Suppose $\mathrm{sel}(D\theta_1)$ consists of the instances of the literal occurrences in $\mathrm{sel}(D)$, and likewise $\mathrm{sel}(C\theta_2)$ of those in $\mathrm{sel}(C)$.

1. *Resolution.* If $C'$ is the conclusion of an ordered resolution inference with selection from $D\theta_1$ and $C\theta_2$, then there are an ordered resolution inference with selection from $D$ and $C$ with conclusion $C''$ and a substitution $\rho$ with $C' = C''\rho$.
2. *Factorization.* If $C'$ is the conclusion of an ordered factorization inference with selection from $D\theta_1$, then there are an ordered factorization inference with selection from $D$ with conclusion $C''$ and a substitution $\rho$ with $C' = C''\rho$.

Together the two parts cover every inference of $\mathrm{Res}^\succ_{\mathrm{sel}}$.

**Proof idea.** For part 1, as $D$ and $C$ share no variables, $\theta_1$ and $\theta_2$ combine into one substitution $\theta$, which unifies the two atoms resolved upon and so factors as $\sigma\rho$ through their most general unifier $\sigma$. The ordering conditions on the ground inference imply the non-ground ones for $\sigma$: if $B\sigma \preceq L\sigma$, then $B\theta \preceq L\theta$ by stability under substitutions. The selection conditions transfer because corresponding literals are selected. Part 2 is the same argument with $\theta_1$ unifying the two atoms that are merged.

## Depends on

- [Ordered resolution with selection](ordered-resolution-with-selection.md)

## Proof depends on

- [Unification returns a most general unifier](../first-order-unification/is-mgu-unify.md)

## Sources

- U. Waldmann, *Automated Reasoning*, lecture notes, Max Planck Institute for Informatics, winter semester 2019/20, <https://rg1-teaching.mpi-inf.mpg.de/autrea-ws19/script.pdf>, Section 3.13, Lemma 3.40 (lifting lemma for $\mathrm{Res}^\succ_{\mathrm{sel}}$) and the remark that an analogous lifting lemma holds for factorization, p. 85.
