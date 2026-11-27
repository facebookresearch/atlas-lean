# Ground instances of a saturated clause set are saturated

Let $\succ$ and $\mathrm{sel}$ be as in [ordered resolution with selection](ordered-resolution-with-selection.md), and let $N$ be a set of clauses that is saturated, $\mathrm{Res}^\succ_{\mathrm{sel}}(N) \subseteq N$. Let $G_\Sigma(N)$ be the set of ground instances of clauses of $N$. Then there is a selection function $\mathrm{sel}'$ that agrees with $\mathrm{sel}$ on $N$ such that $G_\Sigma(N)$ is saturated with respect to $\mathrm{sel}'$: $\mathrm{Res}^\succ_{\mathrm{sel}'}(G_\Sigma(N)) \subseteq G_\Sigma(N)$.

**Proof.** Let $\mathrm{sel}'(C) = \mathrm{sel}(C)$ for $C \in G_\Sigma(N) \cap N$. For $C \in G_\Sigma(N) \setminus N$, choose a fixed clause $D \in N$ of which $C$ is a ground instance and let $\mathrm{sel}'(C)$ consist of the instances of the literal occurrences that $\mathrm{sel}$ selects in $D$. An inference from clauses of $G_\Sigma(N)$ is then, by the lifting lemma, a ground instance of an inference from the chosen clauses of $N$, whose conclusion lies in $N$ by saturation; so its conclusion lies in $G_\Sigma(N)$.

## Depends on

- [Ordered resolution with selection](ordered-resolution-with-selection.md)

## Proof depends on

- [Lifting lemma for ordered resolution with selection](lifting-lemma-for-ordered-resolution-with-selection.md)

## Sources

- U. Waldmann, *Automated Reasoning*, lecture notes, Max Planck Institute for Informatics, winter semester 2019/20, <https://rg1-teaching.mpi-inf.mpg.de/autrea-ws19/script.pdf>, Section 3.13, Corollary 3.41 and its proof, p. 85.
