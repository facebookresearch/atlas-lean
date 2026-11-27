# Poisson maximum likelihood reconciliation

**Reconciliations.** Let $S$ be a rooted species tree whose node $s$ carries the length $|s|$ of the branch ending at $s$, and $G$ a rooted binary gene tree with LCA mapping $m^*$ into $S$. A node $g$ is an **lca-speciation** if its two children are not mapped to $m^*(g)$. A **reconciliation** is a pair $R = \langle m, \Sigma\rangle$ where $m : V(G) \to V(S)$ is a mapping that respects ancestry and $\Sigma$ is a set of lca-speciations with $m(g) = m^*(g)$ for $g \in \Sigma$; the elements of $\Sigma$ are the speciations of $R$ and every other internal node is a duplication. Let $\mathrm{dup}_R(s)$ be the number of duplications with $m(g) = s$. Reconciliations correspond one-to-one with embeddings of $G$ into $S$ that contain neither a duplication followed immediately by loss of one copy nor a gene lost in all descendants of a speciation, the events that leave no trace in $G$.

**Likelihood.** With a constant duplication rate $\lambda$, the number of duplications on a branch of length $\tau$ is Poisson, $P(\tau, d \mid \lambda) = e^{-\lambda\tau}(\lambda\tau)^d / d!$, and the likelihood of a reconciliation is

$$L(S, G, R) = \prod_{s \in S} P\big(|s|,\ \mathrm{dup}_R(s) \mid \lambda\big).$$

An **optimal reconciliation** maximizes $L$ over all reconciliations of $G$ and $S$.

**Dynamic program.** Define $M(s, \kappa)$ for $s \in S$ and $\kappa$ the number of duplication and speciation nodes placed in the subtree $S(s)$: $M(s,\kappa) = P(|s|, \kappa \mid \lambda)$ at a leaf, and at an internal node with children $s_1, s_2$ a maximum over $\delta$ duplications on the branch ending at $s$, $\sigma$ speciations mapped to $s$, and splits $\kappa = \kappa_1 + \kappa_2 + \sigma + \delta$ restricted to *acceptable triplets* $\langle \sigma, \kappa_1, \kappa_2\rangle$ that some reconciliation realizes, of $p(s,\delta)\, M(s_1, \kappa_1)\, M(s_2, \kappa_2)$.

**Theorem.** If at least one duplication–speciation setting $\langle \mathrm{dup}, \mathrm{spec}\rangle$ reconstructed from the table is realized by some reconciliation, then the maximum likelihood equals $M(\mathrm{root}(S), |L(G)| - 1)$. With cached acceptability queries the table costs $O(|S|\,|G|^4)$ time. Instances where no reconstructed setting is valid ("hard" instances) are handled by branch and bound with constrained re-runs of the recursion.

## Depends on

- [Is LCAReconciliation](../../../not-yet-classified/lcareconciliation/is-lcareconciliation.md)

## Expansion

A binary gene tree with $|L(G)|$ leaves has $|L(G)| - 1$ internal nodes, each either a duplication or a speciation, which is why the root entry is read at $\kappa = |L(G)| - 1$. The recursion is an upper bound because acceptability is checked locally at each species node; it is exact whenever the locally optimal counts glue into a global reconciliation, which in simulations failed in only 0.1–0.4% of random gene trees. Unlike birth–death models, the model places duplications as independent counts on species-tree branches, so any discrete count distribution can replace the Poisson.

## Sources

- P. Górecki, G. J. Burleigh, O. Eulenstein, "Maximum likelihood models and algorithms for gene tree evolution with duplications and losses", BMC Bioinformatics 12 (Suppl 1): S15 (2011), Definitions 1–3, Eq (1), Algorithm DP1 (Eq 2), Theorem 1 and Lemmas 1–2, <https://doi.org/10.1186/1471-2105-12-s1-s15>, PMCID PMC3044269.
