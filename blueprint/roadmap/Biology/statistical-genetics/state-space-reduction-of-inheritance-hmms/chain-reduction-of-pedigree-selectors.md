# Chain reduction of pedigree selectors

In the Lander–Green HMM for a pedigree $(V, E)$, each meiosis carries a binary *selector* $S_j$ recording which parental haplotype was transmitted, and the hidden state at a locus is the vector of all selectors. A *chain of length $l$* is a sequence of edges $(v_i, v_{i+1})$, $i = 1,\dots,l$, such that $v_1,\dots,v_l$ are untyped and each has exactly one incoming and one outgoing edge in the pedigree, while $v_{l+1}$ has one incoming edge (and may be typed and have any number of children). Along a chain either an allele is transmitted intact from its start to its end, or a random allele reaches the end.

**Theorem.** Let $S_1,\dots,S_n$ be the selectors of a pedigree and let $C$ be a chain whose edges carry $S_1,\dots,S_l$. Let $S_C$ be the number of $S_1,\dots,S_l$ that are on. Then the likelihood of the marker data can be computed by summing over the states of $(S_C, S_{l+1},\dots,S_n)$, i.e. the $2^l$ joint states of the chain's selectors are replaced by the $l+1$ values of $S_C$.

Applying the reduction to every chain gives exponential savings. For example, in a pedigree of cousins connected to two founders by chains of lengths $t$, $u$, $z$, the full inheritance space of size $2^{t+u+z+4}$ reduces to $2^7\,t\,u\,z$ states; in a pituitary adenoma pedigree with state space $2^{27}$, reducing chains of lengths 2, 3 and 4 gives $2^{18}\cdot 3\cdot 4\cdot 5$ states, an overall reduction by a factor of about 8.5.

## Depends on

- [Lumped forward recursion for hidden Markov models](lumped-forward-recursion-for-hidden-markov-models.md)

## Expansion

Along a chain of untyped individuals the emission probabilities depend only on whether the allele at the start of the chain reaches its end, and clusters of such chains depend only on the number of selectors that block this transmission; this is Condition I for the counting partition of the chain's selectors. Since the selectors flip independently with the recombination fraction between loci, the [counting partition](lumped-forward-recursion-for-hidden-markov-models.md) satisfies Condition II, so the lumped forward recursion applies with $S_C$ in place of $S_1,\dots,S_l$.

## Sources

- D. Geiger, C. Meek, Y. Wexler, "Speeding up HMM algorithms for genetic linkage analysis via chain reductions of the state space", Bioinformatics (2009), Sects. 4–5, Theorem 2, <https://doi.org/10.1093/bioinformatics/btp224>, PMCID PMC2687978.
