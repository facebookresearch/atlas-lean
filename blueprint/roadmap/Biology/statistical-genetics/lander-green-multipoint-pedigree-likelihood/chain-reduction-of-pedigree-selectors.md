# Chain reduction of pedigree selectors

In the Lander–Green HMM for a pedigree $(V, E)$, each meiosis carries a binary *selector* $S_j$ recording which parental haplotype was transmitted, and the hidden state at a locus is the vector of all selectors. A *chain of length $l$* is a sequence of edges $(v_i, v_{i+1})$, $i = 1,\dots,l$, such that $v_1,\dots,v_l$ are untyped and each has exactly one incoming and one outgoing edge in the pedigree, while $v_{l+1}$ has one incoming edge (and may be typed and have any number of children). Along a chain either an allele is transmitted intact from its start to its end, or a random allele reaches the end.

**Theorem.** Let $S_1,\dots,S_n$ be the selectors of a pedigree and let $C$ be a chain whose edges carry $S_1,\dots,S_l$. Call $S_j$ *on* when the meiosis on edge $(v_j, v_{j+1})$ transmits the haplotype that $v_j$ received through its single incoming edge (the choice that continues the directed path from the chain's source to its sink), and *off* otherwise; whether this is the paternal or the maternal haplotype of $v_j$ depends on the sex of the parent from which $v_j$ received it, so "on" is not a fixed selector value (Geiger et al., Sect. 4.2). Let $S_C$ be the number of $S_1,\dots,S_l$ that are on. Then the likelihood of the marker data can be computed by summing over the states of $(S_C, S_{l+1},\dots,S_n)$, i.e. the $2^l$ joint states of the chain's selectors are replaced by the $l+1$ values of $S_C$.

Applying the reduction to every chain gives exponential savings. For example, in a pedigree of cousins connected to two founders by chains of lengths $t$, $u$, $z$, the full inheritance space of size $2^{t+u+z+4}$ reduces to $2^7\,t\,u\,z$ states; in a pituitary adenoma pedigree with state space $2^{27}$, reducing chains of lengths 2, 3 and 4 gives $2^{18}\cdot 3\cdot 4\cdot 5$ states, an overall reduction by a factor of about 8.5.

## Depends on

- [Inheritance Vector](inheritance-vector.md)
- [Transition](transition.md)
- [Likelihood](likelihood.md)

## Proof depends on

- [The Lander–Green forward recursion](likelihood-eq-forward.md)
- [Strong lumpability onto the image of a finite Markov chain](../../../Probability/markov-chains/finite-markov-chains/strong-lumpability-of-finite-markov-chains.md)

## Expansion

Group the joint states of $S_1,\dots,S_l$ by the number $S_C$ of selectors that are on. Along a chain of untyped individuals the emission probabilities depend only on whether the allele at the start of the chain reaches its end, which happens exactly when all $l$ selectors are on ($S_C = l$), so states with the same $S_C$ have the same emission probabilities. Since the selectors flip independently between loci with the recombination fraction $\theta$, the probability of moving from a state with $j$ selectors on to the set of states with $i$ selectors on depends only on $j$:

$$\sum_{t} \binom{j}{t}\binom{l-j}{i-t}\,\theta^{\,i+j-2t}(1-\theta)^{\,l-i-j+2t}.$$

So the selector process is strongly lumpable onto $S_C$, and summing the Lander–Green forward recursion over the members of each class gives a forward recursion on $(S_C, S_{l+1},\dots,S_n)$ with the same total likelihood (Geiger et al., Theorem 1, applied to this counting partition).

## Sources

- D. Geiger, C. Meek, Y. Wexler, "Speeding up HMM algorithms for genetic linkage analysis via chain reductions of the state space", Bioinformatics (2009), Sects. 2–5, Conditions I–II, Theorems 1–2, <https://doi.org/10.1093/bioinformatics/btp224>, PMCID PMC2687978.
