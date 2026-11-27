# Minimal occurrences of a term are originating

**Lemma.** Let $\mathcal C$ be a [bundle](bundles-in-a-strand-space.md), $t$ a term and $n$ a $\preceq_{\mathcal C}$-minimal element of
$\{m \in \mathcal C \mid t \sqsubset \mathrm{term}(m)\}$. Then $t$ [originates](strand-spaces.md) on $n$.

The node $n$ is positive by [the previous lemma](minimal-nodes-of-term-closed-sets-are-positive.md), and its strand predecessors, which lie in the bundle, do not
contain $t$ by minimality.

## Depends on

- [Bundles in a strand space](bundles-in-a-strand-space.md)

## Proof depends on

- [Minimal nodes of term-closed sets are positive](minimal-nodes-of-term-closed-sets-are-positive.md)

## Sources

- F. J. Thayer Fábrega, J. C. Herzog and J. D. Guttman, "Strand spaces: proving security protocols correct", *Journal of Computer Security* 7:191–230, 1999, copy at <http://web.cs.wpi.edu/~guttman/pubs/jcs_strand_spaces.pdf>: Section 2.2, Lemma 2.9 and its proof.
