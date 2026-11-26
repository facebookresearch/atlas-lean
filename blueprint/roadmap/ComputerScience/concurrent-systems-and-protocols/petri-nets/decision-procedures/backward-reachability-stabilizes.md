# Backward reachability from an upward-closed set stabilizes

Let $\mathcal{M}$ be an [upward-closed set of markings](upward-closed-sets-of-markings.md) of an ordinary Petri net. There is $i \ge 0$ with $\mathrm{pre}^*(\mathcal{M}) = \bigcup_{j=0}^{i} \mathrm{pre}^j(\mathcal{M})$ (see [Predecessor sets of markings](predecessor-sets-of-markings.md)). Consequently the backward algorithm that starts from $\mathcal{M}$, repeatedly adds $\mathrm{pre}$ of the current set and stops when the set no longer grows terminates, and it decides whether $M_0 \in \mathrm{pre}^*(\mathcal{M})$, that is, whether some marking of $\mathcal{M}$ is reachable from $M_0$.

## Depends on

- [Upward-closed sets of markings](upward-closed-sets-of-markings.md)
- [Predecessor sets of markings](predecessor-sets-of-markings.md)

## Proof depends on

- [Predecessors of an upward-closed set of markings are upward closed](predecessors-of-an-upward-closed-set-are-upward-closed.md)
- [Upward-closed sets of markings have finitely many minimal elements](upward-closed-sets-of-markings-have-finitely-many-minimal-elements.md)

## Sources

- J. Esparza, *Petri Nets*, lecture notes, Technical University of Munich, version of 18 June 2019, <https://archive.model.in.tum.de/um/courses/petri/SS2019/PNSkript.pdf>, Theorem 3.2.17 and its proof, pp. 61–62, and the algorithm BACK1 of Figure 3.3 with the paragraph after it, p. 62.
