# Linear and semilinear sets of vectors

A set $X \subseteq \mathbb{N}^k$ is *linear* if there are a vector $r \in \mathbb{N}^k$, the root, and a finite set $Q \subseteq \mathbb{N}^k$ of periods such that $X = \{ r + \sum_{q \in Q} \lambda_q q \mid \lambda_q \in \mathbb{N} \text{ for every } q \in Q \}$. A set is *semilinear* if it is a finite union of linear sets; it is given by the finite list of roots and period sets of its linear sets. For a Petri net with places $s_1, \dots, s_k$, a set of markings is semilinear when the corresponding set of vectors in $\mathbb{N}^k$ is.

## Depends on

- [Place/transition Petri nets](../place-transition-petri-nets.md)

## Sources

- J. Esparza, *Petri Nets*, lecture notes, Technical University of Munich, version of 18 June 2019, <https://archive.model.in.tum.de/um/courses/petri/SS2019/PNSkript.pdf>, Definition 3.2.23 and the remark after it, pp. 65–66.
