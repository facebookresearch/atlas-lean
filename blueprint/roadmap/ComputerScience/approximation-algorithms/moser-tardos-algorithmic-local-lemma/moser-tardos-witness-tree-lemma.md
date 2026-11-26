# Moser-Tardos witness tree lemma

To each step of a valid log of the Moser-Tardos algorithm attach its *witness tree*: scan the earlier steps backwards and attach each earlier resampled event below the deepest vertex whose label is equal or adjacent to it; record the tree by its set $S$ of (label, depth) pairs. A structure is *proper* if no two vertices at the same depth have equal or adjacent labels. Every witness tree is proper, and for every fixed proper structure $S$,

$$
\Pr[S \text{ occurs as the witness tree of some step}] \le \prod_{(i, d) \in S} \Pr[A_i].
$$

Moreover, if each $A_i$ satisfies $\Pr[A_i] \le x_i \prod_{j \in \Gamma(i)} (1 - x_j)$ with $x_j \in [0,1)$ and $\Gamma(i)$ containing all events adjacent to $A_i$, then the sum of $\prod_{(j,d)\in S}\Pr[A_j]$ over all proper structures rooted at $i$ is at most $x_i/(1-x_i)$.

## Proof sketch

Couple the tree with the table: if $S$ is the witness tree of a step, each vertex's event holds on the assignment that reads, for each of its variables, the next sample after those consumed by deeper vertices; properness makes these readings use distinct table entries, so the checks are independent and the probability is the product. The sum over structures is bounded by induction on depth, charging a factor $\prod_{j \in \Gamma(i)\cup\{i\}}(1-x_j)^{-1}$ to each label on the deepest level to pay for all choices of children (the paper compares with a Galton-Watson process).

## Depends on

- [Moser-Tardos resampling algorithm in the variable model](moser-tardos-algorithm.md)

## Proof depends on

- [Moser-Tardos resampling algorithm in the variable model](moser-tardos-algorithm.md)

## Sources

- Robin A. Moser and Gábor Tardos, "A Constructive Proof of the General Lovász Local Lemma", Journal of the ACM 57(2), 2010.
