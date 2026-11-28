# Operational semantics of RGSep programs over structured heaps

RGSep programs run on structured heaps that split the heap into the thread's local part, the shared part and the other threads' part. Primitive commands act on the local part only, atomic blocks merge local and shared state, and environment steps change the shared and environment parts within a rely relation.

Let $(M, \uplus, \emptyset)$ be a [separation algebra](../../separation-logic-metatheory/abstract-separation-logic/separation-algebras.md) of abstract heaps. A *structured heap* is a triple $\sigma = (l, s, o) \in M^3$ with $l \uplus s \uplus o$ defined: the thread's local heap, the shared heap and the other threads' local heaps. Primitive commands are relations $A \subseteq M \times M$ such that (1) if $A(l_1 \uplus l, l_2)$ then either $l_2 = l \uplus l_2'$ for some $l_2'$ with $A(l_1, l_2')$, or no $l'$ has $A(l_1, l')$; and (2) if no $l_2$ has $A(l_1 \uplus l, l_2)$, then no $l_2$ has $A(l_1, l_2)$. Boolean tests are maps $b : M \to \{\mathrm{true}, \mathrm{false}, \mathrm{fault}\}$ such that whenever $b(l_1 \uplus l) = v$, either $b(l_1) = v$ or $b(l_1) = \mathrm{fault}$.

Atomic blocks carry a [precise](../../separation-logic-metatheory/abstract-separation-logic/precise-predicates.md) annotation $Q$, written $\mathbf{atomic}_Q\ (b)\ \{C\}$. For a relation $R$ on heaps, the reduction $(C, \sigma) \xrightarrow{R}_{\lambda} \mathit{Config}$, with label $\lambda = p$ for a program step and $\lambda = e$ for an environment step, and $\mathit{Config}$ either $\mathrm{fault}$ or a pair $(C', \sigma')$, includes:

- a primitive command $A$ steps from $(l, s, o)$ to $(\mathbf{skip}, (l', s, o))$ if $A(l, l')$ and $(l', s, o)$ is a structured heap, and to $\mathrm{fault}$ if no $l'$ has $A(l, l')$;
- an environment step $(C, (l, s, o)) \xrightarrow{R}_{e} (C, (l, s', o'))$ whenever $(s, s') \in R$ and $(l, s', o')$ is a structured heap;
- $\mathbf{atomic}_Q\ (b)\ \{C\}$ steps from $(l, s, o)$ by merging $l_1 = l \uplus s$, requiring $b(l_1)$, running $C$ to $\mathbf{skip}$ from $(l_1, \emptyset, o)$ under the rely $\mathrm{Emp}$ that allows no interference, reaching some $(l_2, \emptyset, o')$, and splitting $l_2 = l' \uplus s'$ with $s'$ satisfying $Q$, to reach $(\mathbf{skip}, (l', s', o'))$; it faults if $b(l_1)$ faults, the body faults, or no such splitting exists;
- parallel composition interleaves the program steps of its components, $\mathbf{skip} \parallel \mathbf{skip}$ steps to $\mathbf{skip}$, and sequencing, conditionals and loops step as usual, faults propagating.

Commands are those of the [RGSep proof rules](rgsep-proof-rules.md), with heap commands given by primitive commands.

## Depends on

- [Separation algebras](../../separation-logic-metatheory/abstract-separation-logic/separation-algebras.md)
- [Precise predicates](../../separation-logic-metatheory/abstract-separation-logic/precise-predicates.md)
- [RGSep proof rules](rgsep-proof-rules.md)

## Proof depends on

None.

## Expansion

The two conditions on primitive commands are the relational form of the locality of abstract separation logic's [local actions](../../separation-logic-metatheory/abstract-separation-logic/local-actions.md). A development fixes the full reduction rules (Figure 5 of the technical report), including the three faulting rules for atomic blocks, and the composition of structured heaps, $(l_1, s, o_1) \uplus (l_2, s, o_2) = (l_1 \uplus l_2, s, o)$ when $o_1 = l_2 \uplus o$ and $o_2 = l_1 \uplus o$.

## Sources

- V. Vafeiadis and M. Parkinson, "A marriage of rely/guarantee and separation logic", *CONCUR 2007 – Concurrency Theory*, LNCS 4703, Springer, 2007, pp. 256–271, <https://doi.org/10.1007/978-3-540-74407-8_18>, author copy <https://www.mpi-sws.org/~viktor/papers/concur2007-marriage.pdf>: Section 5 (Definition 5, structured heaps; Definition 6, primitive commands and boolean tests; Fig. 4, abridged operational semantics; footnote 7, precise assertions).
- V. Vafeiadis and M. Parkinson, *A marriage of rely/guarantee and separation logic*, Technical Report UCAM-CL-TR-687, University of Cambridge Computer Laboratory, June 2007, <https://www.cl.cam.ac.uk/techreports/UCAM-CL-TR-687.pdf>: Section 5 (Definitions 13–17 and Figure 5, full operational semantics).
