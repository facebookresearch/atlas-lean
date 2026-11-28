# Actions and interference in RGSep

In RGSep, interference on shared state is defined by actions $P \rightsquigarrow Q$: each replaces a part of the shared heap satisfying $P$ by a part satisfying $Q$ and leaves the rest unchanged. Rely and guarantee conditions are finite sets of actions, read as the reflexive-transitive closure of their union.

Fix a [separation algebra](../../separation-logic-metatheory/abstract-separation-logic/separation-algebras.md) $(M, \uplus, \emptyset)$ of heaps, such as finite partial maps from locations to values with union of maps with disjoint domains. A separation-logic assertion $P$ is interpreted as a set of pairs $(h, i)$ of a heap $h \in M$ and an interpretation $i$ of the logical variables; write $h, i \models_{SL} P$. The separating conjunction is

$$h, i \models_{SL} P \ast Q \iff \exists h_1, h_2.\ h_1 \uplus h_2 = h \wedge h_1, i \models_{SL} P \wedge h_2, i \models_{SL} Q.$$

- An *action* is a pair of separation-logic assertions, written $P \rightsquigarrow Q$. Its meaning is the relation on heaps

$$[\![P \rightsquigarrow Q]\!] = \{(h_1 \uplus h_0,\ h_2 \uplus h_0) \mid \exists i.\ h_1, i \models_{SL} P \wedge h_2, i \models_{SL} Q\},$$

  where both disjoint unions must be defined and $h_0$ is the part of the shared heap the action does not touch. The existential quantification over the interpretation $i$ lets $P$ and $Q$ share logical variables, bound with scope over both: in $x \mapsto M \rightsquigarrow x \mapsto N \wedge N \ge M$ the cell $x$ may change but never decreases. When $P$ and $Q$ describe heaps with different domains, the action transfers ownership between the shared state and the local state of the acting thread.
- A *rely condition* or *guarantee condition* is a finite set $\mathcal{R}$ of actions. Its meaning $[\![\mathcal{R}]\!]$ is the reflexive and transitive closure of $\bigcup_{(P \rightsquigarrow Q) \in \mathcal{R}} [\![P \rightsquigarrow Q]\!]$.
- An action $P \rightsquigarrow Q$ is *allowed by* a guarantee $\mathcal{G}$, written $(P \rightsquigarrow Q) \subseteq \mathcal{G}$, if $[\![P \rightsquigarrow Q]\!] \subseteq [\![\mathcal{G}]\!]$.
- A separation-logic assertion $S$ is *stable* under a relation $R$ on heaps, written $S; R \Longrightarrow S$, if for all heaps $s, s'$ and interpretations $i$, $s, i \models_{SL} S$ and $(s, s') \in R$ imply $s', i \models_{SL} S$. It is stable under a set of actions $\mathcal{R}$ if it is stable under $[\![\mathcal{R}]\!]$, equivalently under $[\![a]\!]$ for each action $a \in \mathcal{R}$.

The empty set of actions means no interference: $[\![\emptyset]\!]$ is the identity relation.

## Depends on

- [Separation algebras](../../separation-logic-metatheory/abstract-separation-logic/separation-algebras.md)

## Proof depends on

None.

## Expansion

The equivalence in the last item (stability under a set of actions is stability under each action) is Lemma 2 of the CONCUR paper and the second part of Lemma 13 of the thesis. A development needs the separation-logic assertion language with logical variables and its satisfaction relation over the chosen separation algebra.

## Sources

- V. Vafeiadis and M. Parkinson, "A marriage of rely/guarantee and separation logic", *CONCUR 2007 – Concurrency Theory*, LNCS 4703, Springer, 2007, pp. 256–271, <https://doi.org/10.1007/978-3-540-74407-8_18>, author copy <https://www.mpi-sws.org/~viktor/papers/concur2007-marriage.pdf>: Section 2.1 (semantics of $\ast$), Section 3.1 (actions and their meaning, rely and guarantee as sets of actions), Section 3.2 (Definition 1 and Lemma 2), Section 3.4 (ownership transfer), Section 3.5 (Definition 4) and Section 5 (abstract heaps as a partial commutative cancellative monoid).
- V. Vafeiadis, *Modular fine-grained concurrency verification*, PhD thesis, University of Cambridge, Technical Report UCAM-CL-TR-726, July 2008, <https://www.cl.cam.ac.uk/techreports/UCAM-CL-TR-726.pdf>: Section 3.1.2 (action semantics with the explicit existential quantification over the interpretation, the Increment example, Definition 11) and Section 3.1.3 (Definition 12, stability, and Lemma 13). The conference paper and the 2007 report print the action relation with the interpretation $i$ left free.
- V. Vafeiadis and M. Parkinson, *A marriage of rely/guarantee and separation logic*, Technical Report UCAM-CL-TR-687, University of Cambridge Computer Laboratory, June 2007, <https://www.cl.cam.ac.uk/techreports/UCAM-CL-TR-687.pdf>: Sections 3.1, 3.2 (Definition 1, Lemma 3) and 3.5 (Definition 8).
