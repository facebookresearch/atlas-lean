# RGSep assertions over local and shared state

RGSep assertions are defined over a thread's local heap and the shared heap at once: unboxed separation-logic formulas describe the local heap, and boxed formulas $\boxed{P}$ describe the shared heap, read through the rely. The connective $\ast$ splits the local heap but not the shared one.

Use the heaps, separation-logic assertions and rely conditions of [actions and interference in RGSep](rgsep-actions-and-interference.md). For a relation $R$ on heaps, the *weakest stable stronger assertion* $\mathrm{wssa}_R(Q)$ of a separation-logic assertion $Q$ is the weakest assertion that is stronger than $Q$ and stable under $R$:

1. $\mathrm{wssa}_R(Q) \Rightarrow Q$;
2. $\mathrm{wssa}_R(Q); R \Longrightarrow \mathrm{wssa}_R(Q)$; and
3. for every $P$, if $P; R \Longrightarrow P$ and $P \Rightarrow Q$, then $P \Rightarrow \mathrm{wssa}_R(Q)$.

RGSep assertions are given by

$$p, q, r ::= P \mid \boxed{P} \mid p \ast q \mid p \wedge q \mid p \vee q \mid \exists x.\, p \mid \forall x.\, p,$$

with $P$ ranging over separation-logic assertions. A state is a pair of a local heap $l$ and a shared heap $s$ with $l \uplus s$ defined. Satisfaction is relative to a rely $\mathcal{R}$:

- $l, s, i \models_{\mathcal{R}} P$ iff $l, i \models_{SL} P$;
- $l, s, i \models_{\mathcal{R}} \boxed{P}$ iff $l = \emptyset$ and $s, i \models_{SL} \mathrm{wssa}_{[\![\mathcal{R}]\!]}(P)$;
- $l, s, i \models_{\mathcal{R}} p_1 \ast p_2$ iff $l = l_1 \uplus l_2$ for some $l_1, l_2$ with $l_1, s, i \models_{\mathcal{R}} p_1$ and $l_2, s, i \models_{\mathcal{R}} p_2$;
- $\wedge$, $\vee$, $\exists$ and $\forall$ are interpreted pointwise, quantifiers ranging over values of logical variables.

So $\boxed{P} \ast \boxed{Q}$ implies $\boxed{P \wedge Q}$. An RGSep assertion is *stable under* a set of actions $\mathcal{R}$ when every boxed subformula $\boxed{P}$ has $P; [\![\mathcal{R}]\!] \Longrightarrow P$, unboxed formulas being always stable. The source states two facts:

1. if $l, s, i \models_{\mathcal{R}} p$, $s' \uplus l$ is defined and $(s, s') \in [\![\mathcal{R}]\!]$, then $l, s', i \models_{\mathcal{R}} p$;
2. if $l, s, i \models_{\mathcal{R}} p$, $[\![\mathcal{R}]\!] \subseteq [\![\mathcal{R}']\!]$ and $p$ is stable under $\mathcal{R}'$, then $l, s, i \models_{\mathcal{R}'} p$.

## Depends on

- [Actions and interference in RGSep](rgsep-actions-and-interference.md)

## Proof depends on

None.

## Expansion

A development needs the existence of $\mathrm{wssa}_R(Q)$ for the relations $[\![\mathcal{R}]\!]$ that arise, and proofs of the two facts, which the source states as Lemmas 3 and 4 (conference numbering). The extended technical report prints the clause for $\boxed{P}$ without $\mathrm{wssa}$; this page follows the conference version.

## Sources

- V. Vafeiadis and M. Parkinson, "A marriage of rely/guarantee and separation logic", *CONCUR 2007 – Concurrency Theory*, LNCS 4703, Springer, 2007, pp. 256–271, <https://doi.org/10.1007/978-3-540-74407-8_18>, author copy <https://www.mpi-sws.org/~viktor/papers/concur2007-marriage.pdf>: Section 3.2 (Definition 2, weakest stable stronger assertion) and Section 3.3 (syntax and semantics of assertions, Lemma 3, Definition 3, Lemma 4, entailments for boxed assertions).
- V. Vafeiadis and M. Parkinson, *A marriage of rely/guarantee and separation logic*, Technical Report UCAM-CL-TR-687, University of Cambridge Computer Laboratory, June 2007, <https://www.cl.cam.ac.uk/techreports/UCAM-CL-TR-687.pdf>: Section 3.3 (semantics of assertions including the quantifier clauses, Lemma 5, Definition 6, Lemma 7).
