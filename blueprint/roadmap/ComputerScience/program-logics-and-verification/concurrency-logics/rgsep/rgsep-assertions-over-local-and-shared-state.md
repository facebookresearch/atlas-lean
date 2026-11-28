# RGSep assertions over local and shared state

RGSep assertions describe a thread's local heap and the shared heap at once: unboxed separation-logic formulas describe the local heap and boxed formulas $\boxed{P}$ the shared heap. The connective $\ast$ splits the local heap but not the shared one.

Use the separation algebra $(M, \uplus, \emptyset)$, the separation-logic assertions and stability of [actions and interference in RGSep](rgsep-actions-and-interference.md). RGSep assertions are given by

$$p, q, r ::= P \mid \boxed{P} \mid p \ast q \mid p \wedge q \mid p \vee q \mid \exists x.\, p \mid \forall x.\, p,$$

with $P$ ranging over separation-logic assertions; boxes are not nested and there is no top-level negation. They are interpreted over triples $(l, s, i)$ of a local heap $l \in M$, a shared heap $s \in M$ with $l \uplus s$ defined, and an interpretation $i$ of the logical variables:

- $l, s, i \models P$ iff $l, i \models_{SL} P$;
- $l, s, i \models \boxed{P}$ iff $l = \emptyset$ and $s, i \models_{SL} P$;
- $l, s, i \models p_1 \ast p_2$ iff $l = l_1 \uplus l_2$ for some $l_1, l_2$ with $l_1, s, i \models p_1$ and $l_2, s, i \models p_2$;
- $\wedge$ and $\vee$ are interpreted pointwise, and $\exists x$ and $\forall x$ quantify over the value of the logical variable $x$.

So $\boxed{P} \ast \boxed{Q}$ is equivalent to $\boxed{P \wedge Q}$. An RGSep assertion is *stable under* a set of actions $\mathcal{R}$, defined by induction: a local assertion $P$ always is; $\boxed{P}$ is if the separation-logic assertion $P$ is stable under $[\![\mathcal{R}]\!]$; $p \ast q$, $p \wedge q$ and $p \vee q$ are if both $p$ and $q$ are; $\exists x.\, p$ and $\forall x.\, p$ are if $p$ is. A stable assertion is preserved by interference: if $p$ is stable under $\mathcal{R}$, $l, s, i \models p$ and $(s, s') \in [\![\mathcal{R}]\!]$ with $l \uplus s'$ defined, then $l, s', i \models p$.

## Depends on

- [Actions and interference in RGSep](rgsep-actions-and-interference.md)

## Proof depends on

- [Actions and interference in RGSep](rgsep-actions-and-interference.md)

## Expansion

The preservation fact is the thesis's Lemma 15, proved by induction on $p$; its converse fails, since a disjunction of unstable boxed assertions can be equivalent to a stable one. The conference paper interprets $\boxed{P}$ instead as the weakest assertion stronger than $P$ that is stable under the rely; the thesis reads boxes literally, as here, and places the stability checks in the proof rules.

## Sources

- V. Vafeiadis, *Modular fine-grained concurrency verification*, PhD thesis, University of Cambridge, Technical Report UCAM-CL-TR-726, July 2008, <https://www.cl.cam.ac.uk/techreports/UCAM-CL-TR-726.pdf>: Section 3.1.1 (syntax and semantics of RGSep assertions, the equivalence $\boxed{P} \ast \boxed{Q} \iff \boxed{P \wedge Q}$, no nested boxes or top-level negation) and Section 3.1.3 (Definition 14, Lemma 15 and the example after it).
- V. Vafeiadis and M. Parkinson, "A marriage of rely/guarantee and separation logic", *CONCUR 2007 – Concurrency Theory*, LNCS 4703, Springer, 2007, pp. 256–271, <https://doi.org/10.1007/978-3-540-74407-8_18>, author copy <https://www.mpi-sws.org/~viktor/papers/concur2007-marriage.pdf>: Section 3.2 (Definition 2, weakest stable stronger assertion) and Section 3.3 (assertions read through it).
