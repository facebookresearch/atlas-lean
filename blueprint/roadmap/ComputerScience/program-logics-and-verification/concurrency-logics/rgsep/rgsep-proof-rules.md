# RGSep proof rules

RGSep derives judgments $\vdash C\ \mathbf{sat}\ (p, \mathcal{R}, \mathcal{G}, q)$ for commands built from primitive commands by sequencing, choice, iteration, atomic blocks and parallel composition: started in a state satisfying $p$, under interference within $\mathcal{R}$, $C$ does not fault, changes shared state only within $\mathcal{G}$, and establishes $q$ if it terminates.

Fix the separation algebra $(M, \uplus, \emptyset)$ of [actions and interference in RGSep](rgsep-actions-and-interference.md). *Primitive commands* $c$ are relations $c \subseteq M \times M$; $c$ *faults* at $m$ if no $m'$ has $c(m, m')$. Each satisfies locality: if $c$ faults at $m_1 \uplus m$, it faults at $m_1$; and if $c(m_1 \uplus m, m_2)$, then either $c$ faults at $m_1$ or $m_2 = m_2' \uplus m$ for some $m_2'$ with $c(m_1, m_2')$. A separation-logic triple $\{P\}\, c\, \{Q\}$ is *valid* for $c$ if for every $m$ and interpretation $i$ with $m, i \models_{SL} P$, $c$ does not fault at $m$ and every $m'$ with $c(m, m')$ has $m', i \models_{SL} Q$. Commands are

$$C ::= \mathbf{skip} \mid c \mid C_1 ; C_2 \mid C_1 + C_2 \mid C^\ast \mid \langle C \rangle_{P \rightsquigarrow Q} \mid C_1 \parallel C_2,$$

where $+$ is nondeterministic choice, $^\ast$ iteration, and the atomic block $\langle C \rangle_{P \rightsquigarrow Q}$ is annotated with [precise](../../separation-logic-metatheory/abstract-separation-logic/precise-predicates.md) separation-logic assertions $P, Q$. Assertions $p, q, r$ and their stability are those of [RGSep assertions over local and shared state](rgsep-assertions-over-local-and-shared-state.md); $\mathcal{R}, \mathcal{G}$ are sets of actions, and $(P \rightsquigarrow Q) \subseteq \mathcal{G}$ is as in [actions and interference in RGSep](rgsep-actions-and-interference.md). The rules are:

- *Prim.* If $\{P\}\, c\, \{Q\}$ is valid for $c$, then $\vdash c\ \mathbf{sat}\ (P, \mathcal{R}, \mathcal{G}, Q)$ for the local assertions $P, Q$.
- *Skip.* If $p$ is stable under $\mathcal{R}$, then $\vdash \mathbf{skip}\ \mathbf{sat}\ (p, \mathcal{R}, \mathcal{G}, p)$.
- *Seq.* From $\vdash C_1\ \mathbf{sat}\ (p, \mathcal{R}, \mathcal{G}, r)$ and $\vdash C_2\ \mathbf{sat}\ (r, \mathcal{R}, \mathcal{G}, q)$ infer $\vdash C_1 ; C_2\ \mathbf{sat}\ (p, \mathcal{R}, \mathcal{G}, q)$.
- *Choice.* From $\vdash C_1\ \mathbf{sat}\ (p, \mathcal{R}, \mathcal{G}, q)$ and $\vdash C_2\ \mathbf{sat}\ (p, \mathcal{R}, \mathcal{G}, q)$ infer $\vdash C_1 + C_2\ \mathbf{sat}\ (p, \mathcal{R}, \mathcal{G}, q)$.
- *Loop.* From $\vdash C\ \mathbf{sat}\ (p, \mathcal{R}, \mathcal{G}, p)$ infer $\vdash C^\ast\ \mathbf{sat}\ (p, \mathcal{R}, \mathcal{G}, p)$.
- *Par.* From $\vdash C_1\ \mathbf{sat}\ (p_1, \mathcal{R} \cup \mathcal{G}_2, \mathcal{G}_1, q_1)$ and $\vdash C_2\ \mathbf{sat}\ (p_2, \mathcal{R} \cup \mathcal{G}_1, \mathcal{G}_2, q_2)$ infer $\vdash C_1 \parallel C_2\ \mathbf{sat}\ (p_1 \ast p_2, \mathcal{R}, \mathcal{G}_1 \cup \mathcal{G}_2, q_1 \ast q_2)$.
- *Atom.* If $P$ and $Q$ are precise, $\vdash C\ \mathbf{sat}\ (P \ast P', \emptyset, \emptyset, Q \ast Q')$ and $(P \rightsquigarrow Q) \subseteq \mathcal{G}$, then $\vdash \langle C \rangle_{P \rightsquigarrow Q}\ \mathbf{sat}\ (\boxed{P \ast F} \ast P', \emptyset, \mathcal{G}, \boxed{Q \ast F} \ast Q')$, for every separation-logic assertion $F$.
- *AtomR.* If $\vdash \langle C \rangle_{P \rightsquigarrow Q}\ \mathbf{sat}\ (p, \emptyset, \mathcal{G}, q)$ and $p$ and $q$ are stable under $\mathcal{R}$, then $\vdash \langle C \rangle_{P \rightsquigarrow Q}\ \mathbf{sat}\ (p, \mathcal{R}, \mathcal{G}, q)$.
- *Frame.* If $\vdash C\ \mathbf{sat}\ (p, \mathcal{R}, \mathcal{G}, q)$ and $r$ is stable under $\mathcal{R} \cup \mathcal{G}$, then $\vdash C\ \mathbf{sat}\ (p \ast r, \mathcal{R}, \mathcal{G}, q \ast r)$.
- *Weaken.* From $\vdash C\ \mathbf{sat}\ (p', \mathcal{R}', \mathcal{G}', q')$ with $p \Rightarrow p'$, $[\![\mathcal{R}]\!] \subseteq [\![\mathcal{R}']\!]$, $[\![\mathcal{G}']\!] \subseteq [\![\mathcal{G}]\!]$ and $q' \Rightarrow q$, infer $\vdash C\ \mathbf{sat}\ (p, \mathcal{R}, \mathcal{G}, q)$.
- *Disj, Conj.* From judgments for $p_1$ and $p_2$ with a common postcondition infer the one for $p_1 \vee p_2$; from judgments with postconditions $q_1$ and $q_2$ and a common precondition infer the one for $q_1 \wedge q_2$.
- *Ex, All.* If the logical variable $x$ is not free in $q$, $C$, $\mathcal{R}$ or $\mathcal{G}$, from $\vdash C\ \mathbf{sat}\ (p, \mathcal{R}, \mathcal{G}, q)$ infer $\vdash C\ \mathbf{sat}\ (\exists x.\, p, \mathcal{R}, \mathcal{G}, q)$; if $x$ is not free in $p$, $C$, $\mathcal{R}$ or $\mathcal{G}$, infer $\vdash C\ \mathbf{sat}\ (p, \mathcal{R}, \mathcal{G}, \forall x.\, q)$.

Every application of Atom to an atomic block uses the block's annotation $P \rightsquigarrow Q$. The guarantee premise may be discharged by derived rules: $(P \rightsquigarrow P) \subseteq \mathcal{G}$ for exact $P$; $(P \rightsquigarrow Q) \subseteq \mathcal{G}$ for $(P \rightsquigarrow Q) \in \mathcal{G}$; substitution of an expression for a logical variable; and consequence, from $P' \Rightarrow P$, $(P \rightsquigarrow Q) \subseteq \mathcal{G}$ and $Q' \Rightarrow Q$ infer $(P' \rightsquigarrow Q') \subseteq \mathcal{G}$.

## Depends on

- [RGSep assertions over local and shared state](rgsep-assertions-over-local-and-shared-state.md)
- [Actions and interference in RGSep](rgsep-actions-and-interference.md)
- [Precise predicates](../../separation-logic-metatheory/abstract-separation-logic/precise-predicates.md)

## Proof depends on

None.

## Expansion

The conference paper's single atomic rule, with precondition $\boxed{\exists \vec y.\, P} \ast P''$ and postcondition $\exists \vec y.\, (\boxed{Q} \ast Q'')$, is derivable from Atom (whose premises include precision of the updated parts), Ex, Weaken and AtomR. The thesis encodes conditionals, while loops and guarded atomic blocks with assume statements, as $(\mathrm{assume}(B) ; C_1) + (\mathrm{assume}(\neg B) ; C_2)$, $(\mathrm{assume}(B) ; C)^\ast ; \mathrm{assume}(\neg B)$ and $\langle \mathrm{assume}(B) ; C \rangle$; the system above contains no Boolean tests and only unguarded atomic blocks, so these encodings are outside it. Program variables are not separated from $M$. For a concrete instance whose states pair a store with a heap and whose separation splits only the heap, primitive commands are not local, the frame rule needs the side condition that the frame mention no variable the command modifies, and the parallel rule needs stack variables local to threads. The conference paper also gives an axiom for a non-atomic read of shared state in the concrete heap model; its report derives it in that model by encoding the read as two atomic reads followed by a consistency check, and it is not a rule of the abstract system.

## Sources

- V. Vafeiadis, *Modular fine-grained concurrency verification*, PhD thesis, University of Cambridge, Technical Report UCAM-CL-TR-726, July 2008, <https://www.cl.cam.ac.uk/techreports/UCAM-CL-TR-726.pdf>: Section 2.2 (the language GPPL and the assume encodings of conditionals, loops and conditional critical regions), Section 2.4.1 (Definitions 3, 4 and 8: resource algebras, locality, precise assertions), Section 2.4.2 (the aside on the stack: side conditions on the frame and parallel rules), Section 3.1.2 (Figure 3.1, rules for an action allowed by a guarantee) and Section 3.1.4 (the rules Weaken, Frame, Disj, Conj, Ex, All, Skip, Loop, Seq, Choice, Prim, Par, AtomR and Atom, the precision requirement, and the derivation of the conference paper's atomic rule).
- V. Vafeiadis and M. Parkinson, "A marriage of rely/guarantee and separation logic", *CONCUR 2007 – Concurrency Theory*, LNCS 4703, Springer, 2007, pp. 256–271, <https://doi.org/10.1007/978-3-540-74407-8_18>, author copy <https://www.mpi-sws.org/~viktor/papers/concur2007-marriage.pdf>: Section 3.5 and Fig. 1 (the conference atomic rule and the shared-read axiom).
- V. Vafeiadis and M. Parkinson, *A marriage of rely/guarantee and separation logic*, Technical Report UCAM-CL-TR-687, University of Cambridge Computer Laboratory, June 2007, <https://www.cl.cam.ac.uk/techreports/UCAM-CL-TR-687.pdf>: Section 5, the paragraph after the proof of Theorem 31 (the shared-read axiom derived in the concrete model).
