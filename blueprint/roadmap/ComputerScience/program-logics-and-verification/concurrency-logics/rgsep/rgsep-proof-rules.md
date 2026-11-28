# RGSep proof rules

RGSep is defined by rules deriving judgments $\vdash C\ \mathbf{sat}\ (p, \mathcal{R}, \mathcal{G}, q)$: started in a state satisfying $p$, under interference at most $\mathcal{R}$, the command $C$ does not fault, causes interference at most $\mathcal{G}$, and ends in a state satisfying $q$ if it terminates. Only atomic blocks change shared state.

Commands are

$$C ::= \mathbf{skip} \mid x := e \mid x := [e] \mid [e_1] := e_2 \mid x := \mathrm{cons}(e_1, \dots, e_n) \mid \mathrm{dispose}(e) \mid C_1; C_2 \mid C_1 \parallel C_2 \mid \mathbf{if}\ (b)\ \{C_1\}\ \mathbf{else}\ \{C_2\} \mid \mathbf{while}\ (b)\ \{C\} \mid \mathbf{atomic}\ \{C\},$$

with pure expressions $e$ over program and logical variables; global variables are not assigned directly. Assertions $p, q, r$ and stability are those of [RGSep assertions over local and shared state](rgsep-assertions-over-local-and-shared-state.md); $\mathcal{R}, \mathcal{G}$ are sets of actions and $(P \rightsquigarrow Q) \subseteq \mathcal{G}$ is as in [actions and interference in RGSep](rgsep-actions-and-interference.md). The rules are:

- *Local axioms.* The [small axioms of separation logic](../../separation-logic-metatheory/separating-implication-and-small-axioms/small-axioms-of-separation-logic.md) for the heap commands, with unboxed pre- and postconditions and arbitrary $\mathcal{R}, \mathcal{G}$.
- *Shared read.* If $Q = (P \ast X \mapsto Y)$ and $x \notin \mathrm{fv}(P)$, then $\vdash x := [e]\ \mathbf{sat}\ (\boxed{Q} \wedge e = X, \mathcal{R}, \mathcal{G}, \boxed{Q} \wedge x = Y)$.
- *Atomic.* If $\vdash C\ \mathbf{sat}\ (P_1 \ast P_2, \emptyset, \emptyset, Q_1 \ast Q_2)$, $\vec y \cap \mathrm{FV}(P_2) = \emptyset$, $P \Rightarrow P_1 \ast F$ and $Q_1 \ast F \Rightarrow Q$ are valid, $(P_1 \rightsquigarrow Q_1) \subseteq \mathcal{G}$, $Q$ is stable under $\mathcal{R}$ and $Q$ is [precise](../../separation-logic-metatheory/abstract-separation-logic/precise-predicates.md), then $\vdash \mathbf{atomic}\ \{C\}\ \mathbf{sat}\ (\exists \vec y.\, \boxed{P} \ast P_2, \mathcal{R}, \mathcal{G}, \exists \vec y.\, \boxed{Q} \ast Q_2)$.
- *Parallel.* If $\vdash C_1\ \mathbf{sat}\ (p_1, \mathcal{R} \cup \mathcal{G}_2, \mathcal{G}_1, q_1)$, $\vdash C_2\ \mathbf{sat}\ (p_2, \mathcal{R} \cup \mathcal{G}_1, \mathcal{G}_2, q_2)$, $p_1$ is stable under $\mathcal{R} \cup \mathcal{G}_1$ and $p_2$ under $\mathcal{R} \cup \mathcal{G}_2$, then $\vdash C_1 \parallel C_2\ \mathbf{sat}\ (p_1 \ast p_2, \mathcal{R}, \mathcal{G}_1 \cup \mathcal{G}_2, q_1 \ast q_2)$.
- *Frame.* If $\vdash C\ \mathbf{sat}\ (p, \mathcal{R}, \mathcal{G}, q)$ and either $r$ is stable under $\mathcal{R} \cup \mathcal{G}$ or $C$ contains no atomic block, then $\vdash C\ \mathbf{sat}\ (p \ast r, \mathcal{R}, \mathcal{G}, q \ast r)$.
- *Consequence.* From $\vdash C\ \mathbf{sat}\ (p', \mathcal{R}', \mathcal{G}', q')$ with $p \Rightarrow p'$, $[\![\mathcal{R}]\!] \subseteq [\![\mathcal{R}']\!]$, $[\![\mathcal{G}']\!] \subseteq [\![\mathcal{G}]\!]$ and $q' \Rightarrow q$, infer $\vdash C\ \mathbf{sat}\ (p, \mathcal{R}, \mathcal{G}, q)$.
- *Sequential rules.* $\vdash \mathbf{skip}\ \mathbf{sat}\ (p, \mathcal{R}, \mathcal{G}, p)$; from $\vdash C_1\ \mathbf{sat}\ (p, \mathcal{R}, \mathcal{G}, r)$ and $\vdash C_2\ \mathbf{sat}\ (r, \mathcal{R}, \mathcal{G}, q)$ infer $\vdash C_1; C_2\ \mathbf{sat}\ (p, \mathcal{R}, \mathcal{G}, q)$; from $\vdash C_1\ \mathbf{sat}\ (p \wedge b, \mathcal{R}, \mathcal{G}, q)$ and $\vdash C_2\ \mathbf{sat}\ (p \wedge \neg b, \mathcal{R}, \mathcal{G}, q)$ infer the conditional; from $\vdash C\ \mathbf{sat}\ (p \wedge b, \mathcal{R}, \mathcal{G}, p)$ infer $\vdash \mathbf{while}\ (b)\ \{C\}\ \mathbf{sat}\ (p, \mathcal{R}, \mathcal{G}, p \wedge \neg b)$.

The guarantee premise of the atomic rule may be discharged by the derived rules: $(x \mapsto y \rightsquigarrow x \mapsto y) \subseteq \mathcal{G}$; $(P \rightsquigarrow Q) \subseteq \mathcal{G}$ for $(P \rightsquigarrow Q) \in \mathcal{G}$; from $(P_1 \rightsquigarrow S \ast Q_1) \subseteq \mathcal{G}$ and $(P_2 \ast S \rightsquigarrow Q_2) \subseteq \mathcal{G}$ infer $(P_1 \ast P_2 \rightsquigarrow Q_1 \ast Q_2) \subseteq \mathcal{G}$; substitution of an expression for a logical variable; and consequence, from $P' \Rightarrow P$, $(P \rightsquigarrow Q) \subseteq \mathcal{G}$ and $Q' \Rightarrow Q$ infer $(P' \rightsquigarrow Q') \subseteq \mathcal{G}$. A frame rule for guarantees, from $(P \rightsquigarrow Q) \subseteq \mathcal{G}$ to $(P \ast F \rightsquigarrow Q \ast F) \subseteq \mathcal{G}$, is unsound.

RGSep subsumes single-resource concurrent separation logic: a resource invariant $I$ corresponds to the interference $\mathcal{R} = \mathcal{G} = \{I \rightsquigarrow I\}$.

## Depends on

- [RGSep assertions over local and shared state](rgsep-assertions-over-local-and-shared-state.md)
- [Actions and interference in RGSep](rgsep-actions-and-interference.md)
- [Small axioms of separation logic](../../separation-logic-metatheory/separating-implication-and-small-axioms/small-axioms-of-separation-logic.md)
- [Precise predicates](../../separation-logic-metatheory/abstract-separation-logic/precise-predicates.md)

## Proof depends on

None.

## Expansion

The atomic rule is stated for the guard $\mathbf{true}$; the general $\mathbf{atomic}\ (b)\ \{C\}$ adds $b$ to the body's precondition and requires $P_1 \ast P_2$ to make $b$ defined. A complete development fixes the heap commands' small axioms in the RGSep judgment form and the semantics of the conditional guard over the local heap. The parameterless-procedure rules of the technical report pass a context of procedure specifications unchanged.

## Sources

- V. Vafeiadis and M. Parkinson, "A marriage of rely/guarantee and separation logic", *CONCUR 2007 – Concurrency Theory*, LNCS 4703, Springer, 2007, pp. 256–271, <https://doi.org/10.1007/978-3-540-74407-8_18>, author copy <https://www.mpi-sws.org/~viktor/papers/concur2007-marriage.pdf>: Section 2 (command syntax), Section 3.5 and Fig. 1 (frame, shared read, parallel, sequence and atomic rules; precision of the atomic postcondition), Fig. 2 (rules G-Exact, G-Ax, G-Seq, G-Sub, G-Cons, admissible G-CoFrm) and Section 6 (relation to concurrent separation logic).
- V. Vafeiadis and M. Parkinson, *A marriage of rely/guarantee and separation logic*, Technical Report UCAM-CL-TR-687, University of Cambridge Computer Laboratory, June 2007, <https://www.cl.cam.ac.uk/techreports/UCAM-CL-TR-687.pdf>: Section 3.5 (all proof rules, including consequence, skip, conditional, while and procedures; Figure 2) and Section 5 (Theorem 31, atomic rule with a guard).
