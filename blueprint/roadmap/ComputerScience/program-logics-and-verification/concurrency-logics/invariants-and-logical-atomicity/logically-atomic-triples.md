# Logically atomic triples

A *logically atomic triple* of Iris 1.0 is defined as a specification under which a possibly non-atomic expression may be used as if it took effect at one instant, so that clients can open invariants around it; it is defined from Iris 1.0 Hoare triples and view shifts by quantifying over client atomic shifts.

In the Iris 1.0 logic, with view shifts $P \mathrel{{}^{\mathcal{E}_1}\!\!\Rrightarrow^{\mathcal{E}_2}} Q$, Hoare triples $\{P\}\ e\ \{v.\, Q\}_{\mathcal{E}}$, timelessness and invariants, write $-\mathcal{E} \triangleq \top \setminus \mathcal{E}$, $\mathcal{E}_1 \mathrel{\#} \mathcal{E}_2$ for disjoint masks, and $P \mathrel{{}^{\mathcal{E}_1}\!\!\Lleftarrow\!\!\Rrightarrow^{\mathcal{E}_2}} Q$ for the two view shifts $P \mathrel{{}^{\mathcal{E}_1}\!\!\Rrightarrow^{\mathcal{E}_2}} Q$ and $Q \mathrel{{}^{\mathcal{E}_2}\!\!\Rrightarrow^{\mathcal{E}_1}} P$. The variable $x$ may occur in $\alpha, \beta, R, Q$ and $v$ in $\beta, Q$. The *atomic shift* and the *logically atomic triple* are

$$
\langle x.\ P \Lleftarrow\!\!\Rrightarrow \alpha \mid R(x), \mathcal{E}_R \mid v.\ \beta \Rrightarrow Q(x, v) \rangle^{\mathcal{E}_M}_{\mathcal{E}} \triangleq \mathrm{timeless}(P) \land \mathcal{E}_R \mathrel{\#} (\mathcal{E} \cup \mathcal{E}_M) \land \big(P \mathrel{{}^{-\mathcal{E}_M}\!\!\Lleftarrow\!\!\Rrightarrow^{-\mathcal{E}_M - \mathcal{E}_R}} \exists x.\ \alpha \ast R(x)\big) \land \big(\forall x, v.\ \beta \ast R(x) \mathrel{{}^{-\mathcal{E}_M - \mathcal{E}_R}\!\!\Rrightarrow^{-\mathcal{E}_M}} Q(x, v)\big),
$$

$$
\langle x.\ \alpha \rangle\ e\ \langle v.\ \beta \rangle^{\mathcal{E}_M}_{\mathcal{E}} \triangleq \mathcal{E}_M \mathrel{\#} \mathcal{E} \land \square \Big(\forall P, Q, R, \mathcal{E}_R.\ \langle x.\ P \Lleftarrow\!\!\Rrightarrow \alpha \mid R(x), \mathcal{E}_R \mid v.\ \beta \Rrightarrow Q(x, v) \rangle^{\mathcal{E}_M}_{\mathcal{E}} \Rightarrow \{P\}\ e\ \{v.\, \exists x.\ Q(x, v)\}_{\top}\Big).
$$

Here $\mathcal{E}_M$ is the *module mask*, $\mathcal{E}$ the *shared mask* and $\mathcal{E}_R$ the *client mask*.

## Depends on

None.

## Proof depends on

None.

## Expansion

This page is stated in the Iris 1.0 framework of the source, whose primitive view shifts, Hoare triples, timelessness and invariants differ in their mask rules from the Iris 3 fancy updates and weakest preconditions of the other pages (the JFP article's Section 8.1 lists the differences). Missing prerequisites, which have no pages: Iris 1.0 view shifts with masks, Iris 1.0 Hoare triples with masks, Iris 1.0 timelessness, and Iris 1.0 invariants.

The source motivates the definition from the client and module perspectives: the opening direction of the bidirectional shift is used at the linearization point, the aborting direction returns to $P$ when a step did not commit, and the committing shift produces the client's postcondition; timelessness of $P$ is needed because nested invariant openings around one physical step can strip only one later. The source lists derived rules (consequence, framing, existential binding, conversion of physically atomic triples, conversion to Hoare triples for timeless $\alpha$, and opening invariants around the triple).

## Sources

- R. Jung, D. Swasey, F. Sieczkowski, K. Svendsen, A. Turon, L. Birkedal and D. Dreyer, "Iris: Monoids and invariants as an orthogonal basis for concurrent reasoning", *Proceedings of the 42nd ACM SIGPLAN-SIGACT Symposium on Principles of Programming Languages (POPL 2015)*, pp. 637-650, 2015, <https://doi.org/10.1145/2676726.2676980>; author copy of the published version <https://iris-project.org/pdfs/2015-popl-iris1-final.pdf>, Section 7.1 (motivation, equations (5)-(8), the three masks), Figure 13 (definition of logically atomic triples and atomic shifts) and Figure 14 (selected derived rules).
