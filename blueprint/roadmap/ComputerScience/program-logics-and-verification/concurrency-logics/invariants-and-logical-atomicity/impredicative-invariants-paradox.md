# Impredicative invariants paradox

In any higher-order separation logic with a masked update modality, invariants that open without a later together with a one-way two-state token protocol make the logic inconsistent; the later in Iris's invariant rule cannot simply be dropped.

**Theorem.** Assume a higher-order separation logic with the persistence modality $\square$ and an update modality $|\!\Rrightarrow_{\mathsf{m}}$ indexed by two masks $\mathsf{m} \in \{0, 1\}$, each a strong monad with respect to $\ast$, with $|\!\Rrightarrow_0 P \vdash |\!\Rrightarrow_1 P$. Assume a type $I$ and a connective $\boxed{\cdot}^{\cdot} : I \to \mathit{iProp} \to \mathit{iProp}$ with

- $P \vdash |\!\Rrightarrow_1 \exists \iota.\ \boxed{P}^{\iota}$ and $\boxed{P}^{\iota} \vdash \square \boxed{P}^{\iota}$;
- if $P \ast Q \vdash |\!\Rrightarrow_0 (P \ast R)$ then $\boxed{P}^{\iota} \ast Q \vdash |\!\Rrightarrow_1 R$.

Finally assume a type $G$ and $S, F : G \to \mathit{iProp}$ with $\mathrm{True} \vdash |\!\Rrightarrow_0 \exists \gamma.\ S(\gamma)$, $S(\gamma) \vdash |\!\Rrightarrow_0 F(\gamma)$, $S(\gamma) \ast F(\gamma) \vdash \mathrm{False}$ and $F(\gamma) \vdash F(\gamma) \ast F(\gamma)$. Then $\mathrm{True} \vdash |\!\Rrightarrow_1 \mathrm{False}$.

## Depends on

None.

## Proof depends on

None.

## Expansion

Following the source's documentation: define $\gamma \mapsto P \triangleq \exists \iota.\ \boxed{S(\gamma) \lor (F(\gamma) \ast \square P)}^{\iota}$, which is persistent; allocation follows from token allocation, mask weakening and invariant allocation; opening both invariants named by $\gamma$ without a later gives $\gamma \mapsto P \ast \gamma \mapsto Q \ast \square P \vdash |\!\Rrightarrow_1 \square Q$; and this weak agreement replays the liar argument with $A(\gamma) \triangleq \exists P.\ \square(P \Rightarrow |\!\Rrightarrow_1 \mathrm{False}) \land \gamma \mapsto P$. All Iris versions satisfy every hypothesis except opening without a later.

## Sources

- R. Jung, R. Krebbers, J.-H. Jourdan, A. Bizjak, L. Birkedal and D. Dreyer, "Iris from the ground up: a modular foundation for higher-order concurrent separation logic", *Journal of Functional Programming* 28, e20, 2018, open access <https://doi.org/10.1017/S0956796818000151> (version of record, Cambridge University Press), Section 8.2, Theorem 9 (with WEAKEN-MASK, INV-ALLOC, INV-PERSIST, INV-OPEN-NOLATER, START-ALLOC, START-FINISH, START-NOT-FINISHED, FINISHED-DUP).
- Iris Team, "The Iris 3.1 documentation", technical documentation (not peer reviewed) that the JFP article cites as its appendix (Iris Team, 2017), version of April 29, 2019, <https://plv.mpi-sws.org/iris/appendix-3.1.pdf>, Section 11.2, Theorem 4, Definition 24 and Lemmas 3-4 (proof), supplementary.
