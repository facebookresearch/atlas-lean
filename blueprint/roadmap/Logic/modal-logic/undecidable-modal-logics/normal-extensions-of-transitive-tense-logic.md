# Normal extensions of transitive tense logic

A tense logic is a normal bimodal logic with a future box and a past box that are converse to each other. The minimal transitive one, $\mathsf{K4}_t$, is the tense logic of transitive frames, and $\mathrm{NExt}\,\mathsf{K4}_t$ is the lattice of its normal extensions, each axiomatized over $\mathsf{K4}_t$ by extra formulas.

**Tense logics.** The tense language $\mathcal{L}_t$ adds to propositional logic two boxes $\Box$ (future) and $\blacksquare$ (past), with duals $\Diamond = \neg\Box\neg$ and $\blacklozenge = \neg\blacksquare\neg$. A *normal bimodal logic* is a set of formulas containing all classical tautologies and the K axioms $\Box(p \to q) \to (\Box p \to \Box q)$ and $\blacksquare(p \to q) \to (\blacksquare p \to \blacksquare q)$, closed under modus ponens, uniform substitution and necessitation for both boxes. A *tense logic* is a normal bimodal logic containing $p \to \Box\blacklozenge p$ and $p \to \blacksquare\Diamond p$; $\mathsf{K}_t$ is the least one. For a tense logic $L$ and a set $\Sigma$ of formulas, $L \oplus \Sigma$ is the least tense logic containing $L \cup \Sigma$, and $\mathrm{NExt}\,L$ is the set of tense logics containing $L$. The logic $\mathsf{K4}_t = \mathsf{K}_t \oplus (\Diamond\Diamond p \to \Diamond p)$ is the tense logic of transitive Kripke frames $(X, R)$, where $\Box$ quantifies over $R$-successors and $\blacksquare$ over $R$-predecessors.

**Properties.** A tense logic $L$ is *consistent* if $\bot \notin L$; *Kripke complete* if it is the logic of its Kripke frames; has the *finite model property* if it is the logic of its finite frames; is *tabular* if it is the logic of a single finite frame; is *canonical* if its canonical frame validates it; is *first-order definable* if its class of Kripke frames is first-order definable and $L$ is complete for it; is *locally tabular* if each finite set of variables gives finitely many formulas up to equivalence in $L$; and is *decidable* if membership in $L$ is decidable.

**Decidability of a property.** A property $P$, identified with the set of logics in $\mathrm{NExt}\,L_0$ having it, is *decidable in $\mathrm{NExt}\,L_0$* if the set $\{\varphi \in \mathcal{L}_t : L_0 \oplus \varphi \in P\}$ is decidable. Only finitely axiomatizable extensions are considered, since otherwise, by a result of Kuznetsov, only trivial properties would be decidable.

## Depends on

- [Kripke model](../kripke-semantics/kripke-model.md)

## Proof depends on

None.

## Expansion

Every finite set of extra axioms can be replaced by the single conjunction, so a finitely axiomatizable extension of $L_0$ has the form $L_0 \oplus \varphi$. If $P$ is undecidable in $\mathrm{NExt}\,(L \oplus \psi)$ for a formula $\psi$, it is undecidable in $\mathrm{NExt}\,L$, because $(L \oplus \psi) \oplus \varphi = L \oplus (\psi \wedge \varphi)$. For unimodal logics, Thomason and Chagrov showed that Kripke completeness, the finite model property and decidability are undecidable in $\mathrm{NExt}\,\mathsf{K}$ and $\mathrm{NExt}\,\mathsf{K4}$, while all of them are decidable in the lattice of extensions of the tense logic of linear frames (Wolter).

## Sources

- Q. Chen and T. Takahashi, "Most properties are undecidable for transitive tense logics", Electronic Proceedings in Theoretical Computer Science 447, 2026, pp. 189–202, doi:10.4204/EPTCS.447.11; read as arXiv:2606.31863v1, <https://arxiv.org/abs/2606.31863v1>: Section 2 (tense logics, $\mathsf{K4}_t$, the properties, the definition of a decidable property and the reduction between lattices) and the overview table in Section 1.
