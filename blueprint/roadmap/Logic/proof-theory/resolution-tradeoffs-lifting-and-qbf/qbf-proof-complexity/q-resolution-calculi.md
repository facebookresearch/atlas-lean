# Q-resolution and its long-distance and universal variants

Q-resolution refutes false prenex QBFs with CNF matrix by resolving on existential variables and deleting trailing universal literals; long-distance Q-resolution also allows certain merged universal tautologies, and QU-resolution also resolves on universal variables.

Let $\Phi = Q_1 X_1 \dots Q_k X_k .\, \phi$ be a closed prenex QBF with CNF matrix $\phi$, quantifier blocks $X_i$ and $Q_i \ne Q_{i+1}$; a variable in $X_i$ has **level** $\mathrm{lv}(x) = i$. A QBF is false iff the universal player has a winning strategy, a family of functions giving each universal variable a value depending on the variables quantified before it.

**Q-resolution** ($\mathsf{Q\text{-}Res}$) derives clauses from $\Phi$ by three rules:

- **axiom:** any non-tautological clause of $\phi$;
- **resolution:** from $C_1 \lor x$ and $C_2 \lor \overline{x}$ with $x$ existential, derive $C_1 \lor C_2$, provided the resolvent is not tautological;
- **universal reduction ($\forall$-Red):** from $D \lor u$ with $u$ a universal literal and $\mathrm{lv}(u) \ge \mathrm{lv}(l)$ for every existential literal $l \in D$, derive $D$.

A refutation is a derivation of the empty clause. **QU-resolution** ($\mathsf{QU\text{-}Res}$) also allows the resolution rule with a universal pivot. **Long-distance Q-resolution** ($\mathsf{LD\text{-}Q\text{-}Res}$) allows resolvents containing both literals of a universal variable $u$, merged into a special literal $u^*$, provided $\mathrm{lv}(x) < \mathrm{lv}(u)$ for the existential pivot $x$ whenever $u$ occurs in both premises; merged literals are reduced like ordinary universal literals. $\mathsf{LQU^+\text{-}Res}$ combines long-distance steps with universal pivots, never resolving on a merged literal.

## Expansion

These calculi model CDCL-based QBF solving: learned clauses and clause learning with universal reduction are Q-resolution derivations, and long-distance steps capture the learning of the original QCDCL algorithm. Without the level condition long-distance resolution is unsound: for the true QBF $\forall u \exists x.\, (u \lor \overline{x}) \land (\overline{u} \lor x)$, resolving on $x$ and reducing would derive the empty clause. Every system here is sound and refutationally complete for false prenex QBFs with CNF matrix; on purely existential QBFs each of them is ordinary resolution.

## Depends on

- [Resolution refutation](../../../propositional-logic/resolution-size-and-width/is-resolution-refutation.md)

## Proof depends on

None.

## Sources

- O. Beyersdorff, L. Chew, M. Janota, "Proof complexity of resolution-based QBF calculi", *STACS 2015*, LIPIcs 30, 76-89, doi:10.4230/LIPIcs.STACS.2015.76 (Section 2, the paragraph on resolution-based calculi for QBF and Figure 2).
- O. Beyersdorff, B. Böhm, "Understanding the relative strength of QBF CDCL solvers and QBF resolution", *Logical Methods in Computer Science* 19(2:2), 2023 (conference version ITCS 2021), doi:10.46298/lmcs-19(2:2)2023, arXiv:2109.04862v5 (Section 2.3, the definitions of Q-resolution and long-distance Q-resolution and the unsoundness example).
