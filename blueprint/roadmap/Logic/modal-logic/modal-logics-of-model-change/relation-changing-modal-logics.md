# Relation-changing modal logics

Relation-changing modal logics extend the basic modal language with dynamic diamonds that delete, add or reverse one edge of the accessibility relation, either next to the current point (local versions) or anywhere in the model (global versions), and then evaluate a formula in the changed model.

**Syntax.** Formulas over a countably infinite set of propositional symbols are

$$
\varphi ::= \bot \mid p \mid \neg\varphi \mid \varphi \wedge \psi \mid \Diamond\varphi \mid \blacklozenge\varphi, \qquad \blacklozenge \in \{\langle sb\rangle, \langle br\rangle, \langle sw\rangle, \langle gsb\rangle, \langle gbr\rangle, \langle gsw\rangle\}.
$$

$\mathcal{ML}(\blacklozenge)$ is the basic modal logic extended with the operator $\blacklozenge$; $\mathcal{ML}(\langle sb\rangle, \langle gsb\rangle)$, $\mathcal{ML}(\langle br\rangle, \langle gbr\rangle)$ and $\mathcal{ML}(\langle sw\rangle, \langle gsw\rangle)$ are *sabotage*, *bridge* and *swap logic*.

**Semantics.** A model $\mathcal M = (W, R, V)$ has a nonempty set $W$, a relation $R \subseteq W \times W$ and a valuation $V$. For a set $S$ of pairs, $\mathcal M^-_S$ replaces $R$ by $R \setminus S$ (for $S \subseteq R$), $\mathcal M^+_S$ replaces $R$ by $R \cup S$ (for $S \subseteq (W \times W) \setminus R$), and $\mathcal M^*_S$ replaces $R$ by $(R \setminus S^{-1}) \cup S$ (for $S \subseteq R^{-1}$). Writing $wv$ for $\{(w, v)\}$, the basic modal clauses are the usual ones, and

- $\mathcal M, w \models \langle sb\rangle\varphi$ iff $\mathcal M^-_{wv}, v \models \varphi$ for some $v$ with $(w, v) \in R$;
- $\mathcal M, w \models \langle br\rangle\varphi$ iff $\mathcal M^+_{wv}, v \models \varphi$ for some $v$ with $(w, v) \notin R$;
- $\mathcal M, w \models \langle sw\rangle\varphi$ iff $\mathcal M^*_{vw}, v \models \varphi$ for some $v$ with $(w, v) \in R$;
- $\mathcal M, w \models \langle gsb\rangle\varphi$ iff $\mathcal M^-_{vu}, w \models \varphi$ for some $(v, u) \in R$;
- $\mathcal M, w \models \langle gbr\rangle\varphi$ iff $\mathcal M^+_{vu}, w \models \varphi$ for some $(v, u) \notin R$;
- $\mathcal M, w \models \langle gsw\rangle\varphi$ iff $\mathcal M^*_{uv}, w \models \varphi$ for some $(v, u) \in R$.

A formula is satisfiable if it is true at some point of some model.

## Depends on

- [Kripke model](../kripke-semantics/kripke-model.md)
- [Satisfaction in a Kripke model](../kripke-semantics/satisfies.md)

## Proof depends on

None.

## Expansion

The local operators move along the changed edge (sabotage deletes the edge it traverses, bridge adds and traverses a new edge, swap traverses an edge and reverses it), while the global operators change one edge anywhere and stay at the current point. The global sabotage operator is van Benthem's operator for the sabotage game, in which one player moves along edges and the other deletes edges. All six logics translate into hybrid logic with the down-arrow binder and the universal modality.

## Sources

- C. Areces, R. Fervari, G. Hoffmann and M. Martel, "Relation-changing logics as fragments of hybrid logics", in *Proceedings of the Seventh International Symposium on Games, Automata, Logics and Formal Verification (GandALF 2016)*, Electronic Proceedings in Theoretical Computer Science 226, 2016, pp. 16–29, <https://doi.org/10.4204/EPTCS.226.2>; read as arXiv:1609.04086v1, <https://arxiv.org/abs/1609.04086v1>: Section 1 and Section 2 (Definitions 1, 2 and 3).
