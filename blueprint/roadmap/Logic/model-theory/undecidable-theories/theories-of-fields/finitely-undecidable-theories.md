# Finitely undecidable theories

A theory is finitely undecidable if every finitely axiomatized subtheory of it, in the same language, is undecidable. A finitely undecidable complete theory with infinite models is in particular not finitely axiomatizable, which links the notion to the open question whether some infinite field is finitely axiomatizable.

**Definition.** Let $\mathcal{L}$ be a finite first-order language, so that $\mathcal{L}$-sentences are finite strings over a finite alphabet. A theory $T$ in $\mathcal{L}$ is *finitely undecidable* if every finitely axiomatized $\mathcal{L}$-theory $\Sigma \subseteq T$ is undecidable, that is, the set $\mathrm{Cons}(\Sigma)$ of $\mathcal{L}$-sentences $\varphi$ with $\Sigma \models \varphi$ is not decidable. An $\mathcal{L}$-structure is finitely undecidable if its complete $\mathcal{L}$-theory is.

The source states the definition once for every finitely axiomatized subtheory and once for every nonempty finite one; in the languages used here the two agree, since the empty set of axioms has an undecidable set of consequences in any language with a binary function symbol (this remark is the page's own, not the source's). Shlapentokh and Videla call this property *finite hereditary undecidability*. For fields the default language is the language of rings $\mathcal{L}_r$; for valued fields it is $\mathcal{L}_{\mathrm{val}}$, the language of rings with a unary predicate for the valuation ring.

## Depends on

- [Complete theory of a first-order structure](../../../first-order-logic/theory-of-structure.md)
- [Field](../../../../Algebra/rings-and-fields/field.md)
- [Decidability by multi-stack machines](../../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

None.

## Expansion

A theory $T_2$ is hereditarily undecidable if some finitely axiomatized essentially undecidable theory, such as Robinson arithmetic $Q$, has a model interpretable in a model of $T_2$ (Tarski); finite undecidability is weaker and also covers decidable complete theories. Ziegler proved that $\mathbb{C}$, the algebraic closure of $\mathbb{F}_p(t)$, $\mathbb{R}$ and $\mathbb{Q}_p$ are finitely undecidable in $\mathcal{L}_r$, although their theories are decidable. If a complete decidable theory $T$ had a finitely axiomatized subtheory $\Sigma$ with the same consequences, $\Sigma$ would be decidable, so a decidable finitely undecidable complete theory is not finitely axiomatizable.

## Sources

- B. Tyrrell, "Finite undecidability in NIP fields", *The Journal of Symbolic Logic* 90(2):509–532, 2025, doi:10.1017/jsl.2023.73; read as arXiv:2210.12729v4, <https://arxiv.org/abs/2210.12729v4>: Definition 1.3, Theorem 1.6 and Section 1 of arXiv:2210.12729v4.
- B. Tyrrell, "Finite undecidability in PAC and PRC fields", *Annals of Pure and Applied Logic* 175(10):103465, 2024, doi:10.1016/j.apal.2024.103465; read as arXiv:2212.12918v2, <https://arxiv.org/abs/2212.12918v2>: the definition in Section 1 and Ziegler's results as recalled there.
