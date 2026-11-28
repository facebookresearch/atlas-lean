# Atomic query answering in the temporal description logic TEL◯ is undecidable

Answering atomic queries over temporal knowledge bases of TEL◯, which combines the lightweight description logic EL with the LTL next and previous operators, is undecidable, closing a question left open when the logic was introduced; with future operators only it is in polynomial time.

**The logic TEL◯.** Fix individual names, concept names and role names, the role names split into *rigid* and *local* ones. A *TEL◯-TBox* is a finite set of concept inclusions in normal form

$$
A\sqsubseteq\bigcirc^n B,\qquad A\sqcap A'\sqsubseteq B,\qquad\exists r.A\sqsubseteq B,\qquad A\sqsubseteq\exists r.B,
$$

with concept names $A,A',B$, a role name $r$ and $n\in\mathbb Z$. A *temporal ABox* is a finite set of facts $A(a,n)$ and $r(a,b,n)$ with individual names $a,b$ and time points $n\in\mathbb Z$. An interpretation is a sequence $(\mathcal I_i)_{i\in\mathbb Z}$ of description logic interpretations over one domain, interpreting individual names by themselves and rigid roles identically at all times; $\bigcirc^n A$ holds at time $i$ where $A$ holds at time $i+n$, and a concept inclusion must hold at every time point. The *future fragment* allows only $n\ge0$, and a *rigid concept name* is interpreted identically at all times. *Temporal atomic query answering* (TAQA) asks, given a TBox $\mathcal T$, an ABox $\mathcal A$ and a fact $A(a,n)$, whether every model of $(\mathcal T,\mathcal A)$ satisfies $A(a,n)$.

**Theorem (Bourgaux, Gnatenko and Thomazo).**

1. TAQA is undecidable in combined complexity for TEL◯-TBoxes, and for TBoxes of the future fragment extended with rigid concept names (Theorem 26).
2. There is a TBox $\mathcal T$ of the future fragment with concept names $A$, $B$ for which $\{n\in\mathbb N:\mathcal T\models A\sqsubseteq\bigcirc^n B\}=\{4^k:k\in\mathbb N\}$, so TEL◯ lacks ultimate periodicity, and it is undecidable whether this set is semilinear for a given future TBox (Theorem 25).

By contrast, TAQA for TBoxes of the future fragment, without rigid concept names, is PTIME-complete in both combined and data complexity (Theorem 27). Undecidability in combined complexity does not settle data complexity.

## Depends on

- [Decidability by multi-stack machines](../../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)
- [Semilinear set of vectors](../../../../TheoryOfComputation/context-free-languages/closure-and-pumping/parikh-images-and-semilinear-sets/is-semilinear.md)

## Proof depends on

None.

## Expansion

For every unary conjunctive grammar $G$ over the letter $c$ one constructs a TBox $\mathcal T_G$ of the future fragment and concept names $A$, $B$ with $\mathcal T_G\models A\sqsubseteq\bigcirc^n B$ exactly when $c^n$ belongs to the language of $G$: concept inclusions $A\sqsubseteq\bigcirc^n B$ shift in time like concatenation of unary words, and conjunctions $A\sqcap A'\sqsubseteq B$ intersect. Emptiness of unary conjunctive languages, which is undecidable by Jeż and Okhotin, then reduces to TAQA for TEL◯-TBoxes and for future TBoxes with rigid concept names, where the existence of some shift $n$ with $\mathcal T_G\models A\sqsubseteq\bigcirc^n B$ can be turned into the entailment of a single fact. Regularity of unary conjunctive languages, also undecidable, reduces to semilinearity of the entailed time shifts. A good expansion links a page for the theorem of Jeż and Okhotin that emptiness, finiteness and regularity of unary conjunctive grammars are undecidable (Theorem 9 of the source).

## Sources

- C. Bourgaux, A. Gnatenko and M. Thomazo, "Analysing temporal reasoning in description logics using formal grammars", in *ECAI 2025*, Frontiers in Artificial Intelligence and Applications, IOS Press, 2025, doi:[10.3233/FAIA251004](https://doi.org/10.3233/FAIA251004) (the publisher record gives no volume or pages), with an extended abstract in *Proceedings of the Thirty-Fifth International Joint Conference on Artificial Intelligence (IJCAI 2026)*, pp. 8232–8236, doi:[10.24963/ijcai.2026/918](https://doi.org/10.24963/ijcai.2026/918); read in arXiv:2508.00575v1 ([arXiv](https://arxiv.org/abs/2508.00575v1)), whose numbering is used: the syntax and semantics of TEL◯ in the preliminaries, Theorem 9 (Jeż and Okhotin), the grammar-to-TBox construction (Theorem 14), Theorems 25 and 26 (non-ultimate periodicity and undecidability) and Theorem 27 (PTIME for the future fragment).
