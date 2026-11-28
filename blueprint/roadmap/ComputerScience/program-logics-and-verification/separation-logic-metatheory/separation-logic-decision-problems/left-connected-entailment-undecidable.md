# Progressing, left-connected and established entailment is undecidable

Entailment in separation logic with inductive definitions is undecidable for problems whose rules are progressing and established on both sides and connected on the left side only, so connectivity of the right-hand side cannot be dropped from the decidable progressing, connected and left-established class.

**Theorem.** The following problem is undecidable: given an entailment problem $\phi \vdash_{\mathcal{R}} \psi$ (a quantifier-free formula $\phi$, a formula $\psi$ and a set of inductive definitions $\mathcal{R}$) that is progressing, left-connected and established, in the sense of [Progressing, connected and established entailment problems](progressing-connected-established-entailment.md), decide whether $\phi \models_{\mathcal{R}} \psi$.

The record size $\kappa$ is a fixed parameter of the logic; the reduction in the source uses records with two fields ($\kappa = 2$).

## Depends on

- [Progressing, connected and established entailment problems](progressing-connected-established-entailment.md)
- [Decidability by multi-stack machines](../../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [Whether a context-free grammar generates every word is undecidable](../../../../TheoryOfComputation/undecidable-problems/undecidable-problems-for-context-free-grammars/exists-not-tm2-decidable-univ.md)

## Expansion

The proof reduces from universality of context-free grammars $G = (N, T, S, \Delta)$: whether $T^* \subseteq L(G)$. Since $T^* \subseteq L(G)$ holds iff $\epsilon \in L(G)$, which is decidable, and $T^+ \subseteq L(G)$, it suffices to decide $T^+ \subseteq L(G)$. One may assume $T = \{0, 1\}$: encode each terminal by a binary block of a fixed length $m$ and add to the image of $L(G)$ the regular set of nonempty binary words that are not concatenations of codewords, so that the new grammar generates every nonempty binary word iff $G$ generates every nonempty word over $T$. Finally, pass to a grammar $G'$ for the nonempty words of the language in Greibach normal form, with productions $A_0 \to a A_1 \dots A_n$ ($n \ge 0$). Two special variables $\hat{0}$, $\hat{1}$ stand for the bits. Each nonterminal $A_0$ becomes a predicate $A_0(x, y, \hat{0}, \hat{1})$ with one rule

$$
A_0(x, y, \hat{0}, \hat{1}) \Leftarrow x \mapsto (\hat{a}, x_1) * A_1(x_1, x_2, \hat{0}, \hat{1}) * \dots * A_n(x_n, y, \hat{0}, \hat{1})
$$

per production $A_0 \to a A_1 \dots A_n$ with $n \ge 1$, and the rule $A_0(x, y, \hat{0}, \hat{1}) \Leftarrow x \mapsto (\hat{a}, y)$ per production $A_0 \to a$; a predicate $T$ describes all nonempty bit lists, by the rules $T(x, y, \hat{0}, \hat{1}) \Leftarrow x \mapsto (\hat{a}, z) * T(z, y, \hat{0}, \hat{1})$ and $T(x, y, \hat{0}, \hat{1}) \Leftarrow x \mapsto (\hat{a}, y)$ for $a \in \{0, 1\}$. The SID is progressing and established, and the rules for $T$ are connected. The entailment $\hat{0} \not\approx \hat{1} * T(x, y, \hat{0}, \hat{1}) \vdash_{\mathcal{R}} S(x, y, \hat{0}, \hat{1})$, with $S$ the predicate of the start symbol of $G'$, is valid exactly when $G'$ generates every nonempty binary word.

A good expansion links, besides the universality page, the existence of an equivalent Greibach normal form grammar for every context-free language without the empty word, and the closure steps that reduce universality to the binary, $\epsilon$-free case.

In contrast, the same source records that the progressing, connected and left-established entailment problem is complete for doubly exponential time (Theorem 5 of the version read), and, citing earlier work of the same authors, that dropping establishment instead also gives undecidability even with progress and connectivity on both sides.

## Sources

- Mnacho Echenim, Radu Iosif and Nicolas Peltier, "Unifying Decidable Entailments in Separation Logic with Inductive Definitions", in *Automated Deduction – CADE 28*, Lecture Notes in Computer Science 12699, pp. 183–199, Springer, 2021, <https://doi.org/10.1007/978-3-030-79876-5_11>; read in arXiv:2012.14361v2, <https://arxiv.org/abs/2012.14361v2> (the report version): Theorem 6 and its proof, and Table 1, of that version.
