# LL(1) grammars have no left recursion

Let $G$ be a grammar with a [correct LL(1) parse table](ll-1-lookahead-and-correct-parse-tables.md) and $l$ a lookahead symbol. Say that there is a *nullable path* from $X$ to $Z$ on $l$ if there are productions $X = X_0 \to \alpha_0 X_1 \beta_0$, $X_1 \to \alpha_1 X_2 \beta_1$, $\dots$, $X_{k-1} \to \alpha_{k-1} X_k \beta_{k-1}$ with $X_k = Z$, $k \ge 1$, every $\alpha_i$ nullable and $l$ in the lookahead set of each of these productions. Then no nonterminal $X$ has a nullable path from $X$ to itself on any $l$: $G$ is not left recursive.

**Proof idea.** Attach sizes to derivations of $\mathrm{NULLABLE}$ and $\mathrm{FIRST}$ facts. In an LL(1) grammar any two derivations of the same $\mathrm{FIRST}$ fact have the same size, and so do any two derivations of $\mathrm{NULLABLE}(X)$ when some lookahead symbol lies in $\mathrm{FOLLOW}(X)$; a left-recursive nonterminal yields two derivations of one fact with different sizes. In the nullable case the lookahead $l$ of the cycle supplies the required $\mathrm{FOLLOW}$ fact. Without that witness the size need not be unique: with $S \to s$, $U \to \varepsilon \mid V$ and $V \to \varepsilon$, the table with the single entry $(S, s)$ is correct, since $\mathrm{FOLLOW}(U)$ and $\mathrm{FOLLOW}(V)$ are empty, yet $\mathrm{NULLABLE}(U)$ has derivations of sizes 1 and 2.

## Depends on

- [LL(1) lookahead and correct parse tables](ll-1-lookahead-and-correct-parse-tables.md)

## Sources

- S. Lasser, C. Casinghino, K. Fisher and C. Roux, "A verified LL(1) parser generator", *10th International Conference on Interactive Theorem Proving (ITP 2019)*, LIPIcs 141, 2019, 24:1–24:18, <https://drops.dagstuhl.de/storage/00lipics/lipics-vol141-itp2019/LIPIcs.ITP.2019.24/LIPIcs.ITP.2019.24.pdf>, Section 4.3: the predicates nullable_path and left_recursive, the three-step argument with sized NULLABLE and FIRST derivations, and Lemma LL1_parse_table_impl_no_left_recursion.
- S. Lasser, the Coq development accompanying the paper, <https://github.com/slasser/vermillion>, file `Proofs/Parser_safe.v`: lemmas `sized_first_sym_det` and `sized_nullable_sym_det`, the latter with the hypothesis `follow_sym g la sym`.
