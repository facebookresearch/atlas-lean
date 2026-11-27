# Equivalence to a lower nesting level of regular expressions with binding is undecidable

For regular expressions with binding over data words, no algorithm decides whether an expression of nesting level $i+1$ has a language-equivalent expression of level $i$. So the nesting depth of iterated bindings that a data language needs cannot be computed from an expression.

**Theorem (Praveen and Srivathsan).** Fix a level $i \ge 1$. The following problem is undecidable. Input: a [regular expression with binding](regular-expressions-with-binding-and-levels.md) $e$ in $F_{i+1}$. Question: is there an expression $f$ in $F_i$ with $L(f) = L(e)$?

The source states the theorem for a level $i$ without a lower bound; its proof uses the expression $r_i$, which the source defines for $i \ge 1$, so the case $i \ge 1$ is the one the proof covers. The alphabet and the variables are part of the input expression; for its strictness constructions the source remarks that a constant number of letters and variables suffices. Universality of REWBs is also undecidable (the source cites Neven, Schwentick and Vianu, and Kostylev, Reutter and Vrgoč), and the proof builds on the universality construction.

## Depends on

- [Regular expressions with binding and nesting levels](regular-expressions-with-binding-and-levels.md)
- [Decidability by multi-stack machines](../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [The Post correspondence problem is undecidable](../../../TheoryOfComputation/undecidable-problems/post-correspondence-problem/exists-not-tm2-decidable-pcp.md)

## Expansion

The proof reduces from the Post correspondence problem. For an instance $\{(u_1, v_1), \dots, (u_n, v_n)\}$, a solution is encoded by a data word $w_1 \# z \# w_2$ with $z \in L(r_i)$, $w_1$ a sequence of blocks $\flat_{l_j} u_{l_j}$ and $w_2$ the matching blocks $\flat_{l_j} v_{l_j}$ (the source writes a dollar sign where this page writes $\flat$), where equal data values link the $j$-th dollar and the $p$-th letter on the two sides. An expression $\Delta$ in $E_{i+1}$ (it binds a value to the left of $\# r_i \#$ and tests it to the right) defines all words $w_1' \# z \# w_2'$ with $z \in L(r_i)$ that do not encode a solution. If the instance has no solution, $\Delta$ is equivalent to $\Gamma^\ast \# r_i \# \Gamma^\ast$, which lies in $F_i$. If it has a solution, a pumping argument on the automaton of a hypothetical equivalent $F_i$ expression, as in the strictness proof for the hierarchy (Lemma 3.2), produces a word that $\Delta$ must accept but that encodes a solution, a contradiction.

A good expansion links the pumping lemma for $E_i$ expressions (Lemma 3.2 of the source) and the correctness lemma for $\Delta$ (Lemma A.2), which have no pages; the undecidability of the Post correspondence problem is linked above.

## Sources

- M. Praveen and B. Srivathsan, "Nesting Depth of Operators in Graph Database Queries: Expressiveness vs. Evaluation Complexity", 43rd International Colloquium on Automata, Languages, and Programming (ICALP 2016), Leibniz International Proceedings in Informatics (LIPIcs) 55, pp. 117:1–117:14, 2016, <https://doi.org/10.4230/LIPIcs.ICALP.2016.117>. Read in arXiv:1603.00658v2, <https://arxiv.org/abs/1603.00658v2>; Theorem 3.4 with its proof idea in Section 3 and its proof in the appendix (Lemma A.2), Definition 3.1 and Lemma 3.2, numbering of arXiv:1603.00658v2.
