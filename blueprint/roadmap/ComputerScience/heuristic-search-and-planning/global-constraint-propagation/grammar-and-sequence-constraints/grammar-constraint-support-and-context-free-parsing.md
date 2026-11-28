# Feasibility of GRAMMAR is as hard as context-free parsing

Deciding whether a GRAMMAR constraint has any solution (detecting disentailment) and context-free membership reduce to each other by constructions linear in the string length for a fixed grammar and alphabet; membership reduces to feasibility even for simple, hence deterministic and LL(1), grammars.

Use the [GRAMMAR constraint](grammar-constraint.md) and its Cartesian product languages $L(R_{D_1,\dots,D_n})$, grammars without empty productions, and $|G|=\sum_{A\to\alpha}|A\alpha|$. A grammar is in [Greibach normal form](../../../../TheoryOfComputation/context-free-languages/grammars-and-pushdown-automata/greibach-normal-form/is-greibach-normal-form.md) when every production has the form $A\to a\alpha$ with $a$ a terminal and $\alpha$ a string of nonterminals; it is **simple** when moreover, for every nonterminal $A$ and terminal $a$, there is at most one production $A\to a\alpha$.

**Theorem.**

1. Let $G$ be a grammar in Greibach normal form and $s$ a word of length $n$. In $O(|G|)$ time one can construct a simple grammar $G'$, and in $O(|G|n)$ time a Cartesian product language $L(R_{D_1,\dots,D_n})$, such that $L(G')\cap L(R_{D_1,\dots,D_n})\ne\emptyset$ iff $s\in L(G)$, that is, iff $\mathrm{GRAMMAR}(G',[X_1,\dots,X_n])$ with domains $D_1,\dots,D_n$ has a solution.
2. Conversely, let $G=\langle N,T,P,S\rangle$ be a grammar in Greibach normal form (the form the source's construction uses) and $L(R_{D_1,\dots,D_n})$ a Cartesian product language. In $O(|G|+|T|^2)$ time one can construct a grammar $G'$, and in $O(n|T|)$ time a word $s$ of length $n|T|$, such that $s\in L(G')$ iff $L(G)\cap L(R_{D_1,\dots,D_n})\ne\emptyset$.

Both constructions are linear in $n$ once the grammar (and, in item 2, the alphabet) is fixed; they are not linear jointly in the grammar and the string. So, for grammars in Greibach normal form, detecting disentailment of GRAMMAR, even restricted to simple grammars, is at least as hard as membership, and it can be done with any membership algorithm on a word of length $n|T|$. These statements concern feasibility only; they say nothing about pruning values, and do not make propagation faster than the $O(|G|n^3)$ CYK-based propagators.

## Depends on

- [GRAMMAR and REGULAR constraints](grammar-constraint.md): the constraint, Cartesian product languages and grammar size.
- [Greibach normal form](../../../../TheoryOfComputation/context-free-languages/grammars-and-pushdown-automata/greibach-normal-form/is-greibach-normal-form.md): the input form in both reductions.

## Proof depends on

None.

## Expansion

*Item 1.* Number the productions of $G$. For the $j$-th production $A\to a\alpha$ add a new terminal $(a,j)$ and the production $A\to(a,j)\alpha$ to $G'$; $G'$ is simple because distinct productions get distinct terminals. Let $D_i=\{(a,j):a=s_i\}$. A word of $L(G')$ in the product language spells $s$ after erasing the indices and records, letter by letter, a leftmost derivation of $s$ in $G$; conversely a derivation of $s$ labels each letter by the production that produced it.

*Item 2* (sketch in the source). Encode each position $i$ by a bitmap of length $|T|$ marking the terminals of $D_i$, and let $s$ be the concatenation of the $n$ bitmaps. Add $B\to0\mid1$, for the $j$-th terminal a nonterminal $T_j\to B^{j-1}1B^{|T|-j}$ accepting the bitmaps with a 1 in position $j$, and replace each production $A\to a\alpha$ ($a$ the $j$-th terminal) by $A\to T_j\alpha$.

The source adds two remarks that are not part of the statement: that Lee's connection between context-free parsing and Boolean matrix multiplication suggests a quadratic lower bound and, through item 2, an $O(n^{2.4})$ disentailment test with fast matrix multiplication (Lee's reduction applies to parsers that report which substrings derive which nonterminals, not to bare membership, so no unconditional lower bound follows); and that converting an arbitrary grammar to Greibach normal form costs a polynomial in $|G|$ (cited from Blum and Koch), which is needed to apply item 1 to arbitrary grammars. Simple languages are contained in the deterministic and in the LL(1) languages, so item 1 applies to those classes too.

## Sources

- G. Katsirelos, S. Maneth, N. Narodytska and T. Walsh, "Restricted global grammar constraints", *Principles and Practice of Constraint Programming – CP 2009*, Lecture Notes in Computer Science 5732 (2009), 501–508, doi:10.1007/978-3-642-04244-7_40. Simple grammars, Theorem 1 with proof, Corollary 1, and Theorem 2 with its proof sketch, §3 of arXiv:0906.5233v1, [https://arxiv.org/abs/0906.5233v1](https://arxiv.org/abs/0906.5233v1).
