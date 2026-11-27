# Regular expressions with binding and nesting levels

Regular expressions with binding (REWBs) define languages of data words: a letter can bind its data value to a variable, and later letters can test their values against it. The levels $F_i$ count how deeply bindings and Kleene stars nest inside each other, and they form a strict hierarchy of data languages.

**Data words.** Fix a finite alphabet $\Sigma$ and an infinite set $\mathcal{D}$ of data values. A data word is a finite sequence $\binom{a_1}{d_1} \cdots \binom{a_n}{d_n}$ with $a_i \in \Sigma$ and $d_i \in \mathcal{D}$; a data language is a set of data words. Data words label the paths of data graphs, graph databases whose edges carry a letter and a data value.

**Syntax (Libkin, Tan and Vrgoč; levels by Praveen and Srivathsan).** For variables $x_1, \dots, x_k$ the conditions $\mathcal{C}_k$ are the Boolean combinations of $x_i^{=}$ and $x_i^{\ne}$. A data value $d$ and a partial valuation $\nu : \{x_1, \dots, x_k\} \to \mathcal{D}$ satisfy $x_i^{=}$ if $\nu(x_i) = d$, and $x_i^{\ne}$ if $\nu(x_i) \ne d$. REWBs over $\Sigma[x_1, \dots, x_k]$ are

$$
r ::= \varepsilon \mid a \mid a[c] \mid r + r \mid r \cdot r \mid r^\ast \mid a{\downarrow}_x(r)
$$

with $a \in \Sigma$, $c \in \mathcal{C}_k$ and $x \in \{x_1, \dots, x_k\}$. In $a{\downarrow}_x(r)$ the expression $r$ is the scope of the binding; a variable is free if it occurs outside the scope of every binding of it.

**Semantics.** For a valuation $\nu$ defined on the free variables of $r$, $L(\varepsilon, \nu) = \{\varepsilon\}$, $L(a, \nu) = \{\binom{a}{d} \mid d \in \mathcal{D}\}$, $L(a[c], \nu) = \{\binom{a}{d} \mid d, \nu \models c\}$, union, concatenation and star act as usual, and

$$
L(a{\downarrow}_{x_i}(r), \nu) = \bigcup_{d \in \mathcal{D}} \Bigl\{\tbinom{a}{d}\Bigr\} \cdot L(r, \nu[x_i \to d]).
$$

The language of $r$ is $L(r) = \bigcup_\nu L(r, \nu)$ over all valuations defined on its free variables. For example $a{\downarrow}_x(b[x^{=}]^\ast)$ defines the data words $a b^\ast$ in which all positions carry the same value.

**Levels.** By induction on $i \ge 1$,

$$
F_0 ::= \varepsilon \mid a \mid a[c] \mid F_0 + F_0 \mid F_0 \cdot F_0 \mid F_0^\ast, \qquad E_i ::= F_{i-1} \mid E_i + E_i \mid E_i \cdot E_i \mid a{\downarrow}_{x_j}(E_i), \qquad F_i ::= E_i \mid F_i + F_i \mid F_i \cdot F_i \mid F_i^\ast.
$$

So $E_i$ adds bindings over iterations of level $i - 1$, and $F_i$ adds iterations over bindings of $E_i$: an expression in $F_i$ nests iterated bindings to depth $i$. Every REWB lies in some $F_i$. The hierarchy is strict: for each $i$ the expression $r_i$, with $r_1 = (a_1{\downarrow}_{x_1}(b_1[x_1^{=}]))^\ast$ and $r_i = (a_i{\downarrow}_{x_i}(r_{i-1}\, b_i[x_i^{=}]))^\ast$, lies in $F_i$, but no expression in $E_i$ (in particular none in $F_{i-1}$) defines $L(r_i)$.

## Depends on

- [Language denoted by a regular expression](../../../TheoryOfComputation/regular-languages/automata-and-expressions/kleene-s-theorem/is-regex-denoted.md)

## Proof depends on

None.

## Expansion

As query languages for data graphs, REWBs return the pairs of nodes joined by a path whose data word lies in the language. Evaluating an $E_i$ query is in the $i$-th level $\Sigma_i$ of the polynomial hierarchy, while unrestricted REWB evaluation is PSPACE-complete. The strictness proof adapts the star-height hierarchy argument for regular expressions.

## Sources

- M. Praveen and B. Srivathsan, "Nesting Depth of Operators in Graph Database Queries: Expressiveness vs. Evaluation Complexity", 43rd International Colloquium on Automata, Languages, and Programming (ICALP 2016), Leibniz International Proceedings in Informatics (LIPIcs) 55, pp. 117:1–117:14, 2016, <https://doi.org/10.4230/LIPIcs.ICALP.2016.117>. Read in arXiv:1603.00658v2, <https://arxiv.org/abs/1603.00658v2>; Definitions 2.1 and 2.2 (REWBs and their semantics), Definition 2.3 (data graphs), the grammar of Section 3, Definition 3.1, Theorem 3.3 and Theorem 4.2, numbering of arXiv:1603.00658v2.
- Leonid Libkin, Tony Tan and Domagoj Vrgoč, "Regular Expressions with Binding over Data Words for Querying Graph Databases", Developments in Language Theory (DLT 2013), Lecture Notes in Computer Science 7907, pp. 325–337, Springer, 2013, <https://doi.org/10.1007/978-3-642-38771-5_29> (origin of REWBs, cited by the first source; not read).
