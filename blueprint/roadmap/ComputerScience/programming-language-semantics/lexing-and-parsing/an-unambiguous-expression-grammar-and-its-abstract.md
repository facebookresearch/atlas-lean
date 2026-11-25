# An unambiguous expression grammar and its abstract syntax

Consider the stratified expression grammar over numerals $n$:

$$
E \to E + T \mid T, \qquad T \to T * F \mid F, \qquad F \to (E) \mid n.
$$

Abstract syntax trees are numerals, sums $a \oplus b$ and products $a \otimes b$. A parse tree maps to an abstract syntax tree by sending $E \to E + T$ to $\oplus$, $T \to T * F$ to $\otimes$, and $F \to (E)$ to the tree of $E$, and by passing through the unit productions.

1. **Unambiguity.** The grammar is unambiguous: every word has at most one parse tree from each nonterminal.
2. **Precedence and associativity.** Under this map, $*$ binds tighter than $+$, and both operators associate to the left. For example, $2 + 3 * 4$ maps to $2 \oplus (3 \otimes 4)$, and $2 + 3 + 4$ maps to $(2 \oplus 3) \oplus 4$.
3. **Printing and parsing.** Print an abstract syntax tree with minimal parentheses:
    - parenthesize a sum when it is an operand of a product or the right operand of a sum;
    - parenthesize a product when it is the right operand of a product.

    Parsing the printed word with $E$ returns the original tree.

**Proof.**
- *Part 1,* by strong induction on the length of the word. Call an occurrence of $+$ or $*$ *top-level* if it lies outside all parentheses.
    - An $E$-parse uses $E \to E + T$ exactly when the word has a top-level $+$, and then it must split at the last such $+$, because a $T$-word has no top-level $+$.
    - Likewise a $T$-parse splits at the last top-level $*$, because an $F$-word has none.
    - An $F$-word is a numeral or a parenthesized $E$-word.

    So each step of the parse is forced, and the induction hypothesis applies to the shorter parts.
- *Part 2.* Splitting at the last top-level operator makes the left operand absorb all earlier operators of the same level, which gives left associativity. A top-level $+$ is always split before any $*$, which gives the precedence of $*$.
- *Part 3,* by induction on the tree. The printed operands of a sum are an $E$-word on the left and a $T$-word on the right, since a right operand that is a sum is parenthesized. The printed operands of a product are a $T$-word and an $F$-word. By part 1 the unique parse reproduces the tree.

## Background

- [Ambiguous grammars](../../../TheoryOfComputation/context-free-languages/grammars-and-pushdown-automata/ambiguity-of-context-free-grammars/is-ambiguous.md)

## Sources

- J. Prins, *Operator Precedence and Stratified Grammars*, Lecture 7 of COMP 520: Compilers, University of North Carolina, 2022, <https://www.cs.unc.edu/~prins/Classes/520/LECS/07-Precedence.pdf>: slides 3–5 (the ambiguous expression grammar, the stratified grammar $E ::= E + T \mid T$, $T ::= T * F \mid F$, $F ::= (E) \mid num$, and how it encodes associativity and precedence) and slide 8 (building abstract syntax trees bottom up). The proofs above are written out here.
- J. E. Hopcroft and J. D. Ullman, *Introduction to Automata Theory, Languages, and Computation*, Addison-Wesley, 1979.
