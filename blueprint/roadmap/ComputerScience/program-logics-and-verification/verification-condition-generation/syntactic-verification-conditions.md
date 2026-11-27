# Syntactic verification conditions

Work with commands generated from assignments, sequencing, conditionals and while loops, and assertions of a first-order language with capture-avoiding substitution. A command is *properly annotated* if an assertion is inserted before each command $C_i$, $i > 1$, of a sequence $C_1; \dots; C_n$ that is not an assignment, and after the word $\mathtt{do}$ of every while loop (the loop invariant). For a properly annotated specification $\{P\}\, C\, \{Q\}$ the verification conditions are the assertions defined by recursion on $C$:

- for $\{P\}\ V := E\ \{Q\}$: the single condition $P \Rightarrow Q[E/V]$, where $Q[E/V]$ is capture-avoiding substitution of $E$ for the free occurrences of $V$ in $Q$;
- for $\{P\}\ \mathtt{if}\ S\ \mathtt{then}\ C_1\ \mathtt{else}\ C_2\ \{Q\}$: those of $\{P \wedge S\}\, C_1\, \{Q\}$ and of $\{P \wedge \neg S\}\, C_2\, \{Q\}$;
- for $\{P\}\ C_1; \dots; C_{n-1}; \{R\}\, C_n\ \{Q\}$ with $C_n$ not an assignment: those of $\{P\}\, C_1; \dots; C_{n-1}\, \{R\}$ and of $\{R\}\, C_n\, \{Q\}$;
- for $\{P\}\ C_1; \dots; C_{n-1}; V := E\ \{Q\}$: those of $\{P\}\, C_1; \dots; C_{n-1}\, \{Q[E/V]\}$;
- for $\{P\}\ \mathtt{while}\ S\ \mathtt{do}\ \{R\}\, C\ \{Q\}$: $P \Rightarrow R$, $R \wedge \neg S \Rightarrow Q$ and those of $\{R \wedge S\}\, C\, \{R\}$.

The conditions are formulas of the assertion language; no command occurs in them. The semantic [verification condition of an annotated command](vc.md) has the same shape, with assertions as predicates on states and state update in place of substitution.

## Depends on

- [First-order arithmetic as an assertion language](../hoare-logic/first-order-arithmetic-as-an-assertion-language.md)

## Proof depends on

Definition only; no proof prerequisites.

## Sources

- M. Gordon, *Background reading on Hoare Logic*, University of Cambridge Computer Laboratory, 2016, <https://www.cl.cam.ac.uk/archive/mjcg/HL/Notes/Notes.pdf>: Section 3.3 (properly annotated commands and specifications) and Section 3.4 (the rules for assignments, conditionals, sequences and WHILE-commands).
- T. Nipkow and G. Klein, *Concrete Semantics with Isabelle/HOL*, Springer, 2014, authors' copy <http://concrete-semantics.in.tum.de/concrete-semantics-brick.pdf>, Section 12.4, for the semantic counterpart and the remark that examples use syntactic assertions with substitution.
