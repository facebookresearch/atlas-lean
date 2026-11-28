# Joint embedding for universal Horn sentences is undecidable

There is no algorithm that decides, given a universal Horn sentence in a finite relational signature with relation symbols of arity at most two, whether its class of finite models has the joint embedding property.

**Theorem (Bodirsky, Rydval and Schrottenloher).** Let $\tau$ be a finite relational signature. A *universal sentence* is $\forall x_1 \cdots \forall x_n\,\psi$ with $\psi$ quantifier-free, written as a conjunction of clauses (disjunctions of atomic and negated atomic formulas, including equalities); it is *Horn* if every clause contains at most one positive literal. For a universal sentence $\Phi$ let $[\![\Phi]\!]_{<\omega}$ be the class of finite models of $\Phi$; it is closed under substructures. There is no algorithm that decides, given a finite relational signature $\tau$ and a universal Horn sentence $\Phi$ over $\tau$, whether $[\![\Phi]\!]_{<\omega}$ has the [joint embedding property](joint-embedding-property.md), even if $\tau$ contains only relation symbols of arity at most two (Theorem 3 of the source). The signature is part of the input: the proof reduces universality of context-free grammars and uses one binary symbol for each symbol of the grammar.

The finite models of a universal sentence in a finite relational signature form the age of a structure iff they have the joint embedding property, so it is undecidable whether such a class is an age. By contrast, deciding whether a given universal sentence is equivalent to a universal Horn sentence is $\Pi^p_2$-complete (Proposition 1 of the source).

## Depends on

- [Joint embedding property](joint-embedding-property.md)
- [Decidability by multi-stack machines](../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [Whether a context-free grammar generates every word is undecidable](../../../TheoryOfComputation/undecidable-problems/undecidable-problems-for-context-free-grammars/exists-not-tm2-decidable-univ.md)

## Expansion

The proof reduces the universality problem for context-free grammars $G = (N, \Sigma, P, S)$, assuming without loss of generality $(A \to A) \in P$ for every nonterminal. The signature has unary symbols $I$, $T$ and a binary symbol $R_a$ for each $a \in N \cup \Sigma$. The sentence $\Phi_1$ contains, for every production $A \to a_1 \cdots a_n$, the Horn clause $\bigwedge_{i \in [n]} R_{a_i}(x_i, x_{i+1}) \Rightarrow R_A(x_1, x_{n+1})$, so that finite models derive along paths the nonterminals generating the word read on the path; $[\![\Phi_1]\!]_{<\omega}$ is closed under disjoint unions. A second sentence $\Phi_2$, depending only on $\Sigma$, contains Horn clauses that witness failures of the JEP unless they are prevented. Then $[\![\Phi_1 \wedge \Phi_2]\!]_{<\omega}$ has the JEP iff $L(G) = \Sigma^+$.

## Sources

- M. Bodirsky, J. Rydval and A. Schrottenloher, "Universal Horn Sentences and the Joint Embedding Property", *Discrete Mathematics & Theoretical Computer Science* 23(2), 2022, paper 4, <https://doi.org/10.46298/dmtcs.7435>; numbers from arXiv:2104.11123v6, <https://arxiv.org/abs/2104.11123v6>: Section 1 (ages and the JEP), Proposition 1, Theorem 3 and its proof.
