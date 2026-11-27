# A finitely presented group in which triviality in all finite quotients is undecidable

There is a finitely presented group $G = \langle A \mid R \rangle$ in which no algorithm decides whether a given word has trivial image in every finite quotient, that is, trivial image in the profinite completion; the set of words with non-trivial image is recursively enumerable but not recursive.

There exist a finite set $A$ and a finite set $R$ of words such that, for $G = \langle A \mid R \rangle$ with profinite completion $\widehat{G}$, the set of reduced words

$$
\{ w \in F(A) : w \ne 1 \text{ in } \widehat{G} \}
$$

is recursively enumerable but not recursive (Theorem 2.1 of the Bridson–Wilton source). Here $F(A)$ is the free group on $A$, identified with the set of freely reduced words, and $w \ne 1$ in $\widehat{G}$ means that the image of $w$ in some finite quotient of $G$ is non-trivial.

The theorem is contained in Slobodskoi's proof that the universal theory of finite groups is undecidable (Theorem 2.2 of the Bridson–Wilton source); it can be read as a profinite analogue of the Novikov–Boone theorem. The uniform version, that no algorithm decides from a finite presentation and a word whether the word survives in some finite quotient, is the undecidability of the uniform word problem for finite groups.

## Depends on

- [Profinite completion](../profinite-rigidity/profinite-completion.md)
- [Group](../../group-basics/group.md)
- [Decidability by multi-stack machines](../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)
- [Recognizability by multi-stack machines](../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-recognizable.md)

## Proof depends on

- [Two-counter machines are universal](../../../TheoryOfComputation/equivalence-of-models/counter-machines/two-counter-machines-are-universal.md)

## Expansion

Recursive enumerability: enumerate the finite quotients of $G$ (finite groups with images of the generators satisfying $R$) and check $w$ in each. Slobodskoi's finitely presented group $G = \langle a_1, \dots, a_n \mid r_1, \dots, r_m \rangle$ encodes a two-tape Minsky machine $M$ computing a partial recursive function, with recursively inseparable sets $S_0$ (inputs $2^k$ on which $M$ halts) and $S_1$ (inputs on which some tape returns to its leftmost square infinitely often). For each $k$ Slobodskoi gives computable words $w_1^{(k)}, w_2^{(k)}$: if $k \in S_1$ both are trivial in every periodic quotient, in particular in every finite quotient (his Lemma 6, as recounted in the Bridson–Wilton source), and if $k \in S_0$ one of them survives in some finite quotient (his Lemma 7). If triviality in $\widehat{G}$ were decidable, the set $D$ of $k$ with $w_1^{(k)} = w_2^{(k)} = 1$ in $\widehat{G}$ would be recursive, contain $S_1$ and miss $S_0$, contradicting recursive inseparability.

## Sources

- M. R. Bridson and H. Wilton, "The triviality problem for profinite completions", Inventiones Mathematicae 202 (2015), no. 2, 839–874, https://doi.org/10.1007/s00222-015-0578-8; arXiv:1401.2273v3 (Theorem 2.1 and Theorem 2.2, Section 2 of arXiv:1401.2273v3).
