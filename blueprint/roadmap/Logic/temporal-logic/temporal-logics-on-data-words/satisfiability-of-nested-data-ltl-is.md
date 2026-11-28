# Satisfiability of nested data LTL is undecidable

Satisfiability of nested data LTL over multi-attributed data words is undecidable over finite and over infinite words, and its fragment without the future class operators $\mathsf X^{=}$ and $\mathsf U^{=}$ is undecidable over infinite words.

**Theorem (Decker, Habermehl, Leucker and Thoma).** Satisfiability of [nested data LTL](nested-data-ltl.md) is undecidable over finite data words and over infinite data words. Satisfiability of its fragment ND-LTL$^-$, without the future class operators $\mathsf X^{=}$ and $\mathsf U^{=}$, is undecidable over infinite data words (Theorem 5 of the source).

In contrast, satisfiability of ND-LTL$^-$ over finite words and of ND-LTL$^+$ over finite and infinite words is decidable (Theorem 7, in Section 6 of the source), and Ackermann-hard (Theorem 4). Extending BD-LTL$^\pm$ with unrestricted tuple navigation is already undecidable (Proposition 2).

## Depends on

- [Nested data LTL](nested-data-ltl.md)
- [Decidability by multi-stack machines](../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [Two-counter machines are universal](../../../TheoryOfComputation/equivalence-of-models/counter-machines/two-counter-machines-are-universal.md)

## Expansion

For a counter system with resets, an ND-LTL$^-$ formula over the propositions for its control states, for the operations $\mathit{inc}$, $\mathit{dec}$, $\mathit{res}$ and for its counters is satisfied exactly by data words whose string projections are runs of the system and whose data match each decrement of a counter with an earlier increment, keeping counter values non-negative (Lemma 4); a run projection must admit such data, and not every data decoration of it is a witness. For infinite words, the formula $\mathsf{GF}\,q$ expresses repeated control-state reachability in counter systems with resets, which is undecidable. For finite words, the formula $\bigwedge_{c \in C} \mathsf G((\mathit{inc} \wedge \mathsf X c) \to \mathsf C^0_{x_c}\mathsf X^{=}(\mathit{dec} \wedge \mathsf X c))$ requires every increment to be followed by a decrement of the same counter before the next reset, so that resets become zero tests and reachability for Minsky machines, which is undecidable, reduces to satisfiability.

## Sources

- N. Decker, P. Habermehl, M. Leucker and D. Thoma, "Ordered Navigation on Multi-attributed Data Words", in *CONCUR 2014 – Concurrency Theory*, Lecture Notes in Computer Science 8704, Springer, 2014, pp. 497–511, <https://doi.org/10.1007/978-3-662-44584-6_34>; read as arXiv:1404.6064v1, <https://arxiv.org/abs/1404.6064v1>: Section 5: Proposition 2, Lemma 4, Theorems 4 and 5 and the arguments following Theorem 4; Section 6 (Theorem 7).
