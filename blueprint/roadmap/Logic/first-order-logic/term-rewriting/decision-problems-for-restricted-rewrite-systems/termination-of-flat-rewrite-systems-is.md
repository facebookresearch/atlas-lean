# Termination of flat rewrite systems is undecidable

Termination of finite term rewriting systems stays undecidable when every rule has both sides of height at most one, and already when variables occur only at depth at most one.

**Theorem (Barguñó, Godoy, Huntingford and Tiwari).** A term is *shallow* if all its variable positions are at depth $0$ or $1$, and *flat* if its height is at most $1$; a rule $l \to r$ is shallow (flat) if both $l$ and $r$ are, and a [term rewriting system](../../automated-deduction/term-rewriting-systems.md) is shallow (flat) if all its rules are. A system $R$ over a finite signature is *terminating* if there is no infinite derivation $s_0 \to_R s_1 \to_R \cdots$ from any term over that signature; an instance is a finite signature with a finite system over it. Then:

1. termination of finite shallow term rewriting systems is undecidable (Theorem 8.1 of the source, by a reduction from the Post correspondence problem with nonempty words);
2. termination of finite flat term rewriting systems is undecidable (Theorem 8.2).

Termination of general finite systems is [undecidable](../termination-of-term-rewriting-is-undecidable.md). By contrast, termination from a given term is decidable for right-flat systems, even modulo a permutative theory (Theorem 4.10); innermost termination is decidable for shallow systems (Section 5 of the source); and termination is decidable for systems whose right-hand sides are shallow and linear (Section 6).

## Depends on

- [Term rewriting systems](../../automated-deduction/term-rewriting-systems.md)
- [Decidability by multi-stack machines](../../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)
- [Abstract reduction system](../abstract-reduction-system.md)

## Proof depends on

- [The Post correspondence problem is undecidable](../../../../TheoryOfComputation/undecidable-problems/post-correspondence-problem/exists-not-tm2-decidable-pcp.md)
- [Instances with nonempty words](../../../../TheoryOfComputation/undecidable-problems/post-correspondence-problem/nonempty-words.md)

## Expansion

*Shallow systems.* For an instance $\langle u_1, v_1\rangle, \ldots, \langle u_n, v_n\rangle$ of the Post correspondence problem with nonempty words, a shallow system $R$ over unary symbols $U_{i,j}$, $V_{i,j}$, $P_{i,j}$ and symbols $f_1, f_2, f_3$ checks, in a loop $f_1 \to f_2 \to f_3 \to f_1$ at the root, that two arguments encode the same index sequence and the same word through the $u_i$ and the $v_i$. A solution $i_1 \cdots i_k$ gives an infinite derivation from a ground term $f_1(s_{uu}, s_{vv})$; conversely, since every rule preserves or decreases height, if $R$ is not terminating one can choose an infinite derivation, from an initial term of minimal height, that has infinitely many root steps (an infinite derivation under a fixed context need not), and its arguments must encode a solution. Hence the instance has a solution iff $R$ is not terminating.

*Flat systems.* Standard transformations, restricting the signature to one non-constant symbol (Lemma 3.1) and turning shallow terms into flat ones (Lemmas 3.2 and 3.3), preserve termination, which transfers the first part to flat systems. The proof uses the undecidability of the Post correspondence problem restricted to instances with nonempty words; a good expansion links a page for it.

## Sources

- L. Barguñó, G. Godoy, E. Huntingford and A. Tiwari, "Termination of Rewriting with Right-Flat Rules Modulo Permutative Theories", *Logical Methods in Computer Science* 6(3), 2010, paper 8, <https://doi.org/10.2168/LMCS-6(3:8)2010>; read as arXiv:1006.0706v3, <https://arxiv.org/abs/1006.0706v3>: Section 2 (shallow, flat and right-flat terms and rules, termination), Section 3 (Lemmas 3.2 and 3.3), Theorem 4.10, Sections 5 and 6, and Section 8 (Theorems 8.1 and 8.2 with the proof of Theorem 8.1).
