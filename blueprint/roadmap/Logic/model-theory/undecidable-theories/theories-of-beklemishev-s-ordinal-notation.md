# Theories of Beklemishev's ordinal notation systems below ε₀ are undecidable

The elementary theory of Beklemishev's notation system for ε₀, built from words of reflection operators of the provability logic GLP, is undecidable, and so is the theory of the fragment for ω₄ and of every larger fragment with only the order and two of the operators.

**Theorem (Pakhomov).** Let $W^\omega$ be the set of finite words over the alphabet $\mathbb N$, with $\Lambda$ the empty word, and for $\alpha \le \omega$ let $W^\alpha$ be the set of words whose letters are all at most $\alpha$. For a word $A = n_1 \cdots n_k$ let $A^\#$ be the [worm](../../modal-logic/reflection-calculus-and-worms/worm.md) $\langle n_k\rangle \cdots \langle n_1\rangle\top$, that is, the worm written by the reversed word. Put $A \sim B$ iff $\mathsf{GLP} \vdash A^\# \leftrightarrow B^\#$, $A \prec B$ iff $A^\# <_0 B^\#$ in the [order on worms](../../modal-logic/reflection-calculus-and-worms/worm-lt.md), that is, $\mathsf{GLP} \vdash B^\# \to \langle 0\rangle A^\#$, and $a_i(A) = Ai$, so that $(a_i(A))^\# = \langle i\rangle A^\#$. By the [order type of worms](../../modal-logic/reflection-calculus-and-worms/exists-worm-ordinal.md), $(W^\omega/{\sim}, \prec)$ is isomorphic to $(\varepsilon_0, <)$; the fragments $W^n$ give notation systems for the towers $\omega_{n+1}$ ($\omega_0 = 1$, $\omega_{n+1} = \omega^{\omega_n}$), and:

1. the elementary theory $\mathrm{Th}(W^\omega/{\sim}, \prec, \Lambda, a_0, a_1, \ldots)$ is undecidable;
2. for every $\alpha$ with $3 \le \alpha \le \omega$, the elementary theory $\mathrm{Th}(W^\alpha/{\sim}, \prec, a_1, a_3)$ is undecidable;
3. for every $\alpha$ with $2 \le \alpha \le \omega$, the elementary theory $\mathrm{Th}(W^\alpha/{\sim}, \prec, \Lambda, a_0, a_1, a_2)$ is decidable.

The source defines $\sim$, $\prec$ combinatorially and proves the agreement with $\mathsf{GLP}$. In terms of ordinals, the theories are undecidable for the fragments for $\omega_4$ and above and decidable, with $\Lambda, a_0, a_1, a_2$, for the fragments for $\omega_3$ and above. The elementary theory of every ordinal $(\alpha, <)$ is decidable (Mostowski and Tarski), and with the meet operation $\wedge$ on words the theories of $(W^\alpha/{\sim}, \wedge)$ are undecidable for $2 \le \alpha \le \omega$ (earlier work cited by the source).

## Depends on

- [Worm](../../modal-logic/reflection-calculus-and-worms/worm.md)
- [The order `<₀` on worms](../../modal-logic/reflection-calculus-and-worms/worm-lt.md)
- [Complete theory of a first-order structure](../../first-order-logic/theory-of-structure.md)
- [Decidability by multi-stack machines](../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

None.

## Expansion

For part 2 the class of finite sets carrying two strict linear orders has a hereditarily undecidable elementary theory. A parametric relative interpretation of this theory in $\mathrm{Th}(W^3/{\sim}, \prec, a_1, a_3)$, with one parameter, represents every finite structure with two linear orders, so the latter theory is undecidable (for $\alpha = 3$; the source then treats every $\alpha \ge 3$). Part 3 interprets the structures with $\Lambda, a_0, a_1, a_2$ in the weak monadic theory of $(\omega_\alpha, R)$, with $R$ a relation tied to the standard cofinal sequences, which is decidable by Braud's theorem.

## Sources

- F. N. Pakhomov, "On elementary theories of ordinal notation systems based on reflection principles", *Proceedings of the Steklov Institute of Mathematics* 289(1):194–212, 2015, <https://doi.org/10.1134/S0081543815040124>; read as arXiv:1312.3002v1, <https://arxiv.org/abs/1312.3002v1>, whose main theorems are cited here by content (their labels do not survive in the text of that copy), with the numbered Fact 1, Fact 2 and Lemma 8 cited by number: the Introduction (the notation system, the three results, related work), the section "Ordinal notation systems with undecidable elementary theories" (Fact 2, on hereditary undecidability under interpretation, and Lemma 8, for $W^3$; Fact 1 gives the equivalences of words), and the section "Some theories of ordinals and words" (decidability via weak monadic theories).
