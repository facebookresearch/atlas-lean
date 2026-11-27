# p-optimal proof systems, E versus P/poly and hard stretching functions

At least one of three statements holds: no p-optimal propositional proof system exists, $\mathsf E\not\subseteq\mathsf{P/poly}$, or some subexponential-time function stretching inputs by one bit has a range meeting every infinite NP set (Krajíček).

**Theorem (Krajíček).** At least one of the following is true:

1. there is no p-optimal propositional proof system;
2. $\mathsf E\not\subseteq\mathsf{P/poly}$, where $\mathsf E$ is the class of languages decidable in deterministic time $2^{O(n)}$;
3. there is a function $h:\{0,1\}^*\to\{0,1\}^*$ with $|h(u)|=|u|+1$ for all $u$, computable in time $2^{O((\log n)^{\log\log n})}$, whose range intersects every infinite NP set.

**First-order version.** For a sound polynomial-time axiomatized theory $T\supseteq S^1_2$ there is a polynomial-time function $g_T$ with $|g_T(u)|=|u|+1$ whose range intersects every infinite definable set $A$ having a definition $\Phi$ for which $T$ proves all true sentences of the form $\exists y\,\forall x>y\,(\Phi(x)\to\neg(w\sqsubseteq x))$, with $w\in\{0,1\}^{|\Phi|+1}$ and $\sqsubseteq$ the initial-subword relation. Applied to the complement of the range of $g_T$, this shows that no sound polynomial-time theory $T\supseteq S^1_2$ is complete.

## Expansion

On input $u$ of length $n$, $g_T$ reads a formula $\Phi$ of length at most $\log n$ as a prefix of $u$, searches for $T$-proofs of size at most $\log n$ of the sentences above for all $w$ of length $|\Phi|+1$, and outputs $w_0u'$ for the first $w_0$ without such a proof, where $u=\Phi u'$; for large $n$ it always finds a prefix $w_0$ occurring infinitely often in $A$. For the propositional version, assume a p-optimal system $P$ and $\mathsf E\subseteq\mathsf{P/poly}$. The canonical propositional translations $\varphi_{n,w}$ of these $\Pi^b_1$-statements have trivial proofs in an ad hoc system, so p-optimality yields a polynomial-time function producing $P$-proofs of them; these proofs are bits of an $\mathsf E$ function and thus truth tables of circuits of size $(\log n)^{O(1)}$, which $h$ can search through in the stated time. Non-existence of a p-optimal system is equivalent to non-existence of a time-optimal proof search algorithm.

## Depends on

- [Optimal and p-optimal propositional proof systems](optimal-and-p-optimal-proof-systems.md)
- [The class P/poly](../../../../TheoryOfComputation/complexity-classes/time-and-space-complexity-classes/ppoly.md)
- [Buss's bounded arithmetic theories $S^i_2$ and $T^i_2$](../bounded-arithmetic-correspondences/buss-theories-s2i-and-t2i.md)

## Proof depends on

- [Cook's translation of $S^1_2$-proofs into extended Frege proofs](../bounded-arithmetic-correspondences/cook-translation-of-s21-into-extended-frege.md)

## Sources

- Jan Krajíček, "A proof complexity conjecture and the incompleteness theorem", *Journal of Symbolic Logic* 90(3):1206–1210, 2025 (published online 2023), doi:10.1017/jsl.2023.69, arXiv:2303.10637v2 (Section 2: the function $g_T$, Lemma 2.1, Theorem 2.2 and Corollary 2.3; Section 3: Theorem 3.1 and Lemma 3.2).
