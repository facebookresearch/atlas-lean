# Local confluence of terminating LCTRSs is undecidable

Unlike for finite terminating term rewriting systems, where Knuth and Bendix's critical pair criterion decides confluence, local confluence of terminating logically constrained rewrite systems is undecidable, even with constraints from linear integer arithmetic, a decidable theory.

**Theorem (Schöpf, Mitterwallner and Middeldorp).** There is no algorithm that decides, given a finite terminating [LCTRS](logically-constrained-term-rewriting-system.md), whether it is locally confluent. This holds already for LCTRSs over the theory of integers whose rules use the theory symbols $>$, $+$, $\cdot$, $=$ and $\wedge$, in constraints that lie in the decidable fragment of linear integer arithmetic (every multiplication has a constant factor). An instance is a finite set of constrained rules, written as finite terms with integer value constants. The proof (Theorem 1 of the source) reduces from the Post correspondence problem over $\{0, 1\}$.

Since a terminating relation is confluent iff it is locally confluent ([Newman's lemma](../newman-s-lemma.md)), confluence of terminating LCTRSs is undecidable as well, as the source states. For finite terminating plain term rewriting systems confluence is decidable by joinability of critical pairs.

## Depends on

- [Logically constrained term rewriting system](logically-constrained-term-rewriting-system.md)
- [Confluence of a relation](../confluence-of-a-relation.md)
- [Term rewriting systems](../../automated-deduction/term-rewriting-systems.md)
- [Decidability by multi-stack machines](../../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [The Post correspondence problem is undecidable](../../../../TheoryOfComputation/undecidable-problems/post-correspondence-problem/exists-not-tm2-decidable-pcp.md)
- [Newman's lemma](../newman-s-lemma.md)

## Expansion

From an instance $P = \{(\alpha_1, \beta_1), \ldots, (\alpha_N, \beta_N)\}$ of the Post correspondence problem over $\{0, 1\}$, with $\alpha_i \neq \beta_i$ for some $i$, candidate index strings are coded bijectively by natural numbers, $[i_0 i_1 \cdots i_k] = i_0 + i_1 N + \cdots + i_k N^k$. The LCTRS $\mathcal R_P$ has a rule $\mathsf{start} \to \mathsf{test}(\mathsf{alpha}(n), \mathsf{beta}(n))\ [n > 0]$, rules $\mathsf{alpha}(n) \to \alpha_i(\mathsf{alpha}(m))$ and $\mathsf{beta}(n) \to \beta_i(\mathsf{beta}(m))$ under the constraint $N \cdot m + i = n \wedge n > 0$ that unfold the number $n$ into the words $\alpha_{i_0}\cdots\alpha_{i_k}$ and $\beta_{i_0}\cdots\beta_{i_k}$, $\mathsf{alpha}(0) \to \mathsf e$, $\mathsf{beta}(0) \to \mathsf e$, and rules for $\mathsf{test}$ that compare the two words letter by letter and reduce to $\top$ if they are equal and to $\bot$ otherwise. The variable $n$ occurs only on the right of the start rule, so $\mathsf{start}$ rewrites to $\mathsf{test}(\mathsf{alpha}(n), \mathsf{beta}(n))$ for every $n > 0$, giving the constrained critical pair $\mathsf{test}(\mathsf{alpha}(n), \mathsf{beta}(n)) \approx \mathsf{test}(\mathsf{alpha}(m), \mathsf{beta}(m))$ $[n > 0 \wedge m > 0]$. Such a term reduces to $\top$ if $n$ codes a solution and to $\bot$ otherwise, and since $P$ is nontrivial the latter happens for some $n$; so all instances are joinable iff every $n > 0$ leads to $\bot$, that is, $\mathcal R_P$ is locally confluent iff $P$ has no solution. Termination follows from the recursive path order with precedence $\mathsf{start} > \mathsf{test} > \mathsf{alpha} > \mathsf{beta} > \cdots$ and the order $x > y \wedge x > 0$ on integers, since the constraint forces $n > m$.

## Sources

- J. Schöpf, F. Mitterwallner and A. Middeldorp, "Confluence of Logically Constrained Rewrite Systems Revisited", in *Automated Reasoning (IJCAR 2024), Part II*, Lecture Notes in Computer Science 14740, Springer, 2024, pp. 298–316, <https://doi.org/10.1007/978-3-031-63501-4_16>; numbers from arXiv:2402.13552v5, <https://arxiv.org/abs/2402.13552v5>: Section 3: Theorem 1 and its proof (the LCTRS $\mathcal R_P$), Example 3; Section 1 for confluence.
