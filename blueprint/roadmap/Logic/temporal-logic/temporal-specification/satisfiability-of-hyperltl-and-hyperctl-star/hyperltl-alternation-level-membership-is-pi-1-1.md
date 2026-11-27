# Membership in a HyperLTL alternation level is Π¹₁-complete

For each fixed $n > 0$, deciding whether a HyperLTL sentence is equivalent to some sentence with at most $n$ alternating blocks of trace quantifiers starting with an existential block is $\Pi^1_1$-complete, as hard as HyperLTL unsatisfiability.

**Theorem (Fortin, Kuijer, Totzke and Zimmermann).** Fix a finite set $AP$ of atomic propositions. A [HyperLTL](../hyperltl.md) formula is a $\Sigma_0$- and $\Pi_0$-formula if it is quantifier-free; it is a $\Sigma_n$-formula if it has the form $\exists\pi_1 \cdots \exists\pi_k.\,\psi$ with $\psi$ a $\Pi_{n-1}$-formula, and a $\Pi_n$-formula if it has the form $\forall\pi_1 \cdots \forall\pi_k.\,\psi$ with $\psi$ a $\Sigma_{n-1}$-formula, where $k = 0$ is allowed. Two sentences are *equivalent* if they have the same models among all sets $T \subseteq (2^{AP})^\omega$. For every fixed $n > 0$, the problem asking whether a given HyperLTL sentence is equivalent to some $\Sigma_n$-sentence is $\Pi^1_1$-complete, where $\Pi^1_1$ is the class of complements of $\Sigma^1_1$ sets of natural numbers.

## Depends on

- [HyperLTL](../hyperltl.md)

## Proof depends on

- [HyperLTL satisfiability is Σ¹₁-complete](hyperltl-satisfiability-is-sigma-1-1-complete.md)

## Expansion

*Upper bound.* By the $\Sigma^1_1$-completeness of satisfiability, equivalence of two sentences is $\Pi^1_1$ (non-equivalence is satisfiability of a Boolean combination, which HyperLTL expresses after prenexing). A sentence is equivalent to a $\Sigma_n$-sentence iff it is equivalent to one of the countably many, effectively enumerable $\Sigma_n$-sentences, and $\Pi^1_1$ is closed under this number quantifier.

*Lower bound.* The proof reduces HyperLTL unsatisfiability, which is $\Pi^1_1$-complete. Theorem 4.2 provides, for each $n$, a $\Sigma_{n+1}$-sentence $\varphi_{n+1}$ not equivalent to any $\Sigma_n$-sentence whose models are finite sets of traces in $(2^{AP})^* \emptyset^\omega$. From a sentence $\varphi$ one builds a sentence $\psi$ whose models are "disjoint unions", splitting both the traces and the time line, of a model of $\varphi_{n+1}$ and a model of $\varphi$; then $\psi$ is equivalent to a $\Sigma_n$-sentence (namely to an unsatisfiable one) iff $\varphi$ is unsatisfiable.

## Sources

- M. Fortin, L. B. Kuijer, P. Totzke and M. Zimmermann, "HyperLTL Satisfiability Is Highly Undecidable, HyperCTL* is Even Harder", *Logical Methods in Computer Science* 21(1), 2025, article 3, <https://doi.org/10.46298/lmcs-21(1:3)2025>; numbers from arXiv:2303.16699v5, <https://arxiv.org/abs/2303.16699v5>: Section 4.1 (the quantifier alternation hierarchy), Theorem 4.2, and Theorem 4.10 with its proof (Lemmas 4.11 to 4.13).
