# Hilbert's tenth problem for term algebras with a substitution operator is undecidable

For the term algebra over a finite signature with a constant and a function symbol of arity at least two, expanded by the operator that substitutes one ground term for another, no algorithm decides which equations between terms have a solution.

**Theorem (Murwanashyaka).** Let $\mathcal L$ be a finite signature with at least one constant symbol and at least one function symbol of arity at least $2$, and let $\mathcal T$ be the term algebra of variable-free $\mathcal L$-terms expanded by the *substitution operator* $t[r \mapsto s]$, the term obtained from $t$ by replacing every occurrence of the subterm $r$ by $s$. The analogue of Hilbert's tenth problem for $\mathcal T$, deciding for given terms $s, t$ in the expanded language whether the sentence $\exists \vec x\,[s = t]$ is true in $\mathcal T$, is undecidable (Computability 2024 version). For the signature with one constant $\bot$ and one binary function $\langle\cdot, \cdot\rangle$ this is Theorem 22 of the arXiv version, which also shows that the existential theory of this structure is undecidable (Theorem 20).

The full first-order theory of a term algebra with the subterm relation is undecidable, but its existential fragment is decidable (NP-complete, Venkataraman); the substitution operator makes already the existential fragment, and even single equations, undecidable.

## Depends on

- [Complete theory of a first-order structure](../../first-order-logic/theory-of-structure.md)

## Proof depends on

- [Davis–Putnam–Robinson–Matiyasevich theorem](../../../TheoryOfComputation/undecidable-problems/diophantine-sets-and-hilbert-s-tenth-problem/dprm-theorem.md)

## Expansion

In the arXiv version the arithmetic $(\mathbb N, 0, 1, +, \times)$ is existentially interpreted in the expanded binary term algebra (Theorem 20), so the existential theory is undecidable by the undecidability of Hilbert's tenth problem; every existential sentence is then effectively reduced to a finite disjunction of sentences $\exists\vec x\,[s = t]$, which gives Theorem 22. The refereed version gives a different proof that does not rely on the solution of Hilbert's tenth problem; that proof is not reproduced here, so the general case remains a node to expand.

## Sources

- J. Murwanashyaka, "Hilbert's tenth problem for term algebras with a substitution operator", *Computability*, 2024, pp. 1–25, <https://doi.org/10.3233/COM-230444>; read in its open abstract at that address, which states the result for every finite signature with a constant and a function symbol of arity at least two, proved without Hilbert's tenth problem; the proof itself was not read.
- J. Murwanashyaka, "Hilbert's Tenth Problem for Term Algebras with a Substitution Operator", in *Revolutions and Revelations in Computability (CiE 2022)*, Lecture Notes in Computer Science, Springer, 2022, pp. 196–207, <https://doi.org/10.1007/978-3-031-08740-0_17>: the conference version.
- J. Murwanashyaka, "Undecidability in First-Order Theories of Term Algebras Extended with a Substitution Operator", arXiv:2111.00573v1, <https://arxiv.org/abs/2111.00573v1>, read beside the refereed versions: Section 1, Theorems 20 and 22.
