# Candidate interpretation for superposition

Let $N$ be a set of clauses not containing the empty clause, and let $\succ$ and $\succ_C$ be the orderings of the [superposition calculus](superposition-calculus.md). For a set $R$ of ground rewrite rules, a ground equation $s \approx t$ is *true in $R$* if it holds in the [quotient](../equational-logic/term-algebra-modulo-an-equational-theory.md) $T_\Sigma(\emptyset)/R$ of the nonempty ground term algebra of the calculus's signature $\Sigma$, which has at least one constant symbol, which for convergent $R$ means that $s$ and $t$ are joinable by $\to_R$; a ground clause is true in $R$ if one of its literals is. By induction on $\succ_C$, define for every $C \in G_\Sigma(N)$ sets $E_C$ and $R_C = \bigcup_{D \prec_C C} E_D$ of ground rewrite rules: $E_C = \{s \to t\}$ if

1. $C = C' \vee s \approx t$,
2. $s \approx t$ is strictly maximal in $C$,
3. $s \succ t$,
4. $C$ is false in $R_C$,
5. $C'$ is false in $R_C \cup \{s \to t\}$, and
6. $s$ is irreducible with respect to $R_C$;

in this case $C$ is *productive*. Otherwise $E_C = \emptyset$. Finally $R_\infty = \bigcup_{D \in G_\Sigma(N)} E_D$.

## Depends on

- [Superposition calculus](superposition-calculus.md)
- [Term rewriting systems](../automated-deduction/term-rewriting-systems.md)
- [The term algebra modulo E is an E-algebra](../equational-logic/term-algebra-modulo-an-equational-theory.md)

## Sources

- U. Waldmann, *Automated Reasoning II*, lecture notes, Max Planck Institute for Informatics, summer semester 2024, <https://rg1-teaching.mpi-inf.mpg.de/autrea2-ss24/notes-current.pdf>, Section 3.4, the construction of candidate interpretations (Bachmair and Ganzinger), p. 54.
