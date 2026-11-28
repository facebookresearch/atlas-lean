# The term algebra modulo E is an E-algebra

Let $E$ be a set of equations over $T_\Sigma(X)$, for a countably infinite set $X$ of variables, so that $T_\Sigma(X)$ is nonempty. For $t \in T_\Sigma(X)$ let $[t] = \{t' \mid E \vdash t \approx t'\}$, derivability being that of the [equational calculus](equational-calculus.md). The $\Sigma$-algebra $T_\Sigma(X)/E$ has universe $\{[t] \mid t \in T_\Sigma(X)\}$ and interprets a function symbol $f$ of arity $n$ by $f([t_1], \dots, [t_n]) = [f(t_1, \dots, t_n)]$. This interpretation is well defined: $[t_i] = [t'_i]$ for all $i$ implies $[f(t_1, \dots, t_n)] = [f(t'_1, \dots, t'_n)]$. Moreover $T_\Sigma(X)/E$ is an [E-algebra](equational-consequence-and-e-algebras.md).

**Proof.** Well-definedness is the Congruence rule. For an equation $\forall x_1 \dots x_n\,(s \approx t)$ of $E$ and values $[v_1], \dots, [v_n]$ of its variables, let $\sigma = \{x_i \mapsto v_i\}$; by structural induction $s$ and $t$ evaluate to $[s\sigma]$ and $[t\sigma]$, which are equal by the Instance rule.

## Depends on

- [Equational calculus](equational-calculus.md)
- [Equational consequence and E-algebras](equational-consequence-and-e-algebras.md)

## Sources

- U. Waldmann, *Automated Reasoning*, lecture notes, Max Planck Institute for Informatics, winter semester 2019/20, <https://rg1-teaching.mpi-inf.mpg.de/autrea-ws19/script.pdf>, Section 4.2, the quotient algebra construction and Lemmas 4.3 and 4.4 with their proofs, p. 108.
