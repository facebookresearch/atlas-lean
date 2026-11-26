# Restricted protocol theories and their secrecy problems

A role of a [well-founded protocol theory](well-founded-protocol-theories.md) is *restricted* if its role states come from a finite list $A_1, \dots, A_a$, its network predicates
from finite lists $NR_1, \dots, NR_n$ and $NS_1, \dots, NS_n$, and all its rules have the form $A_i(\dots), NR_j(\dots) \to \exists \dots.\ A_k(\dots), NS(\dots)$ with $i < k$. A protocol theory
$T = I \cup R \cup A$ is in *restricted form* if $I$ is a set of ground facts, $R$ is a role generation theory and $A$ is a finite set of restricted roles.

Let $\mathcal M$ be the [standard intruder theory](the-standard-dolev-yao-intruder-theory.md). The set $\mathrm{PA}$ of scenarios with an attack consists of the tuples
$(T, \mathcal M, S, n, r, k)$, with $T$ in restricted form and $S$ a ground term (the secret), such that some run of $T$ with $\mathcal M$ reaches a state containing $M(S)$ in which at
most $n$ protocol nonces and at most $r$ role instances occur and every fact has size at most $k$. The secrecy problems are:
$S_{\mathrm{size}=k}$ (given $T, \mathcal M, S$, is $(T, \mathcal M, S, n, r, k) \in \mathrm{PA}$ for some $n, r$?), $S_{\mathrm{nonce}b}$ (given $T, \mathcal M, S, n, k$, for some $r$?),
$S_{\mathrm{role}b}$ (given $T, \mathcal M, S, r, k$, for some $n$?) and $S_{\mathrm{nonce}b, \mathrm{size}=k}$ (given $T, \mathcal M, S, n$, for some $r$?).

## Depends on

- [Well-founded protocol theories](well-founded-protocol-theories.md)
- [The standard intruder theory in multiset rewriting](the-standard-dolev-yao-intruder-theory.md)

## Sources

- N. Durgin, P. Lincoln, J. Mitchell and A. Scedrov, "Multiset rewriting and the complexity of bounded security protocols", *Journal of Computer Security* 12(2):247–311, 2004, copy at <http://www-cs-students.stanford.edu/~nad/papers/msr-jcs215.pdf>: Section 5.1 (Definitions 5.1–5.2) and Section 5.2 (the set $\mathrm{PA}$ and the secrecy problems).
