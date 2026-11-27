# Datalog on K-relations is the least solution of an algebraic system

Let $K$ be a commutative $\omega$-continuous semiring. An algebraic system $x_i = P_i(x_1, \dots, x_n)$,
$1 \le i \le n$, with polynomials $P_i \in K[x_1, \dots, x_n]$ defines an $\omega$-continuous map
$f_P : K^n \to K^n$, whose least fixed point $\sup_m f_P^m(0, \dots, 0)$ is the solution of the system. For a Datalog
query $q$ and a $K$-relation $R$, introduce a variable for each tuple that can appear in an intensional relation and
let the system $\bar Q = T_q(R, \bar Q)$ express, for each such tuple, the sum over its immediate derivations by the
rules of $q$ of the products of the tags of the premises. Then for every tuple $t$ with $q(R)(t) \ne 0$, $q(R)(t)$
equals the component for $t$ of the solution of this system.

## Depends on

- [Datalog on K-relations over ω-continuous semirings](datalog-on-k-relations-over-omega-continuous-semirings.md)

## Informally uses

- [Least model equals least fixpoint for Datalog](../datalog/least-model-equals-least-fixpoint-for-datalog.md)

## Sources

- T. J. Green, G. Karvounarakis and V. Tannen, *Provenance semirings*, PODS 2007, Definition 5.5 and Theorem 5.6. <http://www.cs.ucdavis.edu/~green/papers/pods07.pdf>
