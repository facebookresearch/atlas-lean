# Weakest precondition with cost for data-structure clients

Let $D$ be a deterministic state-transition specification with a charge $c(s, o) \ge 0$ per operation. For an adaptive client $p$ and a postcondition $Q(a, s', t)$ on the client's answer $a$, the final state $s'$ and the total charge $t$, the *weakest precondition* $\mathrm{wp}(p, Q)$ is the set of states $s$ from which every operation issued by $p$ is admissible and $Q$ holds of the outcome. It satisfies $\mathrm{wp}(\mathrm{return}\ a, Q)(s) = Q(a, s, 0)$ and, for a client issuing $o$ first and continuing with $k$,

$$
\mathrm{wp}(o \mathbin{;} k, Q)(s) \iff \mathrm{valid}(s, o) \wedge \mathrm{wp}\left(k(a), Q'\right)(s'), \quad (s', a) = f(s, o),
$$

where $Q'(b, s'', t) = Q(b, s'', t + c(s, o))$. A *cost Hoare triple* $\{P\}\, p\, \{Q\}$ with an initial-state-dependent budget asserts that every admissible run from a state satisfying $P$ ends in $Q$ with total charge within the budget.

## Depends on

- [State-transition specification of a data structure](state-transition-specification.md)
- [Weakest precondition for total correctness](../../program-logics-and-verification/hoare-logic/wp.md)
- [Hoare triples](../../program-logics-and-verification/hoare-logic/triple.md)

## Sources

- T. H. Cormen, C. E. Leiserson, R. L. Rivest and C. Stein, "Introduction to Algorithms", 3rd edition, MIT Press, 2009.
- E. W. Dijkstra, "Guarded Commands, Nondeterminacy and Formal Derivation of Programs", Communications of the ACM 18(8), pp. 453-457, 1975.
- H. R. Nielson, "A Hoare-Like Proof System for Analysing the Computation Time of Programs", Science of Computer Programming 9(2), pp. 107-136, 1987.
