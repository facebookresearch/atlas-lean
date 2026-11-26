# Refinement of a data-structure specification by an abstraction function

Let $D$ and $E$ be state-transition specifications. A *refinement* of $D$ by $E$ consists of an invariant $I$ on $E$-states, an abstraction function $\alpha : \mathsf{State}_E \to \mathsf{State}_D$, and for each $D$-operation $o$ an admissible $E$-client $M_o$ (the *method* of $o$) such that, whenever $I(e)$ holds and $o$ is admissible at $\alpha(e)$, every run of $M_o$ from $e$ ends in a state $e'$ with result $a$ such that $I(e')$ and $(\alpha(e'), a) \in \mathsf{step}_D(\alpha(e), o)$.

The refinement is *amortized* with potential $\Phi : \mathsf{State}_E \to \mathbb{R}_{\ge 0}$ and upper charges $c_D(s, o)$ if every method run with lower cost $c_E$ satisfies the physicist's inequality

$$
c_E + \Phi(e') \le c_D(\alpha(e), o) + \Phi(e).
$$

## Depends on

- [State-transition specification of a data structure](state-transition-specification.md)
- [Amortized cost of an operation](../amortized-analysis/amortized-cost.md)

## Sources

- T. H. Cormen, C. E. Leiserson, R. L. Rivest and C. Stein, "Introduction to Algorithms", 3rd edition, MIT Press, 2009.
- D. D. Sleator and R. E. Tarjan, "Self-Adjusting Binary Search Trees", Journal of the ACM 32(3), 1985.
