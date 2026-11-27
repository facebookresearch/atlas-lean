# Occurrence splitting of a CNF formula

Let $\varphi$ be a CNF formula. Its *occurrence splitting* $\mathrm{Occ}_3(\varphi)$ replaces the variable at each literal occurrence (indexed by its clause and position) by its own fresh copy, keeping the literal's sign, and adds for every original variable $x$ with occurrences $o_1,\dots,o_r$ the implication cycle on the copies $x_{o_1},\dots,x_{o_r}$. Every variable of $\mathrm{Occ}_3(\varphi)$ occurs at most three times (once in an original clause and twice in its cycle).

## Depends on

- [Binary implication cycles and chains](binary-implication-cycles.md)
- [CNF formula](../../conjunctive-normal-form/cnf.md)

## Sources

- C. H. Papadimitriou, Computational Complexity, Addison-Wesley, 1994.
- C. A. Tovey, "A Simplified NP-Complete Satisfiability Problem", Discrete Applied Mathematics 8(1), 85–89, 1984.
