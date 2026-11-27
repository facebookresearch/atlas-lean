# Exactly-one (one-hot) constraint in CNF

For a list of variables $v_1,\dots,v_k$, the CNF formula $\mathrm{EO}(v_1,\dots,v_k)$ consists of the *at-least-one* clause $v_1 \vee \dots \vee v_k$ and the *at-most-one* clauses $\neg v_i \vee \neg v_j$ for all $i \ne j$. An assignment satisfies it if and only if exactly one of $v_1,\dots,v_k$ is true. It has $1 + \binom{k}{2}$ clauses (or $1 + k(k-1)$ when both orders of each pair are emitted), and it is the standard one-hot encoding of a finite-valued variable by Boolean variables.

## Depends on

- [CNF formula](../../conjunctive-normal-form/cnf.md)

## Sources

- T. Walsh, "SAT v CSP", Principles and Practice of Constraint Programming — CP 2000, LNCS 1894, 441–456, 2000.
