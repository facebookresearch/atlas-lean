# Truth-table CNF of a Boolean function

Every Boolean function $f : \{0,1\}^\ell \to \{0,1\}$ is computed by the CNF formula $\bigwedge_{v : f(v) = 0} C_v$ over the variables $x_1,\dots,x_\ell$, where $C_v$ is the clause of the $\ell$ literals falsified by $v$ (so $C_v$ is false exactly at $v$). This formula has at most $2^\ell$ clauses of width $\ell$ and uses at most $\ell \cdot 2^\ell$ binary $\wedge$ and $\vee$ connectives.

## Proof sketch

$C_v$ excludes exactly the point $v$, so the conjunction excludes exactly the zeros of $f$.

## Depends on

- [CNF formula](../../conjunctive-normal-form/cnf.md)

## Proof depends on

- [Functional completeness](../../functional-completeness/exists-eval-bool-eq.md)

## Sources

- S. Arora and B. Barak, Computational Complexity: A Modern Approach, Cambridge University Press, 2009.
