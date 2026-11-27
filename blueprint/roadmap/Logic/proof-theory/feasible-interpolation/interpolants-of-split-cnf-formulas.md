# Interpolants of split CNF formulas

Let $A(x, y)$ and $B(x, z)$ be CNF formulas whose variables are split into shared variables $x = (x_1,\dots,x_n)$ and private variables $y$ (of $A$) and $z$ (of $B$). A Boolean function $f : \{0,1\}^n \to \{0,1\}$ is an *interpolant* of the pair if for every $a \in \{0,1\}^n$: whenever $A(a, y)$ is satisfiable then $f(a) = 1$, and whenever $B(a, z)$ is satisfiable then $f(a) = 0$. An interpolant exists if and only if $A \wedge B$ is unsatisfiable. It is *monotone* if $f$ is monotone in $x$.

## Depends on

- [CNF formula](../../propositional-logic/conjunctive-normal-form/cnf.md)
- [Craig interpolation, semantic form](../../propositional-logic/craig-interpolation/exists-interpolant.md)

## Sources

- J. Krajíček, "Interpolation Theorems, Lower Bounds for Proof Systems, and Independence Results for Bounded Arithmetic", The Journal of Symbolic Logic 62(2), 457–486, 1997: Section 3 (interpolants of implications).
- P. Pudlák, "Lower Bounds for Resolution and Cutting Plane Proofs and Monotone Computations", The Journal of Symbolic Logic 62(3), 981–998, 1997.
