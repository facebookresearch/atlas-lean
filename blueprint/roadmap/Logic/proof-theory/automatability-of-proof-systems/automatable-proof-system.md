# Automatable proof systems

Let $P$ be a Cook-Reckhow propositional proof system for refuting unsatisfiable CNF formulas, and for an unsatisfiable CNF $F$ let $s_P(F)$ be the size of a shortest $P$-refutation of $F$. $P$ is **automatable in time $t$** if there is an algorithm that, on every unsatisfiable $F$, outputs a $P$-refutation of $F$ within time $t\bigl(|F| + s_P(F)\bigr)$. It is **automatable** if this holds with $t$ a polynomial, **quasi-polynomially automatable** if $t(m) = m^{\operatorname{polylog}(m)}$, and **weakly automatable** if some proof system $Q$ (possibly different from $P$) has refutations of $F$ that can be found in time polynomial in $|F| + s_P(F)$.

## Depends on

- [Cook–Reckhow propositional proof systems](../../propositional-logic/propositional-proof-complexity/cookreckhow-propositional-proof-systems.md)

## Sources

- M. L. Bonet, T. Pitassi, R. Raz, "On interpolation and automatization for Frege systems", SIAM Journal on Computing 29 (2000) 1939-1967.
- M. Alekhnovich, A. A. Razborov, "Resolution is not automatizable unless W[P] is tractable", SIAM Journal on Computing 38 (2008) 1347-1363; FOCS (2001).
- A. Atserias, M. Müller, "Automating resolution is NP-hard", FOCS (2019); Journal of the ACM 67 (2020), arXiv:1904.02991.
