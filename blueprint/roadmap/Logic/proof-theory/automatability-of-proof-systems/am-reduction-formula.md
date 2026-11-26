# The Atserias–Müller reduction from SAT to resolution proof size

There is a polynomial-time map sending a $3$-CNF formula $F$ on $n$ variables to an unsatisfiable CNF formula $\mathrm{Ref}(F)$ of size $\operatorname{poly}(n)$ such that:

- if $F$ is satisfiable, then $\mathrm{Ref}(F)$ has a resolution refutation of size $n^{O(1)}$;
- if $F$ is unsatisfiable, then every resolution refutation of $\mathrm{Ref}(F)$ has size at least $2^{n^{\varepsilon}}$ for an absolute constant $\varepsilon > 0$.

The formula $\mathrm{Ref}(F)$ states that there is a short resolution refutation of $F$, written with its rows relativized in a pigeonhole-like fashion.

## Proof sketch

If $F$ has a satisfying assignment $a$, plugging $a$ into the refutation-encoding variables lets resolution derive a contradiction by following the purported refutation line by line, at polynomial cost. If $F$ is unsatisfiable, a random restriction argument reduces any refutation of $\mathrm{Ref}(F)$ to a refutation of a relativized pigeonhole principle combined with the inherent hardness of refuting the claim that the unsatisfiable $F$ has a short refutation at the relevant size, which costs $2^{n^{\varepsilon}}$ by width lower bounds and Ben-Sasson-Wigderson.

## Depends on

- [Automatable proof systems](automatable-proof-system.md)

## Proof depends on

- [Ben-Sasson–Wigderson for general resolution](../../propositional-logic/resolution-size-and-width/refutation-narrow.md)
- [Haken's lower bound for the pigeonhole principle](../../propositional-logic/propositional-proof-complexity/haken-s-lower-bound-for-the-pigeonhole-principle.md)

## Sources

- A. Atserias, M. Müller, "Automating resolution is NP-hard", FOCS (2019); Journal of the ACM 67 (2020), arXiv:1904.02991.
