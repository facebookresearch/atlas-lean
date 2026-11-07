# Van der Waerden's conjecture (Bhargava)

For every natural number $n \ge 3$ there is a
constant $C$ such that $E_n(H) \le C H^{n-1}$ for all sufficiently large natural numbers $H$,
where $E_n(H)$ is the number of monic polynomials of degree $n$ with integer coefficients, all
non-leading coefficients of absolute value at most $H$, whose Galois group over $\mathbb{Q}$
has order less than $n!$.

The degree restriction is necessary: the statement is false for $n = 2$.

## Sources

- M. Bhargava, `Galois groups of random integer polynomials and van der Waerden's Conjecture`, Annals of Math, 201 (2) 2025. Statement taken from https://github.com/ImperialCollegeLondon/AnnalsChallenge (v1.0.0, e32eb14), AnnalsChallenge/AnnalsOfMathematics/2025-201-2-vanDerWaerdenConjecture.lean Via leanprover/lean-eval@38361be, problem `annals_van_der_waerden_conjecture`.
