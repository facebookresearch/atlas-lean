# Integer points on elliptic curves can be listed by an algorithm

There is a computable function $f$ sending each pair $(A, B)$ of integers to a finite list of pairs of integers such that, whenever $4A^3 + 27B^2 \ne 0$, a pair $(x, y)$ of integers lies on the list exactly when $y^2 = x^3 + Ax + B$: an algorithm lists all integer points of every elliptic curve $y^2 = x^3 + Ax + B$ with integer coefficients.

This resolves [Hall–Shlapentokh question on enumerating integer points on elliptic curves](elliptic-curve-integer-points-enumerable.md), the statement recorded as a proposition, in the affirmative; the resolution is due to Baker and Coates (1970), cited under Sources.

## Sources

- AimPL: Definability and decidability problems in number theory, Section 3, Problem 3.1 (C. Hall, A. Shlapentokh).
- A. Baker and J. Coates, Integer points on curves of genus 1, Math. Proc. Cambridge Philos. Soc. 67 (1970), 595–602, https://doi.org/10.1017/S0305004100045904.
