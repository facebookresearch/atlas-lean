# Couveignes: number fields have small models

There is a positive integer $Q$ such that for
every natural number $n \ge Q$ and every number field $K$ of degree $n$ over $\mathbb{Q}$, with
discriminant $d_K$ and root discriminant $\delta_K = |d_K|^{1/n}$, there are natural numbers $r$
and $d$ with $r \le Q \log n$, $d \le Q \log n$ and $\binom{d + r}{r} \le Q n \log n$, and
polynomials $E_1, \dots, E_r \in \mathbb{Z}[x_1, \dots, x_r]$ of total degree at most $d$, all of
whose coefficients have absolute value at most $(n \delta_K)^{Q \log n}$, with the following
property. Let $X$ be the open subscheme of
$\operatorname{Spec} \mathbb{Q}[x_1, \dots, x_r]/(E_1, \dots, E_r)$ where
$\det(\partial E_i / \partial x_j) \ne 0$. Then $X$ has an irreducible component $Z$ which, with
its subscheme structure as the scheme-theoretic closure of the open set of points of $X$ lying on
no other irreducible component, is isomorphic to $\operatorname{Spec} K$.

## Sources

- J.-M. Couveignes, `Enumerating number fields`, Annals of Math, 192 (2) 2020. Statement taken from https://github.com/ImperialCollegeLondon/AnnalsChallenge (v1.0.0, e32eb14), AnnalsChallenge/AnnalsOfMathematics/2020-192-2-EnumeratingNumberFields.lean Via leanprover/lean-eval@38361be, problem `annals_enumerating_number_fields`.
