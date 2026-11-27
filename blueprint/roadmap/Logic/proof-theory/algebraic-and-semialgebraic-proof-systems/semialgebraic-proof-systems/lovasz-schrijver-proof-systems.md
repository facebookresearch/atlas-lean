# Lovász-Schrijver proof systems LS and LS+

Lovász-Schrijver (LS) proofs are dynamic semialgebraic derivations over $\{0,1\}$-valued variables in which an inequality may be multiplied only by a positive scalar or by a variable or its twin; LS+ also admits squares $P^2 \ge 0$. Degree, size and rank are the main measures.

Work over $\mathbb{R}$ with variables $X_1, \dots, X_n$ and twins $\bar{X}_1, \dots, \bar{X}_n$, subject to the axioms

$$
X_i^2 - X_i = 0, \qquad \bar{X}_i^2 - \bar{X}_i = 0, \qquad X_i + \bar{X}_i - 1 = 0 ,
$$

and the semialgebraic axioms $X_i \ge 0$, $\bar{X}_i \ge 0$, $1 - X_i \ge 0$, $1 - \bar{X}_i \ge 0$, $1 \ge 0$. A **semi-algebraic proof** of $Q \ge 0$ from hypotheses $H$ (equations read as two inequalities) is a sequence of inequalities, each a hypothesis, an axiom, or obtained by the rules *addition* ($P \ge 0, Q \ge 0 \vdash P + Q \ge 0$), *multiplication* ($P \ge 0, Q \ge 0 \vdash PQ \ge 0$) and *positivity of squares* ($\vdash P^2 \ge 0$); a **refutation** ends with $-1 \ge 0$.

- An **LS proof** is a semi-algebraic proof in which the polynomial $Q$ in the multiplication rule is a positive scalar or a variable, and the positivity-of-squares rule is not used.
- An **LS+ proof** (positive semidefinite Lovász-Schrijver) also allows positivity of squares.
- $\mathrm{LS}_d$ and $\mathrm{LS}^+_d$ denote the degree-$d$ versions; the original systems of Lovász and Schrijver manipulate quadratic polynomials only and are $\mathrm{LS}_2$ and $\mathrm{LS}^+_2$.

Size is the number of symbols needed to write the polynomials as explicit sums of monomials, degree the maximum total degree in the proof, and **rank** the maximum nesting depth of multiplications by a variable; because of cancellations the degree can be much smaller than the rank.

## Expansion

Sherali-Adams and positive semidefinite Sherali-Adams are the static subsystems of LS and LS+ in which all multiplications precede all additions, and an LS proof of degree $d$ and rank $k$ converts into an SA proof of degree $d + k$ by reordering the rules. Each positive semidefinite SA proof converts into a Sums-of-Squares proof of twice the degree by replacing multiplication by $X$ with multiplication by $X^2$ and subtracting a multiple of $X^2 - X$. Sherali-Adams and Sums-of-Squares of sublinear degree cannot refute all unsatisfiable systems of linear equations over $\mathbb{Z}_2$, whereas bounded-degree LS simulates Gaussian elimination over $\mathbb{Z}_2$ in polynomial size.

## Depends on

None.

## Proof depends on

None.

## Sources

- Albert Atserias, Joanna Ochremiak, "Proof complexity meets algebra", *ACM Transactions on Computational Logic* 20(1), 2019, https://doi.org/10.1145/3265985; numbering of arXiv:1711.07320v2 (Section 2.3, axioms and rules of semi-algebraic proofs and the definitions of LS and LS+).
