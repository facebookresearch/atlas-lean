# Dimension of multiple zeta values in low weight

Let $F$ be a finite field with $q$
elements, $K = F(t)$, and $w$ a positive integer with $w \le 2q - 2$. Let $\mathcal{T}_w$ be the
set of multiple zeta values $\zeta_A(s_1, \dots, s_r)$ over $F$ with $r \ge 1$, positive integers
$s_1, \dots, s_r$ with sum $w$, $s_i \le q$ for $1 \le i \le r - 1$, and $s_r < q$, and let
$\mathcal{Z}_w$ be the $K$-vector space spanned by all multiple zeta values of weight $w$. Then
the elements of $\mathcal{T}_w$ are linearly independent over $K$, and
$\dim_K \mathcal{Z}_w = d(w)$, where $d$ is the dimension sequence for multiple zeta values.

Together with Brown's theorem in positive characteristic (Theorem A of the source), which says
that $\mathcal{T}_w$ spans $\mathcal{Z}_w$, this means that $\mathcal{T}_w$ is a $K$-basis of
$\mathcal{Z}_w$.

## Sources

- T. N. Dac, `On Zagier-Hoffman's conjectures in positive characteristic`, Annals of Math, 194 (1) 2021. Statement taken from https://github.com/ImperialCollegeLondon/AnnalsChallenge (v1.0.0, e32eb14), AnnalsChallenge/AnnalsOfMathematics/2021-194-1-ZagierHoffmanPositiveChar.lean Via leanprover/lean-eval@38361be, problem `annals_zagier_hoffman_positive_char`.
