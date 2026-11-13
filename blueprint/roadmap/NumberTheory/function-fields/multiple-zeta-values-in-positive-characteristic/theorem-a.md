# Brown's theorem in positive characteristic

Let $F$ be a finite field with $q$ elements,
$K = F(t)$, and $w$ a positive integer. Let $\mathcal{Z}_w$ be the $K$-vector space spanned by
the multiple zeta values over $F$ of weight $w$, and let $\mathcal{T}_w$ be the set of multiple
zeta values $\zeta_A(s_1, \dots, s_r)$ with $r \ge 1$, positive integers $s_1, \dots, s_r$ with
sum $w$, $s_i \le q$ for $1 \le i \le r - 1$, and $s_r < q$. Then $\mathcal{Z}_w$ is the
$K$-linear span of $\mathcal{T}_w$, so every multiple zeta value of weight $w$ is a $K$-linear
combination of elements of $\mathcal{T}_w$, and $\dim_K \mathcal{Z}_w \le d(w)$, where $d$ is
the dimension sequence for multiple zeta values.

## Sources

- T. N. Dac, `On Zagier-Hoffman's conjectures in positive characteristic`, Annals of Math, 194 (1) 2021. Statement taken from https://github.com/ImperialCollegeLondon/AnnalsChallenge. Problem `annals_zagier_hoffman_positive_char` of the lean-eval benchmark.
