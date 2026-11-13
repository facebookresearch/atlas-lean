# Generalized Lucasnomial Fuss–Catalan numbers are integers (Ballot)

Let $P$ and $Q$ be
nonzero integers with $\gcd(P, Q) = 1$, and let $U : \mathbb{N} \to \mathbb{Z}$ satisfy $U_0 = 0$,
$U_1 = 1$, $U_{m+2} = P U_{m+1} - Q U_m$ for every natural number $m$, and $U_m \ne 0$ for every
$m \ge 1$. Then for all natural numbers $r \ge 1$, $a \ge 2$ and $n \ge 1$, the rational number

$$\frac{U_r}{U_{(a-1)n+r}} \cdot \frac{\prod_{j=0}^{n-1} U_{an+r-1-j}}{\prod_{j=0}^{n-1} U_{j+1}}$$

is an integer; its second factor is the Lucasnomial coefficient $\binom{an+r-1}{n}_U$.

## Sources

- Christian Ballot, "Lucasnomial Fuss-Catalan Numbers and Related Divisibility Questions," Journal of Integer Sequences 21 (2018), Article 18.6.5, Theorem `thm:2`, lines 553–558, <https://cs.uwaterloo.ca/journals/JIS/VOL21/Ballot/ballot30.tex>. Fundamental Lucas sequences, nondegeneracy, and regularity at lines 185–207; Lucasnomial coefficients at lines 215–221. It follows from `generalized_lucasnomial_fuss_catalan_integral_general`; the hypotheses `hP` and `hQ` are unused and keep the source's shape.
