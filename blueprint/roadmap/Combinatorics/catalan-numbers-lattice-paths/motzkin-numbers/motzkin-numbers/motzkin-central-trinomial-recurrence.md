# Recurrence linking central trinomial coefficients and Motzkin numbers

For $n \in \mathbb{N}$
let $T_n$ be the central trinomial coefficient, the coefficient of $X^n$ in $(1 + X + X^2)^n$.
Let $M : \mathbb{N} \to \mathbb{N}$ be any function with
$M_n = \sum_{k=0}^{\lfloor n/2 \rfloor} \binom{n}{2k} C_k$ for every $n$, where $C_k$ is the
$k$-th Catalan number (these sums are the Motzkin numbers). Then for every $n \ge 1$,
$T_{n+1} = T_n + 2n \, M_{n-1}$.

The source attributes the recurrence to Barcucci, Pinzani, and Sprugnoli, "The Motzkin family",
and proves it with hybrid-polynomial operator calculus; the proof here instead uses the binomial
sum for $T_n$ and an elementary termwise binomial identity.

## Sources

- P. Blasiak, G. Dattoli, A. Horzela, K. A. Penson, and K. Zhukovsky, "Motzkin Numbers, Central Trinomial Coefficients and Hybrid Polynomials," Journal of Integer Sequences 11 (2008), Article 08.1.1, Theorem (equation eq34), lines 459–464, https://cs.uwaterloo.ca/journals/JIS/VOL11/Penson/penson131.tex
