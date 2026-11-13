# Santos's coefficients

For natural numbers $i$, $p$, $q$ and a complex number $z$,
Santos's coefficient $\beta_i(p, q, z)$ is the complex number

$$
\beta_i(p, q, z) = 2^{-2q} \sum_{b=\max(0, i-p)}^{q} 2^b \binom{2q-b}{q}
\sum_{a=0}^{b} \binom{p+b-q-z}{a} \binom{q+z}{b-a} \binom{a-q}{p+b-i},
$$

where $\binom{w}{n} = w(w-1)\cdots(w-n+1)/n!$ for complex $w$ and natural $n$.

## Sources

- Eder G. Santos, *Counting Nonattacking Chess Piece Placements: Bishops and Anassas*, Journal of Integer Sequences 28 (2025), Article 25.8.6, Lemma 2.7, equation (9).
