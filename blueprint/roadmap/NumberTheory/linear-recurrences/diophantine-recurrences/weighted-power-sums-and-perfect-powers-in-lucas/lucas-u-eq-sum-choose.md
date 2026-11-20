# Binomial-sum formula for the Lucas sequence $U$

Let $x$ and $y \neq 0$ be integers and
let $(U_n)$ be the Lucas sequence with parameters $(x, y)$, given by $U_0 = 0$, $U_1 = 1$ and
$U_{n+2} = x U_{n+1} - y U_n$. Then for every $r \geq 1$,

$$
U_r = \sum_{i=0}^{\lfloor (r-1)/2 \rfloor} (-y)^i \binom{r-i-1}{i} x^{r-2i-1}.
$$

## Sources

- Benjamin Earp-Lynch, Simon Earp-Lynch, Omar Kihel and Puntani Pongsumpun, *Extension of the Equation ∑ j F_j^p = F_n^q to a Family of Lucas Sequences*, The Fibonacci Quarterly 62 (2024), no. 3, Lemma 2.1 (vii).
