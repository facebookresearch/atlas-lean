# Generalized Catalan identity for Horadam sequences

Let $R$ be a commutative ring, let
$c_1, c_2 \in R$, and let $W, Y, U : \mathbb{N} \to R$ be sequences that each satisfy
$x_{n+2} = c_1 x_{n+1} + c_2 x_n$ for every $n \in \mathbb{N}$, with $U_0 = 0$ and $U_1 = 1$.
Then for all $s, i, j \in \mathbb{N}$,

$$W_{s+i}\,Y_{s+j} - W_s\,Y_{s+i+j} = (-c_2)^s\,(W_1 Y_j - W_0 Y_{j+1})\,U_i.$$

The source states the identity over the integers, with integer coefficients, all integer
indices and $c_2 \ne 0$. This version restricts the indices to natural numbers and allows
coefficients in any commutative ring, so no invertibility of $c_2$ is needed; the bi-infinite
version is not claimed.

## Sources

- Aram Tangboonduangjit and Thotsaporn Thanatipanonda, "Determinants Containing Powers of Generalized Fibonacci Numbers," Journal of Integer Sequences 19 (2016), Article 16.7.1, Proposition "Generalized Catalan Identity," lines 111–126 of `https://cs.uwaterloo.ca/journals/JIS/VOL19/Tangboonduangjit/aram5.tex`. Proves `Wanted` entry `horadam_generalized_catalan_identity`.
