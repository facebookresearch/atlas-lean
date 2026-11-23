# Trudi's formula as a generating function

Let $K$ be a field and $a_0, a_1, a_2, \dots$
a sequence in $K$ with $a_0 \ne 0$. For $n \ge 1$ let $A_n$ be the $n \times n$
Toeplitz–Hessenberg matrix whose $(i, j)$ entry is $a_{i-j+1}$ if $j \le i + 1$ and $0$
otherwise. In the ring of formal power series over $K$, let $f(x) = \sum_{n \ge 1} \det(A_n) x^n$,
$g(x) = \sum_{i \ge 1} a_i x^i$ and $h(x) = a_0^{-1} g(-a_0 x)$. Then $f(x)(1 + h(x)) = -h(x)$,
that is, $f(x) = -h(x)/(1 + h(x))$.

## Sources

- Taras Goy and Mark Shattuck, *Determinantal Representations of Some Classical Recurrent Sequences*, INTEGERS 25 (2025), Article A97, Lemma 2.
