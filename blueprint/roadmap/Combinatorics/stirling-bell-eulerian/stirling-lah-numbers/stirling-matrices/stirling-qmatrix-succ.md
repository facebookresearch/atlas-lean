# Recurrence for $Q^{(N)}(n)$ in $N$

For natural numbers $n$ and $N$ with $N \ge 1$, let
$V(n)$ be the $n \times n$ upper bidiagonal matrix with $V(n)_{i,i} = i$, $V(n)_{i,i+1} = 1$
and all other entries $0$, let $I_n$ be the $n \times n$ identity matrix, and for $M \ge 1$ let
$Q^{[M]}(n)$ be the $n \times n$ matrix with
$Q^{[M]}(n)_{i,j} = (-1)^{j-i+1} i^{M-1} / ((i-1)!\,(j-i-1)!)$ for $j \ge i + 1$ and $0$
otherwise. Then, as matrices over $\mathbb{Q}$,

$$Q^{[N+1]}(n) = Q^{[N]}(n)\,(V(n) - I_n).$$

## Sources

- M. Bahrami-Taghanaki, A. R. Moghaddamfar, Navid Salehy and Nima Salehy, *On Matrices Whose Entries Are Stirling Numbers of the Second Kind (I)*, INTEGERS 25 (2025), Article A27, Lemma 2 (`integers-2025-A27-lem-2`).
