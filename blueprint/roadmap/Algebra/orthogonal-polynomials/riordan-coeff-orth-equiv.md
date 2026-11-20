# Meixner-type characterization of Riordan orthogonal polynomial arrays

Let $d$ and $h$ be
real formal power series with $[x^0]\,h = 0$, $[x^1]\,h \ne 0$ and $[x^0]\,d \ne 0$, where
$[x^n]$ denotes the coefficient of $x^n$, and let $L$ be the Riordan array of $(d, h)$, with
entries $L_{n,k} = [x^n]\,(d h^k)$ for $n, k \ge 0$. Call $L$ a monic orthogonal coefficient
array if there are real polynomials $P_0, P_1, \dots$ with $[x^k]\,P_n = L_{n,k}$ for all
$n, k$, each $P_n$ monic, and the family $(P_n)$ formally orthogonal. Each of the following
three conditions is equivalent to $L$ being a monic orthogonal coefficient array.

1. Meixner form: there are real numbers $\lambda, \mu, r, s$ with $s \ne 0$ and $s + \mu \ne 0$
   such that $d\,(1 + r x + s x^2) = 1 - \lambda x - \mu x^2$ and $h\,(1 + r x + s x^2) = x$.
2. Stieltjes form of the inverse: $L_{0,0} = 1$, and there are an array $(L'_{n,k})$ and real
   numbers $r_1, s_1, r, s$ with $s_1 \ne 0$ and $s \ne 0$ such that $L_{n,k} = L'_{n,k} = 0$
   whenever $k > n$; $\sum_{j=0}^{n} L_{n,j} L'_{j,k}$ and $\sum_{j=0}^{n} L'_{n,j} L_{j,k}$
   both equal $1$ if $n = k$ and $0$ otherwise; and
   $L'_{n+1,k} = \sum_{j=0}^{n+1} L'_{n,j} S_{j,k}$ for all $n, k$, where $S$ is the
   Stieltjes matrix with parameters $r_1, s_1, r, s$: its superdiagonal entries are $1$, its
   diagonal is $r_1, r, r, \dots$, its subdiagonal is $s_1, s, s, \dots$, and all other
   entries are $0$.
3. Coefficient recurrence: there are real numbers $\lambda, \mu, r, s$ with $s \ne 0$ and
   $s + \mu \ne 0$ such that for all $N, K \ge 0$,
   $L_{N,K} + r L_{N-1,K} - L_{N-1,K-1} + s L_{N-2,K} = c_{N,K}$, where any entry of $L$
   with a negative index is read as $0$, $c_{0,0} = 1$, $c_{1,0} = -\lambda$,
   $c_{2,0} = -\mu$, and $c_{N,K} = 0$ otherwise.

Proof: The coefficient recurrence is the common hub. The Meixner equivalence follows from
Barry-Hennessy, the orthogonality equivalence from Favard's theorem as in Chihara, and the
inverse-array equivalence from the Stieltjes production construction of the inverse array.

## Sources

- Paul Barry and Aoife Hennessy, "Meixner-Type Results for Riordan Arrays and Associated Integer Sequences," Journal of Integer Sequences 13 (2010), Article 10.9.4, Proposition (referee's summary of the main results), lines 733–752, https://cs.uwaterloo.ca/journals/JIS/VOL13/Barry5/barry96s.tex
