# Miller's algorithm

For $P$ with $[n]P=O$, Miller's algorithm evaluates $f_{n,P}$ at a divisor $D$ by a square-and-multiply loop over the binary digits of $n\ge1$, multiplying in one line-function value per doubling or addition step.

Let $E$ be an elliptic curve over a field $k$, $n=(1\,n_{m-1}\dots n_1n_0)_2\ge1$ with $m=\lfloor\log_2n\rfloor$, $P\in E(k)$ with $[n]P=O$, and $D$ a divisor on $E$ whose points are $k$-rational. With $G_{A,B}$ the line functions of the Miller-function page, the algorithm sets $f\leftarrow1$, $T\leftarrow P$ and, for $i=m-1,\dots,0$:

1. $f\leftarrow f^2\,G_{T,T}(D)$ and $T\leftarrow[2]T$;
2. if $n_i=1$: $f\leftarrow f\,G_{T,P}(D)$ and $T\leftarrow T+P$.

It returns $f$. If every line function $G_{T,T}$ and $G_{T,P}$ evaluated has neither a zero nor a pole at the points of $D$, the output equals $f_{n,P}(D)$. The loop has $\lfloor\log_2n\rfloor$ iterations, each consisting of operations in $k$.

## Depends on

- [Miller functions](miller-functions.md)
- [Evaluation of a divisor against a function](../../../../../AlgebraicGeometry/algebraic-curves/divisors-on-curves/evaluation-of-curve-divisors/eval.md)

## Proof depends on

- [Addition formula for Miller functions](miller-function-addition-formula.md)

## Expansion

Invariant: after processing the digits $n_{m-1},\dots,n_i$, with $j=(1n_{m-1}\dots n_i)_2$, one has $T=[j]P$ and $f=f_{j,P}(D)$. Doubling uses $f_{2j,P}=f_{j,P}^2G_{[j]P,[j]P}$ and the addition step uses $f_{j+1,P}=f_{j,P}G_{[j]P,P}$, both instances of the addition formula, evaluated at $D$ multiplicatively; the hypothesis on zeros and poles makes each evaluation a nonzero field element. Avoiding only the support of $f_{n,P}$ is not enough, because intermediate line functions can vanish or have poles at points of $D$. When $T=O$ or $P=O$ the line function is $1$. Cost: each iteration evaluates one or two line functions at the points of $D$ and raises the values to the coefficients of $D$, so when $D$ has a bounded number of points with bounded coefficients the whole computation uses $O(\log n)$ operations in $k$; this count is derived from the loop, not taken from the cited statement. The same recurrence, without the hypothesis $[n]P=O$, evaluates $f_{n,P}$ at a single point: for every $n\ge1$ and $P,Q\in E(k)$, $f_{n,P}(Q)$ can be evaluated with $O(\log n)$ field operations in $k$ (Sutherland, Corollary 23.25), again when every intermediate line value at $Q$ is defined and nonzero. The values $G(X)$ are values of rational functions at regular points; substituting $X$ into an uncancelled quotient $l/v$ gives this value only when $v(X)\ne0$, and otherwise needs local cancellation.

## Sources

- S. D. Galbraith, *Mathematics of Public Key Cryptography*, Cambridge University Press, 2012, doi:10.1017/CBO9781139012843; numbering from the author's extended and corrected version 2.0 chapters, <https://www.math.auckland.ac.nz/~sgal018/crypto-book/crypto-book.html>, Algorithm 29 and Exercise 26.3.6.
- A. V. Sutherland, *18.783 Elliptic Curves*, Lecture 23 notes, MIT, Fall 2023, <https://math.mit.edu/classes/18.783/2023/LectureNotes23.pdf>, Lemma 23.24 and Corollary 23.25.
- V. S. Miller, "Short programs for functions on curves", unpublished manuscript, IBM Thomas J. Watson Research Center, 1986, <https://crypto.stanford.edu/miller/miller.pdf>.
- V. S. Miller, "The Weil pairing, and its efficient calculation", *Journal of Cryptology* 17(4):235–261, 2004, doi:10.1007/s00145-004-0315-8, Section 4.1: equations (7)–(9), Proposition 3 and Algorithm 1 (the recurrence and its evaluation at a point along an addition–subtraction chain).
