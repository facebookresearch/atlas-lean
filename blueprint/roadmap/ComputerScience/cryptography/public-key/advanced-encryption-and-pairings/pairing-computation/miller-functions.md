# Miller functions

For a point $P$ on an elliptic curve and an integer $n$, the Miller function $f_{n,P}$ is the function with divisor $n(P)-([n]P)-(n-1)(O)$ whose expansion at $O$ in the uniformizer $x/y$ has leading coefficient $1$; Tate and Weil pairings are computed from values of such functions at divisors.

Let $E$ be an elliptic curve over a field $k$ given by a Weierstrass equation, with point at infinity $O$, and fix the uniformizer $t=x/y$ at $O$. A nonzero function $g\in k(E)^\times$ is *normalized* if the leading coefficient of its Laurent expansion in $t$ at $O$ is $1$. For $P\in E(k)$ and $n\in\mathbb{Z}$, the *Miller function* $f_{n,P}$ is the normalized function with

$$
\operatorname{div}(f_{n,P})=n(P)-([n]P)-(n-1)(O).
$$

The divisor has degree $0$ and its points sum to $O$ in $E$, so such a function exists, and normalization makes it unique. In particular $f_{0,P}=f_{1,P}=1$, $f_{n,O}=1$ for all $n$, and if $[n]P=O$ then $\operatorname{div}(f_{n,P})=n(P)-n(O)$.

**Line functions.** For $A,B\in E(k)$ let $G_{A,B}$ be the normalized function with $\operatorname{div}(G_{A,B})=(A)+(B)-(A+B)-(O)$. Explicitly: $G_{A,B}=1$ if $A=O$ or $B=O$; if $A,B$ are affine with $A+B=O$ (including $A=B$ of order $2$), then $G_{A,B}=x-x(A)$; otherwise $G_{A,B}=l/v$, where $l=y-\lambda x-\nu$ is the line through $A$ and $B$ (the tangent at $A$ if $A=B$) and $v=x-x(A+B)$. With these, $f_{n+1,P}=f_{n,P}\,G_{P,[n]P}$ and $f_{-n,P}=\bigl(f_{n,P}\,G_{[n]P,-[n]P}\bigr)^{-1}$ for $n\ge0$.

## Depends on

- [Divisors on a curve](../../../../../AlgebraicGeometry/algebraic-curves/divisors-on-curves/divisors-on-a-curve/curve-divisor.md)
- [Order of an element at a place](../../../../../AlgebraicGeometry/algebraic-curves/divisors-on-curves/place/ord.md)

## Proof depends on

None.

## Expansion

The divisor of $l$ is $(A)+(B)+(-(A+B))-3(O)$ and that of $x-x(C)$ is $(C)+(-C)-2(O)$, so $l/v$ has the stated divisor; $x$ and $y$ have expansions $t^{-2}(1+\cdots)$ and $t^{-3}(1+\cdots)$ at $O$, so $l$, $v$ and $l/v$ are normalized. The recursions follow by comparing divisors of normalized functions (Sutherland, Lemma 23.24(i)); they also construct $f_{n,P}$ explicitly over $k$ without appeal to the Abel–Jacobi criterion. Prerequisite still to add: the principal divisor of a nonzero function on $E$, and the Abel–Jacobi criterion over the algebraic closure that a degree-zero divisor $\sum n_X(X)$ is principal if and only if $\sum[n_X]X=O$, with descent of a Galois-fixed principal divisor to the divisor of a function over $k$.

## Sources

- S. D. Galbraith, *Mathematics of Public Key Cryptography*, Cambridge University Press, 2012, doi:10.1017/CBO9781139012843; numbering from the author's extended and corrected version 2.0 chapters, <https://www.math.auckland.ac.nz/~sgal018/crypto-book/crypto-book.html>, Definition 26.3.4.
- A. V. Sutherland, *18.783 Elliptic Curves*, Lecture 23 notes, MIT, Fall 2023, <https://math.mit.edu/classes/18.783/2023/LectureNotes23.pdf>, Definition 23.16, Theorem 23.17, the normalization before Definition 23.19, Definition 23.23 and Lemma 23.24(i).
- V. S. Miller, "Short programs for functions on curves", unpublished manuscript, IBM Thomas J. Watson Research Center, 1986, <https://crypto.stanford.edu/miller/miller.pdf>.
- V. S. Miller, "The Weil pairing, and its efficient calculation", *Journal of Cryptology* 17(4):235–261, 2004, doi:10.1007/s00145-004-0315-8, Section 4.1: Definitions 4–6, Proposition 2 and Lemmas 1–2 (normalized line functions and the functions $f_{n,P}$ for all integers $n$, normalized with respect to the uniformizer fixed there).
