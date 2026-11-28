# Addition formula for Miller functions

Miller functions satisfy $f_{m+n,P}=f_{m,P}\,f_{n,P}\,G_{[m]P,[n]P}$ and $f_{mn,P}=f_{m,P}^{\,n}\,f_{n,[m]P}$, where $G_{A,B}$ is the normalized line function with divisor $(A)+(B)-(A+B)-(O)$; this lets $f_{n,P}$ be built by double-and-add.

**Theorem.** Let $E$ be an elliptic curve over a field $k$ and $P\in E(k)$, with Miller functions $f_{n,P}$ and line functions $G_{A,B}$ as defined on the Miller-function page. For all integers $m,n$:

$$
f_{m+n,P}=f_{m,P}\,f_{n,P}\,G_{[m]P,[n]P},\qquad f_{mn,P}=f_{m,P}^{\,n}\,f_{n,[m]P}=f_{n,P}^{\,m}\,f_{m,[n]P} .
$$

## Depends on

- [Miller functions](miller-functions.md)

## Proof depends on

None.

## Expansion

Both sides of each identity are normalized functions with the same divisor: for the first, $\operatorname{div}(f_{m,P}f_{n,P}G_{[m]P,[n]P})=(m+n)(P)-(m+n-1)(O)-([m+n]P)$ after cancelling $([m]P)+([n]P)$; for the second, $n\bigl(m(P)-(m-1)(O)-([m]P)\bigr)+n([m]P)-(n-1)(O)-([mn]P)=mn(P)-(mn-1)(O)-([mn]P)$. Two normalized functions with equal divisors are equal, and products of normalized functions are normalized. The cases where $[m]P$ or $[n]P$ is $O$ use $G=1$.

## Sources

- A. V. Sutherland, *18.783 Elliptic Curves*, Lecture 23 notes, MIT, Fall 2023, <https://math.mit.edu/classes/18.783/2023/LectureNotes23.pdf>, Lemma 23.24(ii)–(iii).
- S. D. Galbraith, *Mathematics of Public Key Cryptography*, Cambridge University Press, 2012, doi:10.1017/CBO9781139012843; numbering from the author's extended and corrected version 2.0 chapters, <https://www.math.auckland.ac.nz/~sgal018/crypto-book/crypto-book.html>, Exercise 26.3.5.
