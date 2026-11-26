# Line-parity codes and universal recovery menus

Let $K$ be a finite field and $\ell \ge 1$. For $u, v \in K^\ell$ with $v \ne 0$, the punctured line through $u$ in direction $v$ is the set of $|K| - 1$ points $u + c v$, $c \in K^\times$; it omits $u$. A line-parity code on $K^\ell$ consists of an information set $I \subseteq K^\ell$ and, for every assignment of data on $I$, a codeword $w : K^\ell \to K$ extending it such that for every point $u$ and every nonzero direction $v$,

$$\sum_{c \in K^\times} w(u + c v) = w(u).$$

Thus any value can be recovered from many disjoint sets of other points. Given occupied points and $k$ requested targets $t_1, \dots, t_k$ with directions $v_1, \dots, v_k$, request $i$ is clean if its punctured line avoids the occupied points and the lines of all other requests. A list (menu) of $r$ tuples of nonzero directions is universal for $g$ occupied lines if, for every set of at most $g$ occupied lines and every target tuple (repetitions and occupied targets allowed), some entry leaves at least half of the requests clean.

## Depends on

- [Linear code](../linear-codes/linear-code.md)

## Sources

- S. Schlesinger, "Boolean circuit mass production", 2026.
- I. S. Reed, "A Class of Multiple-Error-Correcting Codes and the Decoding Scheme", Transactions of the IRE Professional Group on Information Theory, 1954.
- D. E. Muller, "Application of Boolean Algebra to Switching Circuit Design and to Error Detection", Transactions of the IRE Professional Group on Electronic Computers, 1954.
