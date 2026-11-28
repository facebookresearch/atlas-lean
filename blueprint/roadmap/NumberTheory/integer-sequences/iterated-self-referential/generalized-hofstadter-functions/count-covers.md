# An image length at the count bounds the position

Let $\tau_k$ be the substitution
sending the letter $k$ to $k\,1$ and every other letter $i$ to $i + 1$, let $\tau_k^j$ be its
$j$-fold iterate, let $x_k$ be its fixed point starting with $k$, let
$L_k^{(j)}(n) = |\tau_k^j(x_k[0] \cdots x_k[n-1])|$, and for a decidable predicate $P$ on letters
let $C_k^{(P)}(n) = \#\{0 \le i < n : P(x_k[i])\}$. If $C_k^{(P)}(L_k^{(j)}(c) + 1) = c + 1$ for
every natural number $c$, then $n \le L_k^{(j)}(C_k^{(P)}(n))$ for every natural number $n$.
