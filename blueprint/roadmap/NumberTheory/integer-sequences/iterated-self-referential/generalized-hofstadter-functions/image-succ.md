# Image length of a prefix one letter longer

Let $\tau_k$ be the substitution sending the
letter $k$ to $k\,1$ and every other letter $i$ to $i + 1$, let $\tau_k^j$ be its $j$-fold
iterate, let $x_k$ be its fixed point starting with $k$, and let
$L_k^{(j)}(n) = |\tau_k^j(x_k[0] \cdots x_k[n-1])|$. For all natural numbers $k$, $j$ and $n$,
$L_k^{(j)}(n + 1) = L_k^{(j)}(n) + |\tau_k^j(x_k[n])|$.
