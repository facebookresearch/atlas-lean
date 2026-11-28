# Image length of a prefix under iterated substitution

Let $\tau_k$ be the substitution
of finite words over $\mathbb{N}$ that replaces the letter $k$ by $k\,1$ and every other letter $i$
by $i + 1$, let $\tau_k^j$ be its $j$-fold iterate, and let $x_k$ be its fixed point starting
with $k$. For natural numbers $k$, $j$ and $n$, `imageLength k j n` is
$|\tau_k^j(x_k[0] \cdots x_k[n-1])|$, the length of the word obtained by applying $\tau_k$ $j$
times to the prefix of $x_k$ of length $n$.
