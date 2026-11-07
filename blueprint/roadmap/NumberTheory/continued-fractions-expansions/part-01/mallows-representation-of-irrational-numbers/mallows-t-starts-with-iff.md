# Blocks of $T(Q(\mathrm{SB}(\alpha)))$ and of $Q(\mathrm{SB}(\alpha))$

Let $X$ be one of
the letters $O_L, E_R, O_R, E_L$, let $u = u_1 \cdots u_\ell$ be a finite word over $\{L, R\}$,
and let $\dot Q^X(u) = \langle X_0, X_1, \dots, X_\ell \rangle$ be the word with $X_0 = X$ and
$X_k = \delta(X_{k-1}, u_k)$ for $1 \le k \le \ell$, where $\delta$ is the transition rule that
defines the map $Q$ from sequences over $\{L, R\}$ to sequences over $\{O_L, E_R, O_R, E_L\}$.
Assume that $X_\ell$ is $O_L$ or $O_R$, and let $n$ be the length of the word
$\dot T(\dot Q^X(u))$, where $\dot T$ is the finite version of the map $T$ from sequences over
$\{O_L, E_R, O_R, E_L\}$ to sequences $T(x) = \langle T_1(x), T_2(x), \dots \rangle$ over
$\{L, M, R\}$. Let $\alpha$ be an irrational number with $0 < \alpha < 1$, let
$\mathrm{SB}(\alpha)$ be its Stern–Brocot representation, write
$x = Q(\mathrm{SB}(\alpha)) = \langle x_1, x_2, \dots \rangle$, let $o(1) < o(2) < \cdots$ be the
positions $j$ with $x_j \in \{O_L, O_R\}$, and let $i_0 \ge 1$. Then the $n$ letters
$T_{i_0}(x), \dots, T_{i_0 + n - 1}(x)$ form the word $\dot T(\dot Q^X(u))$ and $x_{o(i_0)} = X$
if and only if the $\ell + 1$ letters $x_{o(i_0)}, x_{o(i_0) + 1}, \dots, x_{o(i_0) + \ell}$ form
the word $\dot Q^X(u)$.

The source assumes $X \in \{O_L, O_R\}$ and $\ell \ge 1$. For $X \in \{E_R, E_L\}$ both sides are
false, since $x_{o(i_0)}$ is $O_L$ or $O_R$; for $\ell = 0$ both sides say $x_{o(i_0)} = X$.

## Sources

- Takanori Hida, *The Mallows Representation of the Irrational Numbers*, INTEGERS 25 (2025), Article A78, Lemma 3 (`integers-2025-A78-lem-3`).
