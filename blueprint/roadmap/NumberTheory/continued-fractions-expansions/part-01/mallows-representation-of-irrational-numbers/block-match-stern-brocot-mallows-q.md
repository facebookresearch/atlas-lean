# Block-matching lemma

Let $\alpha \in (0, 1)$ be irrational, let $x = \mathrm{SB}(\alpha)$
be its Stern–Brocot representation, let $q = Q(x)$ be the image of $x$ under Hida's map $Q$ to
sequences over $\{O_L, E_R, O_R, E_L\}$, and let $T(q)$ be the image of $q$ under Hida's map $T$
to sequences over $\{L, M, R\}$; all sequences are indexed from $0$. Let $o(i)$ be the $i$-th
position, counting from $0$, at which $q$ takes the value $O_L$ or $O_R$. Then for all natural
numbers $\ell$, $j_1$, $j_2$, $i_1$, $i_2$, with $-$ denoting truncated subtraction of natural
numbers:
(i) $x_{j_1 + t} = x_{j_2 + t}$ for all $t < \ell$ together with $q_{j_1} = q_{j_2}$ holds if and
only if $q_{j_1 + t} = q_{j_2 + t}$ for all $t \le \ell$;
(ii) $T(q)_{i_1 + t} = T(q)_{i_2 + t}$ for all $t < \ell$ together with $q_{o(i_1)} = q_{o(i_2)}$
holds if and only if $q_{o(i_1) + t} = q_{o(i_2) + t}$ for all $t \le o(i_1 + \ell) - o(i_1)$;
(iii) if $T(q)_{i_1 + t} = T(q)_{i_2 + t}$ for all $t < \ell$ and $q_{o(i_1)} = q_{o(i_2)}$, then
$o(i_2 + k) - o(i_2) = o(i_1 + k) - o(i_1)$ for all $k \le \ell$.

The paper assumes $\ell \ge 1$, $j_1 < j_2$ and $i_1 < i_2$; the statement is trivial for
$\ell = 0$, symmetric in the two positions, and trivial for equal positions.

## Sources

- Takanori Hida, *The Mallows Representation of the Irrational Numbers*, INTEGERS 25 (2025), Article A78, Lemma 2.
