# Structure of four-digit Kaprekar dynamics in odd bases

Let $B > 3$ be an odd integer.
For a pair of natural numbers $d = (d_1, d_2)$, let $K(d) = (a - e, b - c)$, where
$a \ge b \ge c \ge e$ are the four numbers $d_1 - 1, B - 1, B - 1, B - d_1$ if $d_2 = 0$, and
$d_1, d_2 - 1, B - d_2 - 1, B - d_1$ if $d_2 \ne 0$, sorted in decreasing order (subtraction is
truncated at $0$). Let $X_B$ be the set of pairs with $1 \le d_1 < B$ and $d_2 \le d_1$, and let
$T_B$ be the set of pairs in $X_B$ with $0 < d_2 < d_1$ and $d_1$, $d_2$ both odd. Let
$\mathcal{P}$ be the set of two-element sets $S$ of subsets of $\mathbb{Z}/B\mathbb{Z}$ such that
every $C \in S$ has the form $\{x, -x\}$ with $x \ne 0$. For a set $S$ of subsets of
$\mathbb{Z}/B\mathbb{Z}$ let $2S = \{2C : C \in S\}$, where $2C = \{2y : y \in C\}$, and for
$d \in T_B$ let $\Phi(d) = \{\{u, -u\}, \{v, -v\}\}$, where $u$ and $v$ are the residues of
$(d_1 + d_2)/2$ and $(d_1 - d_2)/2$ modulo $B$. Then $K$ maps $T_B$ into itself, the third
iterate $K^3$ maps $X_B$ into $T_B$, $S \mapsto 2S$ maps $\mathcal{P}$ into itself, $\Phi$ is a
bijection from $T_B$ onto $\mathcal{P}$, and $\Phi(K(d)) = 2\,\Phi(d)$ for every $d \in T_B$.

Here a pair $(d_1, d_2) \in X_B$ stands for the four-digit base-$B$ numbers whose digits, sorted
as $a \ge b \ge c \ge e$, satisfy $a - e = d_1$ and $b - c = d_2$; the four numbers listed above
are the base-$B$ digits of their Kaprekar image, so $K$ is the Kaprekar map on these pairs.

## Sources

- Evan Chen, Ken Ono, Richard E. Schwartz, and Dinesh Thakur, "Four-Digit Kaprekar Dynamics in Odd Bases", Journal of Integer Sequences 29 (2026), Article 26.4.7, Theorem `thm:structural`, lines 220-230, <https://cs.uwaterloo.ca/journals/JIS/VOL29/Ono/ono3.tex>.
