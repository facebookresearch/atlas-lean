# $a$, $b$, $c$, $d$ divide gcds of reduced differences

Let $a, b, c, d$ be natural numbers
and put $s_1 = ab + 1$, $s_2 = ac + 1$, $s_3 = ad + 1$, $s_4 = bc + 1$, $s_5 = bd + 1$,
$s_6 = cd + 1$. For indices $i, j$ let $t_{ij}$ be the integer $(s_j - s_i) / \gcd(s_j, s_i)$.
Then $a \mid \gcd(t_{12}, t_{13}, t_{23})$, $b \mid \gcd(t_{14}, t_{15}, t_{45})$,
$c \mid \gcd(t_{24}, t_{26}, t_{46})$ and $d \mid \gcd(t_{35}, t_{36}, t_{56})$ in $\mathbb{Z}$.

The source assumes that $\{a, b, c, d\}$ is $S$-Diophantine; that hypothesis is not needed.

## Sources

- Volker Ziegler, *On the Existence of `{p, q}`-Diophantine Quadruples and Quintuples*, INTEGERS 25 (2025), Article A92, Lemma 3, quoting Szalay and Ziegler (2013), Lemma 3.
