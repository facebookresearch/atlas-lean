# Powers of $2$ dividing the $C_4$ group determinant at four parity patterns

Let
$D(x_0, x_1, x_2, x_3)$ be the group determinant of $C_4$, that is the determinant of the
$4 \times 4$ circulant matrix with $(i, j)$ entry $x_{i - j}$ (indices mod $4$). For integers
$k, l, m, n$ put $D_1 = D(2k, 2l, 2m, 2n)$, $D_2 = D(2k+1, 2l+1, 2m+1, 2n+1)$,
$D_3 = D(2k, 2l+1, 2m, 2n+1)$, $D_4 = D(2k, 2l, 2m+1, 2n+1)$,
$w_3 = (2k+2l+1)(2m+2n+1)$ and $w_4 = (2k+2m+1)(2l+2n+1)$, and write $2^e \mathbb{Z}_{odd}$
for the set of integers $2^e(2t+1)$ with $t \in \mathbb{Z}$. Then:

* if $k + m \not\equiv l + n \pmod 2$ then $D_1 \in 2^4 \mathbb{Z}_{odd}$, and if
  $k + m \equiv l + n \pmod 2$ then $2^8 \mid D_1$;
* if $k + m \not\equiv l + n \pmod 2$ then $D_2 \in 2^4 \mathbb{Z}_{odd}$; if
  $(k + m)(l + n) \equiv -1 \pmod 4$ then $D_2 \in 2^7 \mathbb{Z}_{odd}$; and if
  $k + m \equiv l + n \pmod 2$ and $(k + m)(l + n) \not\equiv -1 \pmod 4$ then $2^9 \mid D_2$;
* if $k - m$ and $l - n$ are both odd then $D_3 \in 2^5 \mathbb{Z}_{odd}$; if
  $k \equiv m \pmod 2$ and $w_3 \equiv \pm 3 \pmod 8$ then $D_3 \in 2^6 \mathbb{Z}_{odd}$; and if
  neither of these two conditions holds then $2^7 \mid D_3$;
* if $w_4 \equiv \pm 3 \pmod 8$ then $D_4 \in 2^4 \mathbb{Z}_{odd}$, and if
  $w_4 \equiv \pm 1 \pmod 8$ then $2^5 \mid D_4$.

## Sources

- Yuka Yamaguchi and Naoya Yamaguchi, *Integer Group Determinants for C_4^2*, INTEGERS 24 (2024), Article A30, Lemma 7 (`integers-2024-A30-lem-7`).
