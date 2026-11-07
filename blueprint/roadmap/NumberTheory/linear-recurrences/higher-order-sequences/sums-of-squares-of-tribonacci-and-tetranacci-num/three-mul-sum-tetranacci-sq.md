# Sum of squares of a Tetranacci sequence

Let $Q \colon \mathbb{Z} \to \mathbb{Z}$ satisfy
$Q(m+4) = Q(m+3) + Q(m+2) + Q(m+1) + Q(m)$ for every integer $m$. Then for every natural
number $n$,

$$3 \sum_{k=1}^{n} Q(k)^2 = 3\,Q(n)\,Q(n+1) - 3\,Q(0)\,Q(1) - \bigl(Q(n+1) - Q(n-1)\bigr)^2 +
\bigl(Q(1) - Q(-1)\bigr)^2 + Q(n-2)\bigl(Q(n) + Q(n-3)\bigr) - Q(-2)\bigl(Q(0) + Q(-3)\bigr).$$

Inside the boundary terms the sums $Q(n) + Q(n-3)$ and $Q(0) + Q(-3)$ carry a plus sign, as in
Gryszka's Lemma 2; this sign is the one forced by the paper's telescoping calculation.

## Sources

- Karol Gryszka, "A Simple Proof of the Formula for the Sum of Tribonacci and Tetranacci Numbers Squared", Theorem 2.
