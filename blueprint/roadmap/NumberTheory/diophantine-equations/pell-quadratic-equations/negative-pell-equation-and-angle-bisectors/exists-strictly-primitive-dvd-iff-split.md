# Strictly primitive solutions modulo p and splitting of p

Let $d > 1$ be a square-free
integer, let $K$ be a number field of degree $2$ over $\mathbb{Q}$ containing an element $s$ with
$s^2 = d$ (so $K = \mathbb{Q}(\sqrt d)$), and let $p$ be a prime such that $p \ne 2$, or
$d \equiv 1 \pmod 8$, or $d \equiv 2 \pmod 4$. Then there are integers $x, y$ with $x$ and $dy$
coprime and $p \mid x^2 - dy^2$ if and only if $p$ splits in $K$, that is, exactly two prime
ideals of the ring of integers of $K$ lie over $p$.

In the paper's terms: $|x^2 - dy^2| = z$ has a strictly primitive integral solution for some
multiple $z$ of $p$ exactly when $p$ splits. The paper requires only $p \ne 2$ or
$d \not\equiv 5 \pmod 8$; for $d \equiv 3 \pmod 4$ and $p = 2$ its statement fails: for $d = 3$,
$(x, y) = (1, 1)$ gives $|1 - 3| = 2$ with $\gcd(1, 3) = 1$, while $2$ ramifies in
$\mathbb{Q}(\sqrt 3)$.

## Sources

- Takashi Hirotsu, *General Pell's Equations and Angle Bisectors between Planar Lines with Rational Slopes*, INTEGERS 24 (2024), Article A111, Theorem 7 (`integers-2024-A111-thm-7`).
