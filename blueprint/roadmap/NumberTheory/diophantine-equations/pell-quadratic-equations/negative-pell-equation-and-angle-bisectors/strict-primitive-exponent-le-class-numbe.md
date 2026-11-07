# The strictly primitive exponent is at most the class number

Let $d > 1$ be a squarefree
integer with $d \equiv 2$ or $d \equiv 3 \pmod 4$, and let $K$ be a number field of degree $2$
containing a square root of $d$ (so $K \cong \mathbb{Q}(\sqrt{d})$). Let $S(d)$ be the set of
primes $p$ for which $|x^2 - d y^2| = p^l$ has a strictly primitive integral solution ($x$ and
$d y$ coprime) for some integer $l > 0$, and for $p \in S(d)$ let $l_p$ be the least such $l$.
Then $l_p \le h_K$ for every $p \in S(d)$, where $h_K$ is the class number of $K$.

The source states this for all squarefree $d > 1$ except $d \equiv 1 \pmod 4$ with $p = 2$. For
$d \equiv 5 \pmod 8$ that is false: $\mathbb{Q}(\sqrt{37})$ has class number $1$, but $l_3 = 3$
for $d = 37$, since $8^2 - 37 \cdot 1^2 = 27$ while $|x^2 - 37 y^2| = 3$ and $|x^2 - 37 y^2| = 9$
have no strictly primitive solutions (the elements of norm $\pm 3$ and $\pm 9$ generating
primitive ideals are $(5 \pm \sqrt{37}) / 2$ and $(31 \pm 5\sqrt{37}) / 2$ times units, and all
units lie in $\mathbb{Z}[\sqrt{37}]$).

## Sources

- Takashi Hirotsu, *General Pell's Equations and Angle Bisectors between Planar Lines with Rational Slopes*, INTEGERS 24 (2024), Article A111, Corollary 1 (`integers-2024-A111-cor-1`).
