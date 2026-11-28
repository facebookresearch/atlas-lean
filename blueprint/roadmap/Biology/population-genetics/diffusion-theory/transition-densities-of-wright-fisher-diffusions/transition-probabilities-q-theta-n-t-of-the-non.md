# Finite and entrance transition probabilities for the mutation line-count process

Let $\theta>0$, put $\lambda_k=k(k+\theta-1)/2$ for $k\ge1$ and
$\lambda_0=0$, and let $B$ be the pure-death chain that jumps $k\to k-1$
at rate $\lambda_k$, with zero absorbing. Write
$\rho_k(t)=e^{-\lambda_kt}$,
$a_{(m)}=\prod_{r=0}^{m-1}(a+r)$ and
$a_{[m]}=\prod_{r=0}^{m-1}(a-r)$ for integers $m\ge0$, with empty products one.
For integers $i\ge1$, $1\le j\le i$, and $t\ge0$,

$$p^\theta_{ij}(t)=\mathbb P_i(B_t=j)
 =\sum_{k=j}^{i}\rho_k(t)
 \frac{(-1)^{k-j}(2k+\theta-1)(j+\theta)_{(k-1)}i_{[k]}}
 {j!(k-j)!(i+\theta)_{(k)}}.$$

The zero-state probability, including its constant term, is

$$p^\theta_{i0}(t)=1+\sum_{k=1}^{i}\rho_k(t)
 \frac{(-1)^k(2k+\theta-1)\theta_{(k-1)}i_{[k]}}
 {k!(i+\theta)_{(k)}}.$$

Use $p^\theta_{00}(t)=1$, $p^\theta_{ij}(t)=0$ for $j>i$.
These are nonnegative and each finite row sums to one; at $t=0$ the row is
the point mass at $i$.

There is an entrance process from infinity. For $t>0$ it is finite almost
surely, with probabilities

$$q^\theta_j(t)=\sum_{k=j}^\infty\rho_k(t)
 \frac{(-1)^{k-j}(2k+\theta-1)(j+\theta)_{(k-1)}}{j!(k-j)!},\quad j\ge1,$$

$$q^\theta_0(t)=1+\sum_{k=1}^\infty\rho_k(t)
 \frac{(-1)^k(2k+\theta-1)\theta_{(k-1)}}{k!}.$$

Each displayed infinite series is absolutely convergent for fixed $t>0$.
The $q_j^\theta(t)$ are nonnegative and sum to one. The process tends to
infinity as $t\downarrow0$ and is absorbed at zero in finite time almost
surely. No probability distribution on the finite states at $t=0$ is
claimed for the entrance law.

For the boundary comparison $\theta=0$, the positive-state finite formula
reduces to [the neutral Tavaré formula](../../../coalescent-theory/ancestral-lineage-counting-and-tavar-s-formula/tavare-prob.md)
for $1\le j\le i$. In that case a nonempty chain stops at one rather than
zero; the positive-$\theta$ assertion about absorption at zero does not apply.

## Depends on

- [Neutral Tavaré formula, for the boundary comparison](../../../coalescent-theory/ancestral-lineage-counting-and-tavar-s-formula/tavare-prob.md)

## Expansion

Construct the finite chain using independent holding times
$E_k\sim\operatorname{Exp}(\lambda_k)$. For $s>0$ its occupancy transform is

$$\int_0^\infty e^{-st}p^\theta_{ij}(t)\,dt
 =\frac{\prod_{r=j+1}^i\lambda_r}{\prod_{r=j}^i(s+\lambda_r)},\quad0\le j\le i.$$

The distinct rates satisfy
$\lambda_r-\lambda_k=(r-k)(r+k+\theta-1)/2$. Partial fractions and inversion
give the finite formulas, including the pole at zero for $j=0$. The neutral
formula is a boundary comparison, not a proof of the positive-mutation case.

For the entrance construction let $S_j=\sum_{k=j+1}^\infty E_k$ for $j\ge0$.
The total mean $\sum_{k=1}^\infty1/\lambda_k$ is finite, so $S_0<\infty$
almost surely and $S_j\downarrow0$. Put $B_t=j$ when
$S_j\le t<S_{j-1}$ for $j\ge1$, and $B_t=0$ when $t\ge S_0$.
The finite chains under this holding-time coupling converge at each fixed
positive time to this process almost surely; equality with a jump time has
probability zero.

For fixed $j$ the finite-series factor $i_{[k]}/(i+\theta)_{(k)}$ is in
$[0,1]$ for $k\le i$ and tends to one as $i\to\infty$; set it to zero for
$k>i$. The other coefficients have at most $\exp(O(k\log(k+1)))$ growth,
whereas $\rho_k(t)$ decays as $\exp(-tk^2/2+O(k))$. Dominated convergence
therefore gives the entrance series. Nonnegativity and normalization come
from the entrance process, not from an unjustified rearrangement of a
double alternating series.

## Sources

- S. Tavaré, "Line-of-descent and genealogical processes, and their applications in population genetics models", Theoretical Population Biology 26 (1984), 119–164, <https://doi.org/10.1016/0040-5809(84)90027-3>, (4.7), Sections 5.1–5.2, equations (5.1)–(5.7), and Appendix I. Equation (5.2) is the positive-state finite formula, (5.3) its zero-state case, and (5.5) the entrance formula.
