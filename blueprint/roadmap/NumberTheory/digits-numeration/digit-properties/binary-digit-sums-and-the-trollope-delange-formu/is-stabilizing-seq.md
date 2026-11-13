# Stabilizing sequence for the dyadic odometer

Let $q \in \mathbb{C}$, let $\omega$ be a
dyadic integer, let $S_{q,\omega}$ be the interpolated odometer partial sum, and for a natural
number $l$ let $M_{q,\omega}(l) = \sup_{t \in [0, 1]} |S_{q,\omega}(tl) - t S_{q,\omega}(l)|$ be the
maximal fluctuation. A sequence $(l_n)$ of natural numbers is a stabilizing sequence for
$(q, \omega)$ with normalizing sequence $(R_n)$ of complex numbers and limiting curve
$\varphi : \mathbb{R} \to \mathbb{C}$ when: every $l_n$ is positive and $l_n \to \infty$; every
$R_n$ is nonzero and $|R_n| \to \infty$; there are real constants $c > 0$ and $C$ with
$c M_{q,\omega}(l_n) \le |R_n| \le C M_{q,\omega}(l_n)$ for all sufficiently large $n$;
$\varphi$ is continuous on $[0, 1]$; and the functions
$t \mapsto (S_{q,\omega}(t l_n) - t S_{q,\omega}(l_n))/R_n$ converge uniformly on $[0, 1]$ to
$\varphi$.

The normalizing sequence $R_n$ is chosen of the order of $M_{q,\omega}(l_n)$, not equal to it:
with equality every normalized fluctuation would have supremum norm at most $1$, so the limit in
Theorem 2 of Article A61 could not be the negative Takagi–Landsberg function $-\mathcal{T}_a$
(for example $\mathcal{T}_{3/4}(1/3) = 4/3$). This matches the sources' usage, where
$\varphi^{l_n,R_n}$ is parametrized by the chosen $R_n$ (e.g. $R_n = (2q)^{n-1}$ along
$l_n = 2^n$ in Article A61, Section 3); unbounded growth of $R_n$ is the necessary condition for
a limiting curve recorded in the odometer paper.

## Sources

- Aleksei Minabutdinov, *Limiting curves for the dyadic odometer and the generalized Trollope-Delange formula*, Definition 1 and Section 3.1, restated in *A q-Weighted Analogue of the Trollope-Delange Formula*, INTEGERS 26 (2026), Article A61, Section 3.
