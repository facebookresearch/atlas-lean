# Turing instability of the mean-field survival model for zebrafish stripes

**Model.** On a ring of $N$ cell sites $j \in \mathbb{Z}/N\mathbb{Z}$, let $X_j(t)$ and $M_j(t)$ be the probabilities that site $j$ holds a xanthophore or a melanophore. The (simplified) mean-field survival model is

$$\begin{aligned}
X_j' &= 1 - X_j - M_j - X_j\,\tfrac{M_{j-1} + M_{j+1}}{2},\\
M_j' &= (b+1)(1 - X_j) - (b+d+1)M_j - M_j\,\tfrac{X_{j-1} + X_{j+1}}{2} + d\,M_j\,\tfrac{X_{j-h} + X_{j+h}}{2},
\end{aligned}$$

with kinetic parameters $b, d > 0$ and a long-range interaction distance $1 \le h \le N/2$ (melanophores are sustained by xanthophores $h$ sites away, killed by neighbouring xanthophores, and kill neighbouring xanthophores). Apart from the trivial state $(1,0)$ it has the homogeneous coexistence equilibrium

$$(X^*, M^*) = \Big(\frac{d}{b+d},\ \frac{b}{b+2d}\Big).$$

Linearising and taking the discrete Fourier transform decouples the perturbation into $2\times 2$ blocks indexed by the mode $k \in \{0,\dots,N-1\}$, in which the coupling enters only through $x_k = \cos(2\pi k/N)$ and $T_h(x_k)$, where $T_h$ is the Chebyshev polynomial of the first kind of order $h$ (so $T_h(x_k) = \cos(2\pi h k/N)$). Let

$$\mathcal{P} = \{(b,d) : 0 < b < d\}.$$

**Theorem (discrete Turing bifurcation).**
1. If $(b,d) \in \mathcal{P}$, there is $H_1 \ge 3$ depending only on $(b,d)$, and $N_1$ depending on $(b,d)$ and $h$, such that for all $h \ge H_1$ and $N \ge N_1$ the coexistence equilibrium is linearly unstable to spatially periodic perturbations in some Fourier mode $k \neq 0$ (a Turing instability). Moreover, for $N$ large enough the fastest-growing mode satisfies

$$\Big\lceil \frac{N}{4h} \Big\rceil \le k \le \Big\lceil \frac{N}{2h} \Big\rceil,$$

so the pattern wavelength $N/k$ lies between $2h$ and $4h$ sites.
2. If $(b,d) \notin \mathcal{P}$, the coexistence equilibrium is linearly stable.
3. For $h = 1, 2$ the equilibrium is linearly stable for all admissible $(b,d)$; for every $h \ge 3$ and $N$ large enough, some nonzero mode is unstable for some $(b,d)$, and the instability region of mode $k$ is contained in $\mathcal{P}$.
4. The trivial equilibrium $(1,0)$ is unstable exactly in the modes $k$ with $x_k > 1/(b+1)$; at $x_k = 1/(b+1)$ the mode matrix has eigenvalues $0$ and $-(b+3)$ and the mode is neutral.

## Proof sketch

For mode $k$ the linearisation at a homogeneous state $(X_H, M_H)$ is

$$\hat L_k = \begin{pmatrix} -M_H - 1 & -x_k X_H - 1 \\ (d\,T_h(x_k) - x_k) M_H - b - 1 & (d-1)X_H - b - d - 1\end{pmatrix},$$

and the mode is unstable iff a real eigenvalue becomes positive, which reduces to a sign condition $F(x_k, T_h(x_k), b, d) < 0$ on a polynomial $F$. Because $T_h$ oscillates $h$ times faster than $x \mapsto x$, short-range inhibition and long-range activation can make $F$ negative only at frequencies near $1/(4h)$ to $1/(2h)$, and only when $b < d$. The result explains stripe widths of order the melanophore projection length and shows that the $N \to \infty$ continuum PDE can mispredict the onset of instability.

## Sources

- Robert Jencks, "The mean-field survival model for stripe formation in zebrafish exhibits Turing instability", *Mathematical Biosciences* 385 (2025), 109463, <https://doi.org/10.1016/j.mbs.2025.109463>. Preprint version: arXiv:2411.15293 (2024), Proposition 1 and Theorems 1–2 (Main Results), <https://doi.org/10.48550/arXiv.2411.15293>.
