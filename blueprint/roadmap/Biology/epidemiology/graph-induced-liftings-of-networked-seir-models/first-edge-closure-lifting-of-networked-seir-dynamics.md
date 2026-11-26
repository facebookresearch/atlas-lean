# First edge-closure lifting of networked SEIR dynamics

**Setting.** Let $\mathcal V=\{1,\dots,n\}$ be subpopulations with a nonnegative weight matrix $A=[a_{ij}]$ and effective transmission support $\mathcal E=\{(i,j):a_{ij}>0\}$ (diagonal pairs allowed), $m=|\mathcal E|$. With normalized fractions $S_i+E_i+I_i+R_i=1$, the networked SEIR model is
$$\dot S_i=-\beta\sum_j a_{ij}S_iI_j,\quad \dot E_i=\beta\sum_j a_{ij}S_iI_j-\sigma E_i,\quad \dot I_i=\sigma E_i-\gamma I_i,\quad \dot R_i=\gamma I_i,$$
with state $x\in\mathbb R^{4n}$ in the admissible set $\Omega$ (all compartments in $[0,1]$ summing to $1$ at each node, which is positively invariant). Write $\delta_i^{\mathrm{in}}=\sum_\ell a_{i\ell}$ for the weighted in-degree, $\delta^{\mathrm{in}}_{\max}=\max_i\delta_i^{\mathrm{in}}$, and $\Delta^{\mathrm{in}}$ for the maximum (unweighted) in-degree of the support.

**Statement.**

1. (Edge-based quadratic form) With the edge dictionary $\phi^{SI}_e(x)=S_{i_e}I_{j_e}$, $e=(i_e,j_e)\in\mathcal E$, the dynamics are exactly
$$\dot x=A_\ell\,x+M\,\phi^{SI}(x),$$
where $A_\ell$ collects the linear transitions ($\sigma$, $\gamma$) and $M\in\mathbb R^{4n\times m}$ has two nonzero entries per column, $M_{i_e,e}=-\beta a_{i_ej_e}$ and $M_{n+i_e,e}=+\beta a_{i_ej_e}$. The nonlinearity is carried by $m$ bilinear monomials.
2. (First edge-closure lifting) Let $\phi^{SE}_e(x)=S_{i_e}E_{j_e}$ and $z_2(x)=\bigl(x,\phi^{SI}(x),\phi^{SE}(x)\bigr)\in\mathbb R^{4n+2m}$. Then
$$\frac{d}{dt}z_2(x)=K_2\,z_2(x)+r_2(x)$$
for a graph-structured matrix $K_2$, where the residual vanishes in the $x$-block and, for $e=(i_e,j_e)$,
$$(r_{SI})_e=-\beta\sum_{\ell:(i_e,\ell)\in\mathcal E}a_{i_e\ell}S_{i_e}I_\ell I_{j_e},\qquad (r_{SE})_e=-\beta\sum_{\ell:(i_e,\ell)\in\mathcal E}a_{i_e\ell}S_{i_e}I_\ell E_{j_e}+\beta\sum_{\ell:(j_e,\ell)\in\mathcal E}a_{j_e\ell}S_{i_e}S_{j_e}I_\ell .$$
Every nonzero residual component is a homogeneous cubic.
3. (Residual bound) For every $x\in\Omega$,
$$\|r_2(x)\|_\infty\le 2\beta\,\delta^{\mathrm{in}}_{\max},\qquad \|r_2(x)\|_2\le\sqrt{5m}\,\beta\,\delta^{\mathrm{in}}_{\max} .$$

## Depends on

- [SEIR epidemic model](../seir-epidemic-model/README.md)

## Expansion

Only infection creates nonlinear terms, and channel $(i,j)$ moves mass $\beta a_{ij}S_iI_j$ from $S_i$ to $E_i$, which gives the two-entry columns of $M$. Differentiating $S_iI_j$ gives $\dot S_iI_j+S_i\dot I_j$; the term $\sigma S_iE_j$ is the $SE$ monomial of the same channel and $-\gamma S_iI_j$ is itself in the dictionary, while $\dot S_iI_j$ produces the cubic terms of $r_{SI}$. Differentiating $S_iE_j$ similarly yields $-\sigma S_iE_j$ (linear part) plus cubic terms from $\dot S_i$ and from the infection inflow into $E_j$. So the dictionary $\{x,\phi^{SI},\phi^{SE}\}$ is closed under the linear field and the cubic remainder is exactly the omitted part. On $\Omega$ all variables lie in $[0,1]$, so each $SI$ residual is bounded by $\beta\delta_{i_e}^{\mathrm{in}}$ and each $SE$ residual by $\beta(\delta_{i_e}^{\mathrm{in}}+\delta_{j_e}^{\mathrm{in}})$; summing squares over the $2m$ components gives the $\ell_2$ bound. The bound depends on the network only through the incoming transmission intensity, not on the number of nodes.

## Sources

- Enrique Baeyens, "Graph-Induced Tensor Liftings for Networked SEIR Models: Dimensional Reduction and Residual Analysis", arXiv:2607.17664 (2026), Proposition 1, Proposition 2, Proposition 5 and Proposition 8, <https://doi.org/10.48550/arXiv.2607.17664>
