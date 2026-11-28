# Global dynamics of the residence-times SIS patch model

**Model.** Residents of patch $i \in \{1, \dots, n\}$ have births $b_i$, deaths $d_i$ and recovery $\gamma_i$, with no disease deaths, so $N_i = S_i + I_i \to b_i/d_i$. They spend the fraction $p_{ij} \in [0,1]$ of their time in patch $j$. The **residence-times matrix** $\mathbb{P} = (p_{ij})$ satisfies (HP1) every column has a positive entry and (HP2) every row sums to $1$. Patch $j$ carries an environmental risk $\beta_j$ per unit time. The effective population present in patch $j$ is $\sum_kp_{kj}N_k$, of which $\sum_kp_{kj}I_k$ is infected, so the incidence on patch-$i$ susceptibles is $\sum_j\beta_j\,p_{ij}S_i\,\frac{\sum_kp_{kj}I_k}{\sum_kp_{kj}N_k}$. On the limiting population sizes, with $\bar N = (b_i/d_i)_i$, $\tilde N = \mathbb{P}^{t}\bar N$ and $\mathcal{B} = (\beta_j)_j$, the infected vector obeys

$$
\dot I = \mathrm{diag}(\bar N - I)\,\mathbb{P}\,\mathrm{diag}(\mathcal{B})\,\mathrm{diag}(\tilde N)^{-1}\mathbb{P}^{t}I - \mathrm{diag}(d + \gamma)I
$$

on the invariant box $0 \le I \le \bar N$. The basic reproduction number is

$$
\mathcal{R}_0 = \rho\left(\mathrm{diag}(\bar N)\,\mathbb{P}\,\mathrm{diag}(\mathcal{B})\,\mathrm{diag}(\tilde N)^{-1}\mathbb{P}^{t}\,\mathrm{diag}(d+\gamma)^{-1}\right).
$$

**Theorem (global dynamics).** If $\mathbb{P}$ is irreducible:
1. If $\mathcal{R}_0 \le 1$, the disease-free equilibrium $I = 0$ is globally asymptotically stable. If $\mathcal{R}_0 > 1$ it is unstable.
2. If $\mathcal{R}_0 > 1$, there is a unique endemic equilibrium $\bar I \gg 0$, and it is globally asymptotically stable.

**Theorem (patch-level endemicity).** Let $\mathcal{R}_0^i = \beta_i/(d_i + \gamma_i)$ be the reproduction number of the isolated patch $i$ and

$$
\mathcal{R}_0^i(\mathbb{P}) = \mathcal{R}_0^i\sum_{j=1}^n\frac{\beta_j}{\beta_i}\,p_{ij}\,\frac{p_{ij}\,b_i/d_i}{\sum_{k=1}^np_{kj}\,b_k/d_k}.
$$

Assume (HP1)–(HP2), allowing zero entries in $\mathbb{P}$.
1. If $\mathcal{R}_0^i(\mathbb{P}) > 1$, the disease persists in patch $i$.
2. If patch $i$ residents never share a patch with anyone else ($p_{kj} = 0$ for all $k \neq i$ whenever $p_{ij} > 0$), then $\mathcal{R}_0^i(\mathbb{P}) = \mathcal{R}_0^i\sum_j(\beta_j/\beta_i)p_{ij}$, and if this is below $1$, $I_i(t) \to 0$.

So movement can create endemicity in an otherwise safe patch, by spending time in high-risk patches ($\beta_j/\beta_i > 1/\mathcal{R}_0^i$). It can also remove endemicity from a patch with $\mathcal{R}_0^i > 1$ when its residents spend enough time in low-risk patches.

## Depends on

- [Basic reproduction number of the next-generation matrix](../../next-generation-matrix-and-the-basic-reproductio/r0.md)

## Expansion

Each total population converges to $b_i/d_i$, so the theory of asymptotically autonomous triangular systems reduces the model to the $I$-system on the box. That system is cooperative: off-diagonal Jacobian entries $(\bar N_i - I_i)[\mathbb{P}\mathrm{diag}(\mathcal{B})\mathrm{diag}(\tilde N)^{-1}\mathbb{P}^{t}]_{ik} \ge 0$. Its Jacobian is irreducible when $\mathbb{P}$ is, and the Jacobian decreases as $I$ increases, i.e. the system is strictly sublinear. Hirsch's theorem for such systems gives the dichotomy: either all orbits tend to $0$, or there is a unique interior equilibrium attracting all nonzero orbits. Which case occurs is decided by the sign of the stability modulus of the Jacobian at $0$, i.e. by $\mathcal{R}_0$ versus $1$ (van den Driessche–Watmough). The patch-level persistence bound comes from the diagonal term of the $I_i$ equation. Under the isolation condition the cross terms vanish and the $I_i$ equation becomes a scalar logistic SIS equation with transmission $\sum_j\beta_jp_{ij}$.

## Sources

- Derdei Bichara, Yun Kang, Carlos Castillo-Chavez, Richard Horan and Charles Perrings, "SIS and SIR epidemic models under virtual dispersal", arXiv:1503.08881 (2015), Section 2 (model derivation, Theorems 2.1 and 2.2), Appendix sections on the computation of $\mathcal{R}_0$ and the proofs of Theorems 2.1–2.2, <https://doi.org/10.48550/arXiv.1503.08881>. Published version: Bulletin of Mathematical Biology 77(11) (2015), 2004–2034, <https://doi.org/10.1007/s11538-015-0113-5>; locators above refer to the arXiv version.
