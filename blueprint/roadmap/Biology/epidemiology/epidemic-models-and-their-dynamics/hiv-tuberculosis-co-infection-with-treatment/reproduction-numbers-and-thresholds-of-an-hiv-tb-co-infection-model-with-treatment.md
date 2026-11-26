# Reproduction numbers and thresholds of an HIV–TB co-infection model with treatment

**Model.** A population with recruitment $\Lambda$ and natural death rate $d$ is split into susceptibles $S$; TB-only classes (latent $T_L$, active $T_I$, under treatment $T_T$); HIV-only classes ($H$, HIV with latent TB $H_L$, HIV under treatment $H^T$); and co-infected classes ($C$, and co-infected under TB treatment in early and late phase, without ($C_1, C_2$) or with ($C_1^T, C_2^T$) antiretroviral therapy). The forces of infection are

$$ \lambda_T = \beta e\,\frac{T_I + C}{N}, \qquad \lambda_H = \lambda\sigma\,\frac{H + H_L + C + C_1 + C_2}{N}, $$

where $\beta e$ and $\lambda\sigma$ are the effective TB and HIV contact rates. Latent TB progresses at rate $k_1$ without HIV ($k_2$ with HIV), active TB is treated at rate $r$ and treated individuals recover to $S$ at rate $r_1$, HIV is treated at rate $r_2$, and $d_T, d_H$ are disease-induced death rates. People under treatment for a disease do not transmit it. The TB-only submodel is

$$ \dot S = \Lambda - \frac{\beta e S T_I}{N} - dS + r_1 T_T, \quad \dot T_L = \frac{\beta e S T_I}{N} - (d+k_1)T_L, \quad \dot T_I = k_1 T_L - (d+d_T+r)T_I, \quad \dot T_T = rT_I - (r_1+d+d_T)T_T, $$

and the HIV-only submodel is

$$ \dot S = \Lambda - \frac{\lambda\sigma S H}{N} - dS, \quad \dot H = \frac{\lambda\sigma S H}{N} - (r_2+d+d_H)H, \quad \dot H^T = r_2 H - (d+d_H)H^T. $$

Both have the disease-free state $S = \Lambda/d$, where $N = \Lambda/d$, and the reproduction numbers

$$ \mathcal R_0^T = \frac{\beta e\,k_1}{(d+k_1)(d+r+d_T)}, \qquad \mathcal R_0^H = \frac{\lambda\sigma}{r_2+d+d_H}, \qquad \mathcal R_0 = \max\{\mathcal R_0^T, \mathcal R_0^H\}. $$

**Theorem.**

1. All solutions of the full 12-compartment model with non-negative initial data stay non-negative, and $\{N \le \Lambda/d\}$ is positively invariant.
2. In each submodel the disease-free equilibrium is globally asymptotically stable when its reproduction number is below $1$ and unstable above $1$. When it is above $1$ there is a unique endemic equilibrium, which is locally asymptotically stable.
3. In the full model the disease-free equilibrium $E_0$ is locally asymptotically stable if $\mathcal R_0 < 1$ and unstable if $\mathcal R_0 > 1$.
4. The TB-only boundary equilibrium $E_T$ exists for $\mathcal R_0^T > 1 > \mathcal R_0^H$ and bifurcates from $E_0$ through a supercritical (forward) transcritical bifurcation at $\mathcal R_0^T = 1$, with bifurcation parameter $\beta e$. It is locally asymptotically stable for $\mathcal R_0^T$ near $1$.
5. Symmetrically, the HIV-only equilibrium $E_H$ exists for $\mathcal R_0^H > 1 > \mathcal R_0^T$ and arises through a supercritical transcritical bifurcation at $\mathcal R_0^H = 1$, with bifurcation parameter $\lambda\sigma$.

## Expansion

At the disease-free state the Jacobian is block triangular. The TB block gives the characteristic factor $x^2 + (2d+r+d_T+k_1)x + (d+k_1)(d+r+d_T) - \beta e k_1$, whose coefficients are all positive iff $\mathcal R_0^T < 1$ (Routh–Hurwitz). The HIV block has the eigenvalue $\lambda\sigma - (r_2+d+d_H)$. The co-infection classes are fed only by products of the two infections, so they add no new threshold, and the spectral radius of the full next-generation matrix is the larger of the two single-disease numbers. Global stability in the submodels follows the Castillo-Chavez decomposition: the uninfected subsystem converges to $\Lambda/d$, and the infected subsystem is $A\mathbf I - \hat G$ with $A$ a Metzler matrix and $\hat G \ge 0$ because $S \le N$. The forward transcritical bifurcations come from center-manifold theory (Castillo-Chavez–Song). Treatment enters the thresholds only through $r$ and $r_2$. Treating TB-only and HIV-only cases lowers $\mathcal R_0^T$ and $\mathcal R_0^H$ directly, while co-infection treatment alone does not change either number.

## Depends on

- [Next-generation basic reproduction number](../../next-generation-matrix-and-the-basic-reproductio/r0.md)

## Sources

- Sachin Kumar and Shikha Jain, "Assessing the Effects of Treatment in HIV-TB Co-infection Model", arXiv:1709.10353 (2017): Section 2 (model, Theorem 2.1), Section 3 (TB submodel, Theorems 3.1–3.4), Section 4 (HIV submodel, Theorems 4.1–4.4), Section 5 (full model, Theorems 5.1–5.3). <https://doi.org/10.48550/arXiv.1709.10353> Published version: Eur. Phys. J. Plus (2018) 133: 294, <https://doi.org/10.1140/epjp/i2018-12117-8>.
