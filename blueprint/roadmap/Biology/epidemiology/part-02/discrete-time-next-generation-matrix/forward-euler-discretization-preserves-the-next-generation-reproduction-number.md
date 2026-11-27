# Forward-Euler discretization preserves the next-generation reproduction number

**Discrete-time next-generation theorem.** Let $X_{n+1} = G(X_n)$ be a difference-equation epidemic model on $\mathbb R^{d}_{+}$ with $G$ of class $C^1$, the first $k$ coordinates being infected compartments, and with a unique disease-free equilibrium (DFE) $x_0$ at which the Jacobian has the block form

$$J(x_0) = \begin{pmatrix} \Phi + H & 0 \\ A & C \end{pmatrix},$$

where the $k \times k$ matrices $\Phi$ (new infections) and $H$ (survival and transitions within infected compartments) are entrywise nonnegative, $\Phi + H$ is irreducible, and the spectral radii satisfy $\rho(H) < 1$ and $\rho(C) < 1$. Then the basic reproduction number is $R_0 = \rho\big(\Phi (I - H)^{-1}\big)$, and the DFE is locally asymptotically stable if $R_0 < 1$ and unstable if $R_0 > 1$.

**Proposition (step-size invariance).** Let $\dot x = f(x)$ be a continuous-time model whose infected subsystem linearized at the DFE is $\dot y = (\mathcal F - \mathcal V) y$, with $\mathcal F \ge 0$ and $\mathcal V$ a nonsingular M-matrix, so that $R_0^{\mathrm{cont}} = \rho(\mathcal F \mathcal V^{-1})$. Its forward-Euler discretization $X_{n+1} = X_n + h f(X_n)$ with step $h > 0$ has, at the same DFE, $\Phi = h\mathcal F$ and $H = I - h\mathcal V$. If $h \max_i \mathcal V_{ii} \le 1$ (so $H \ge 0$), then $\rho(H) < 1$, $(I - H)^{-1} = h^{-1}\mathcal V^{-1}$, and

$$R_0^{\mathrm{disc}} = \rho\big(h\mathcal F\,(h\mathcal V)^{-1}\big) = \rho(\mathcal F \mathcal V^{-1}) = R_0^{\mathrm{cont}},$$

independent of $h$. Local stability of the DFE of the discrete map additionally requires $\rho(C) < 1$ for the uninfected block $C = I + h D$, a step-size condition that the continuous model does not impose.

**Example.** In the discrete COVID-19 model with susceptible $S$, untreated infectious $I$ and isolated treated $T$ classes,

$$S_{n+1} = S_n + h\Big[\Lambda - \frac{\alpha S_n I_n}{1 + \delta T_n} - (\gamma_1 + d_1) S_n\Big], \quad I_{n+1} = I_n + h\Big[\frac{\alpha S_n I_n}{1 + \delta T_n} - (\beta + d_1) I_n\Big],$$

$$T_{n+1} = T_n + h\big[\beta I_n - (\gamma_2 + d_1 + d_2) T_n\big],$$

with all parameters positive, the DFE is $(S_0, 0, 0)$ with $S_0 = \Lambda/(\gamma_1 + d_1)$, the infected blocks are $\Phi = \begin{pmatrix} h\alpha S_0 & 0 \\ 0 & 0 \end{pmatrix}$ and $H = \begin{pmatrix} 1 - h(\beta + d_1) & 0 \\ h\beta & 1 - h(\gamma_2 + d_1 + d_2) \end{pmatrix}$, and

$$R_0 = \frac{\alpha\Lambda}{(\gamma_1 + d_1)(\beta + d_1)}.$$

The DFE Jacobian has eigenvalues $1 - h(\gamma_1 + d_1)$, $1 + h\big(\alpha S_0 - (\beta + d_1)\big)$ and $1 - h(\gamma_2 + d_1 + d_2)$, so for steps with $h(\gamma_1 + d_1) < 2$, $h(\gamma_2 + d_1 + d_2) < 2$ and $h(\beta + d_1 - \alpha S_0) < 2$ the DFE is stable exactly when $R_0 < 1$.

## Depends on

- [Basic reproduction number of the next-generation matrix](../../next-generation-matrix-and-the-basic-reproductio/r0.md)
- [$R_0$ as a threshold for the linearized infected subsystem](../../next-generation-matrix-and-the-basic-reproductio/is-hurwitz-sub-iff-r0-lt-one.md)

## Expansion

For the discrete theorem, the infected block $\Phi + H$ is nonnegative, and with $\rho(H) < 1$ one has $\rho(\Phi + H) < 1$ if and only if $\rho(\Phi(I - H)^{-1}) < 1$ (and likewise with $>$), by the standard M-matrix splitting argument applied to $I - H - \Phi$; the block-triangular form makes the spectrum of $J(x_0)$ the union of those of $\Phi + H$ and $C$. Under forward Euler the Jacobian of the map is $I + hJ_f$, whose infected block is $h\mathcal F + (I - h\mathcal V)$. The off-diagonal entries of $\mathcal V$ are nonpositive, so $I - h\mathcal V \ge 0$ once $h\mathcal V_{ii} \le 1$; its Perron root is $1 - h s$, with $s > 0$ the smallest real eigenvalue of $\mathcal V$, hence below $1$. The factors of $h$ then cancel in the next-generation matrix. In the example the incidence $\alpha S I/(1 + \delta T)$ has derivative zero in $T$ at the DFE, so treated individuals do not enter $\Phi$, and the next-generation matrix has the single nonzero entry $\alpha S_0/(\beta + d_1)$. The source states stability of the DFE as equivalent to $R_0 < 1$ without the step-size conditions; they are needed because an eigenvalue $1 - hc$ with large $hc$ can fall below $-1$ (flip instability of the numerical scheme).

## Sources

- D. Ghosh, P. K. Santra, G. S. Mahapatra, A. Elsonbaty and A. A. Elsadany, "A discrete-time epidemic model for the analysis of transmission of COVID19 based upon data of epidemiological parameters", *The European Physical Journal Special Topics* (2022), Eqs. (2)–(5), Theorem 1 and Theorem 3 with the subsection "Computations of basic reproduction number". <https://doi.org/10.1140/epjs/s11734-022-00537-2> (PMC8924950)
- L. J. S. Allen and P. van den Driessche, "The basic reproduction number in some discrete-time epidemic models", *Journal of Difference Equations and Applications* 14 (2008) 1127–1147, Theorem 2.1 (cited by the first source). <https://doi.org/10.1080/10236190802332308>
