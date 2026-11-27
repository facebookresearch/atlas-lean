# Reproduction number of the two-patch commuter SIR model

**Model.** Two patches $i\in\{1,2\}$ (with $j$ the other patch) have home populations $N_i$, split into permanent residents $N_{ir}$ and commuters $N_{ic}=N_{ii}+N_{ij}$, of whom $N_{ii}$ are currently at home and $N_{ij}$ in patch $j$. Commuters of patch $i$ leave at rate $\lambda_i$ and return at rate $\mu_i$, and these subpopulations are at their balance $N_{ii}=\frac{\mu_i}{\lambda_i+\mu_i}N_{ic}$, $N_{ij}=\frac{\lambda_i}{\lambda_i+\mu_i}N_{ic}$. The population present in patch $i$ is $N_{ip}=N_{ir}+N_{ii}+N_{ji}$. Each group $g\in\{ir,ii,ij\}$ has SIR compartments; transmission in patch $i$ is frequency dependent with rate $\beta_i$ and the recovery rate $\gamma$ is common, e.g.

$$\dot S_{ii}=-\beta_iS_{ii}\frac{I_{ir}+I_{ii}+I_{ji}}{N_{ip}}-\lambda_iS_{ii}+\mu_iS_{ij},\qquad \dot I_{ij}=\beta_jS_{ij}\frac{I_{jr}+I_{jj}+I_{ij}}{N_{jp}}-\gamma I_{ij}+\lambda_iI_{ii}-\mu_iI_{ij},$$

and residents do not move. Let $\mathcal R_i=\beta_i/\gamma$ be the reproduction number of isolated patch $i$.

**Proposition (explicit threshold).** Define

$$q_{11}=\mathcal R_1\Big(\frac{N_{1r}}{N_{1p}}+\frac{N_{11}}{N_{1p}}\frac{\gamma+\mu_1}{\gamma+\lambda_1+\mu_1}+\frac{N_{21}}{N_{1p}}\frac{\gamma+\lambda_2}{\gamma+\lambda_2+\mu_2}\Big),\qquad q_{21}=\mathcal R_1\Big(\frac{N_{11}}{N_{1p}}\frac{\lambda_1}{\gamma+\lambda_1+\mu_1}+\frac{N_{21}}{N_{1p}}\frac{\mu_2}{\gamma+\lambda_2+\mu_2}\Big),$$

and $q_{22},q_{12}$ by exchanging the indices $1$ and $2$, and

$$\mathcal R_{1,2}=\frac{q_{11}+q_{22}+\sqrt{(q_{22}-q_{11})^2+4q_{12}q_{21}}}{2}.$$

Then: if $\mathcal R_{1,2}>1$ the disease-free equilibrium is unstable; if $\mathcal R_{1,2}<1$ it is exponentially stable with respect to the infected variables; and if $\mathcal R_1=\mathcal R_2=\mathcal R$ then $\mathcal R_{1,2}=\mathcal R$.

**Corollary (bounds).** $\min(\mathcal R_1,\mathcal R_2)\le\mathcal R_{1,2}\le\max(\mathcal R_1,\mathcal R_2)$.

**Corollary (convex-combination form).** If $\mathcal R_2>\mathcal R_1$, then $\mathcal R_{1,2}=\alpha\mathcal R_1+(1-\alpha)\mathcal R_2$, where $\alpha\in[0,1)$ is the smallest root of

$$P(\alpha)=\alpha^2(\mathcal R_2-\mathcal R_1)-\alpha(\mathcal R_2-\mathcal R_1+q_{12}+q_{21})+q_{12}.$$

## Depends on

- [Basic reproduction number of the next-generation matrix](../../next-generation-matrix-and-the-basic-reproductio/r0.md)

## Expansion

The next-generation matrix $FV^{-1}$ of the six infected groups has rank two (one dimension per patch), so its spectral radius is the Perron root of a $2\times2$ matrix $(q_{kl})$; $q_{kl}$ is the expected number of infections caused in the population present in patch $k$ by infections generated in patch $l$, obtained from the mean residence times $\frac{\gamma+\mu}{\gamma+\lambda+\mu}$ and $\frac{\lambda}{\gamma+\lambda+\mu}$ of an infected commuter at home and away. The formula for $\mathcal R_{1,2}$ is the larger root of its characteristic polynomial. When $\mathcal R_1=\mathcal R_2$, the all-ones vector is a positive eigenvector of the transpose with eigenvalue $\mathcal R$, and Perron–Frobenius gives $\mathcal R_{1,2}=\mathcal R$. The bounds follow from monotonicity of the spectral radius of nonnegative matrices, $M(\mathcal R_-,\mathcal R_-)\le M(\mathcal R_1,\mathcal R_2)\le M(\mathcal R_+,\mathcal R_+)$. Since the column sums satisfy $q_{11}+q_{21}=\mathcal R_1$ and $q_{22}+q_{12}=\mathcal R_2$, eliminating the eigenvalue gives the quadratic $P$, with $P(0)=q_{12}\ge0$ and $P(1)=-q_{21}\le0$, so its root in $[0,1)$ is the weight $\alpha$. The formula also covers the case without permanent residents.

## Sources

- Alain Rapaport, Ismail Mimouni, "The Role of Permanently Resident Populations in the Two-Patches SIR Model with Commuters", Bulletin of Mathematical Biology 85 (2023), 3, <https://doi.org/10.1007/s11538-022-01111-6>. Published version of arXiv:2211.16137, cited next; locators there refer to the arXiv version.
- A. Rapaport and I. Mimouni, "The role of permanently resident populations in the two-patches SIR model with commuters", arXiv:2211.16137 (2022), Section 2 (model), Section 3 (Proposition 1, Corollaries 2 and 3), <https://doi.org/10.48550/arXiv.2211.16137>.
