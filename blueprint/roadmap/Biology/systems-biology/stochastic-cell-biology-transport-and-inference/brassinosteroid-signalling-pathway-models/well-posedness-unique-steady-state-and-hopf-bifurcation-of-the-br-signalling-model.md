# Well-posedness, unique steady state and Hopf bifurcation of a brassinosteroid signalling model

**Model.** The plant hormone brassinosteroid (BR) binds the receptor BRI1 and displaces the inhibitor BKI1; free BKI1 promotes dephosphorylation of the transcription factor BZR, and dephosphorylated BZR represses BR biosynthesis. With conserved totals of BKI1, BRI1 and BZR, the nondimensional state is $b$ (BR), $k$ (free BKI1, as a fraction of total) and $z$ (dephosphorylated BZR, as a fraction of total):

$$\begin{aligned} \frac{db}{dt}&=\beta_k(\kappa-1+k)k-\beta_b(1-k)b+\frac{1}{1+(\theta_bz)^{h_b}}-b,\\ \frac{dk}{dt}&=\frac1\epsilon\Big(\beta_b(1-k)b-\beta_k(\kappa-1+k)k\Big),\\ \frac{dz}{dt}&=\delta_z(1-z)k-\rho_z\frac{z}{1+(\theta_zk)^{h_z}}, \end{aligned}$$

with $\kappa\ge1$ (ratio of receptor to BKI1 totals), positive rate constants $\beta_k,\beta_b,\theta_b,\epsilon,\delta_z,\rho_z,\theta_z$ and integer Hill exponents $h_b,h_z$. The first term of $db/dt$ and $dk/dt$ is release of BR when BKI1 rebinds the receptor, the second is BR binding; the Hill term is BZR-repressed synthesis.

**Theorem (well-posedness).** For every parameter set and every initial value in $M=[0,1+\beta_k\kappa]\times[0,1]^2$ there is a unique global $C^1$ solution, and $M$ is positively invariant.

**Theorem (unique steady state).** For every parameter set the system has exactly one steady state $(b^*,k^*,z^*)\in M$.

**Theorem (Hopf bifurcation).** The linearization at the steady state has a cubic characteristic polynomial $\lambda^3+a_2\lambda^2+a_1\lambda+a_0$; as the BZR phosphorylation parameters $\delta_z$ and $\rho_z$ vary, the Routh–Hurwitz quantity $a_2a_1-a_0$ changes sign and the system undergoes a Hopf bifurcation. Oscillations occur only for relatively large $\delta_z,\rho_z$ (fast BZR phosphorylation cycling); for the fitted wild-type parameters the steady state is stable, consistent with BR homeostasis.

## Expansion

Invariance of $M$ follows by checking the vector field on each face: at $k=0$ the $k$-equation reduces to $\beta_bb/\epsilon\ge0$, at $k=1$ to $-\beta_k\kappa/\epsilon\le0$, similarly for $z$, and at $b=1+\beta_k\kappa$ the production terms are dominated by decay. At a steady state the $k$-equation forces binding and release to balance, so the $b$-equation reduces to $b=1/(1+(\theta_bz)^{h_b})$, a decreasing function of $z$; the $z$-equation gives $z$ as an increasing function of $k$, and the binding balance gives $k$ as an increasing function of $b$. A decreasing function composed with increasing ones has exactly one fixed point, which is the unique steady state. The negative feedback loop BR $\to$ BKI1 release $\to$ BZR dephosphorylation $\to$ repressed BR synthesis is the classical Goodwin-type architecture that can oscillate when the loop gain and delay (here, BZR cycling speed) are large. A PDE–ODE extension with BR diffusion in the cytoplasm and receptor kinetics on the membrane, and a crosstalk model with gibberellin signalling via DELLA–BZR interaction, are also formulated.

## Sources

- Henry R. Allen, Mariya Ptashnyk, "Mathematical modelling and analysis of the brassinosteroid and gibberellin signalling pathways and their interactions", Journal of Theoretical Biology 432 (2017), 109–131, <https://doi.org/10.1016/j.jtbi.2017.08.013>. Published version of arXiv:1703.07584, cited next; locators there refer to the arXiv version.
- Henry R. Allen, Mariya Ptashnyk, "Mathematical Modelling and Analysis of the Brassinosteroid and Gibberellin Signalling Pathways and their Interactions", arXiv:1703.07584 (2017): reduced model (Section 3) and its nondimensional form (Section 4), Theorem 1 (well-posedness, Appendix 2.1), Theorem 2 (unique steady state, Appendix 2.2), Theorem 3 and Section 4.1 (linearized stability and Hopf bifurcation), Sections 5–6 (spatial and crosstalk models). <https://doi.org/10.48550/arXiv.1703.07584>
