# H-infinity attenuation level of extrinsic noise in regulatory networks

**Model.** A regulatory network with intrinsic multiplicative noise and an extrinsic input $\upsilon(t)$ (environmental signal or noise) is

$$dx = (Nx + H\upsilon)\,dt + Mx\,d\omega, \qquad Z = Cx,$$

where $H$ couples the input to the genes and $C$ selects the observed genes ($C = e_i^{\mathsf T}$ for gene $i$, $C = I$ for the whole network); the nonlinear version has $N(x)$, $H(x)$, $M(x)$. With $\|\upsilon\|_2^2 = \mathbb{E}\int_0^\infty \upsilon^{\mathsf T}\upsilon\,dt$, the network has attenuation level $\rho$ from $\upsilon$ to $Z$ if, for $x(0) = 0$, $\|Z\|_2 \le \rho\,\|\upsilon\|_2$ for all $\upsilon \in L^2$ (with an initial-state term $\mathbb{E}\,V(x(0))$ added to the right-hand side, $\|Z\|_2^2 \le \mathbb{E}\,V(x(0)) + \rho^2\|\upsilon\|_2^2$, otherwise). With $\rho_o$ the smallest attenuation level, the input is attenuated at $Z$ if $\rho_o < 1$ and amplified if $\rho_o > 1$.

**Theorem 3 (linear network).** The attenuation level $\rho$ is guaranteed if some $P = P^{\mathsf T} > 0$ satisfies

$$PN + N^{\mathsf T}P + M^{\mathsf T}PM + C^{\mathsf T}C + \frac{1}{\rho^2}PHH^{\mathsf T}P \le 0,$$

equivalently, by the Schur complement, the LMI

$$\begin{pmatrix} PN + N^{\mathsf T}P + M^{\mathsf T}PM + C^{\mathsf T}C & PH \\ (PH)^{\mathsf T} & -\rho^2 I \end{pmatrix} \le 0 .$$

The optimal level is $\rho_o = \min\rho$ over $\rho > 0$, $P > 0$ satisfying this LMI.

**Theorem 4 (nonlinear network).** The attenuation level $\rho$ is guaranteed if some $C^2$ function $V$ with $V(x) > 0$ for $x \ne 0$ and $V(0) = 0$ satisfies the Hamilton–Jacobi inequality

$$x^{\mathsf T}C^{\mathsf T}Cx + \Big(\frac{\partial V}{\partial x}\Big)^{\mathsf T}N(x) + \frac12M(x)^{\mathsf T}\frac{\partial^2V}{\partial x^2}M(x) + \frac{1}{4\rho^2}\Big(\frac{\partial V}{\partial x}\Big)^{\mathsf T}H(x)H(x)^{\mathsf T}\frac{\partial V}{\partial x} \le 0 .$$

Under a polytopic global linearization with vertices $(N_i, H_i, M_i)$, $\rho_o$ is approximated by the smallest $\rho$ for which one $P > 0$ satisfies the LMI of Theorem 3 at every vertex.

## Depends on

- [Stability in probability of regulatory networks with multiplicative noise](stability-in-probability-of-regulatory-networks-with-multiplicative-noise.md)

## Expansion

With $V = x^{\mathsf T}Px$, Itô's formula gives $\mathcal LV = x^{\mathsf T}(PN + N^{\mathsf T}P + M^{\mathsf T}PM)x + 2x^{\mathsf T}PH\upsilon$. Completing the square,

$$Z^{\mathsf T}Z - \rho^2\upsilon^{\mathsf T}\upsilon + \mathcal LV = x^{\mathsf T}\Big(PN + N^{\mathsf T}P + M^{\mathsf T}PM + C^{\mathsf T}C + \tfrac{1}{\rho^2}PHH^{\mathsf T}P\Big)x - \big\|\rho\upsilon - \rho^{-1}H^{\mathsf T}Px\big\|^2,$$

so the matrix inequality gives $\mathbb{E}\int_0^\infty(Z^{\mathsf T}Z - \rho^2\upsilon^{\mathsf T}\upsilon)\,dt \le \mathbb{E}\,V(x(0))$, which is the attenuation bound. Solving the LMI gene by gene ($C = e_i^{\mathsf T}$) ranks genes by their sensitivity to environmental noise; genes with $\rho_o > 1$ form the weak structure of the network.

## Sources

- B.-S. Chen and Y.-C. Wang, "On the attenuation and amplification of molecular noise in genetic regulatory networks", BMC Bioinformatics 7 (2006) 52, Eqs. (11)–(21), Theorems 3–4 and Remarks 3–4, <https://doi.org/10.1186/1471-2105-7-52>, PMCID PMC1435772.
