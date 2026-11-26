# Stable scaling regimes of the stochastic dual phosphorylation network

**Network.** A substrate with three phosphoforms $S_1,S_2,S_3$, a kinase $A$ and a phosphatase $B$ react by mass action:

$$A+S_1\underset{\alpha_1^-}{\overset{\alpha_1}{\rightleftharpoons}}AS_1\xrightarrow{\lambda_1}A+S_2,\qquad A+S_2\underset{\alpha_2^-}{\overset{\alpha_2}{\rightleftharpoons}}AS_2\xrightarrow{\lambda_2}A+S_3,$$

$$B+S_3\underset{\beta_1^-}{\overset{\beta_1}{\rightleftharpoons}}BS_3\xrightarrow{\mu_1}B+S_2,\qquad B+S_2\underset{\beta_2^-}{\overset{\beta_2}{\rightleftharpoons}}BS_2\xrightarrow{\mu_2}B+S_1 .$$

The state $V_N(t)\in\mathbb N^9$ counts copies of all nine species, a continuous-time Markov chain. Total substrate is $N$, and the totals $E_N$, $F_N$ of $A$ and $B$ satisfy $E_N/N\to e$, $F_N/N\to f$. Rates do not depend on $N$, so complex formation occurs at rate of order $N^2$.

**Regimes.** For a subset $H$ of species, the $H$-regime is stable if, whenever $V^H_N(0)$ stays bounded and $V^{H^c}_N(0)/N$ converges to any point of a nonempty open set, $V^H_N$ stays $O(1)$ and $V^{H^c}_N/N$ converges on a time interval to a deterministic trajectory while the occupation measure of $V^H_N$ converges to an averaging measure.

**Theorem (fewer enzymes than substrate, $e+f<1$).** Take $H=\{A,B\}$ (free enzymes) with initial scaled concentrations $(x_1^0,x_3^0,a_1^0,b_1^0)$ in the admissible region. Then $V^{H^c}_N(t)/N$ converges to the solution of

$$\dot x_1=\mu_2b_2+\alpha_1^-a_1-\alpha_1x_1m_A,\quad \dot x_3=\lambda_2a_2+\beta_1^-b_1-\beta_1x_3m_B,$$

$$\dot a_1=\alpha_1m_Ax_1-(\lambda_1+\alpha_1^-)a_1,\quad \dot b_1=\beta_1m_Bx_3-(\mu_1+\beta_1^-)b_1,$$

with $x_2=1-e-f-x_1-x_3$, $a_2=e-a_1$, $b_2=f-b_1$ and

$$m_A=\frac{(\lambda_1+\alpha_1^-)a_1+(\lambda_2+\alpha_2^-)a_2}{\alpha_1x_1+\alpha_2x_2},\qquad m_B=\frac{(\mu_1+\beta_1^-)b_1+(\mu_2+\beta_2^-)b_2}{\beta_1x_3+\beta_2x_2},$$

while the free enzyme counts are asymptotically independent Poisson with means $m_A(t)$, $m_B(t)$. If $(\mu_1f-\lambda_2e)(\lambda_1e-\mu_2f)>0$ this system has a unique equilibrium with

$$a_1^*=\mu_2\frac{\mu_1f-\lambda_2e}{\lambda_1\mu_1-\lambda_2\mu_2},\qquad b_1^*=\lambda_2\frac{\lambda_1e-\mu_2f}{\lambda_1\mu_1-\lambda_2\mu_2}.$$

When the backward rates $\alpha_i^-,\beta_i^-$ all equal a common $c\in\{0,1\}$, this equilibrium is stable if $\mu_1f>\lambda_2e$ and $\lambda_1e>\mu_2f$ and unstable if both inequalities are reversed; in the first case the regime $H=\{A,B\}$ is stable. If instead $\lambda_1e<\mu_2f$, the regime $H=\{S_2,S_3,A,AS_2,BS_3\}$ is stable: the substrate accumulates in the unphosphorylated form.

**More enzymes than substrate ($e+f>1$).** The free substrate forms $S_1,S_2,S_3$ are $O(1)$ and the complexes and free enzymes scale with $N$; an equilibrium of the limiting system exists (and is then unique, when $\lambda_1\mu_1>\lambda_2\mu_2$) iff $e>\mu_2/(\lambda_1+\mu_2)$ and $f>\lambda_2/(\lambda_2+\mu_1)$, up to boundary cases.

## Expansion

When a species is $O(1)$ but its consumption and production rates are of order $N$, it relaxes on a time scale $1/N$; conditioned on the slow variables it behaves as an $M/M/\infty$ queue (or a small network of them) with Poisson invariant law, and the slow variables see only its stationary mean. This stochastic averaging principle replaces the quasi-steady-state approximation: $m_A$ is the mean free kinase level that balances complex formation against complex break-up. Stability of the equilibrium follows from the Routh–Hurwitz criterion applied to the quartic characteristic polynomial of the four-dimensional limit.

## Sources

- L. Laurence, P. Robert, "Thermodynamic Limits of Stochastic Chemical Reaction Networks with Phosphorylation", arXiv:2606.30325 (2026), network (CRN), Proposition 6, Theorems 7 and 9, Corollaries 8 and 13, Propositions 10–12, Theorem 14, Proposition 16, <https://doi.org/10.48550/arXiv.2606.30325>.
