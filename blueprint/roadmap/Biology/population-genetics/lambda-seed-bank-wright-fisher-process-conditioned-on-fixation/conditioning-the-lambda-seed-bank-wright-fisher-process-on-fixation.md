# Conditioning the Λ-seed-bank Wright–Fisher process on fixation

**Model.** Let $\Lambda = a\,\delta_0 + \Lambda_0$ be a finite measure on $[0,1]$ with $\Lambda_0(\{0\}) = 0$ and $\int_0^1 y^{-2}\Lambda(dy) < \infty$, encoding Kingman-type resampling (weight $a$) and multiple-merger reproduction events of size $r$ (rate $r^{-2}\Lambda_0(dr)$). Let $\alpha, \sigma \ge 0$ be the deactivation and activation rates of a seed bank. The **Λ-seed-bank Wright–Fisher process** $\mathbf{Z} = (Z_1, Z_2, Z_3)$ on

$$D = \{\mathbf{z} \in [0,1]^3 : z_1 \le z_3,\ z_2 \le 1 - z_3\}$$

records the active mass of a focal type $\heartsuit$ ($Z_1$), its dormant mass ($Z_2$) and the total active mass ($Z_3$). It is the unique strong solution of

$$\begin{aligned}
dZ_1 &= (\sigma Z_2 - \alpha Z_1)\,dt + \sqrt{a Z_1 (Z_3 - Z_1)}\,dB_t \\
&\quad + \int_0^1\!\!\int_0^1 r\Big[(Z_3 - Z_1)\mathbb{1}_{\{u \le Z_1/Z_3\}} - Z_1 \mathbb{1}_{\{u > Z_1/Z_3\}}\Big]\,\widetilde{N}(dt,dr,du),\\
dZ_2 &= (\alpha Z_1 - \sigma Z_2)\,dt, \qquad dZ_3 = \big(\sigma(1 - Z_3) - \alpha Z_3\big)\,dt,
\end{aligned}$$

with $\widetilde N$ a compensated Poisson random measure of intensity $dt \otimes r^{-2}\Lambda_0(dr) \otimes du$ (all coefficients evaluated at left limits). Fixation of $\heartsuit$ is the event $\lim_{s \to \infty}(Z_1(s) + Z_2(s)) = 1$.

A **$(\Lambda, \xi, \mathrm{M})$-seed-bank Wright–Fisher process** adds to the $Z_1$ equation coordinated mutations toward $\heartsuit$ that act only while a switching environment $\xi_t \in \{0,1\}$ equals $1$: a drift $b\,\xi_t (Z_3 - Z_1)\,dt$ and jumps converting a fraction $r$ of the non-$\heartsuit$ active mass, $r\,\xi_{t-}(Z_3 - Z_1)$, driven by a mutation measure $\mathrm{M} = b\,\delta_0 + \mathrm{M}_0$.

**Theorem.** Let $\widetilde{\mathbf{Z}}$ be the Λ-seed-bank Wright–Fisher process conditioned on fixation of $\heartsuit$. Then there is a continuous-time Markov chain $\xi$ on $\{0,1\}$ with rates $q_{01} = \alpha$, $q_{10} = \sigma$ such that $\widetilde{\mathbf{Z}}$ has the law of the $(\Lambda, \xi, \mathrm{M})$-seed-bank Wright–Fisher process with

$$\mathrm{M}(\{0\}) = a, \qquad \mathrm{M}_0(dy) = y^{-1}\Lambda_0(dy).$$

## Expansion

In the lookdown construction of the $N$-particle Moran model with seed bank, fixation of $\heartsuit$ is (up to a null set) the event that the level-one particle carries $\heartsuit$ at time $0$. Conditioning on it, the remaining $N-1$ levels form again a seed-bank lookdown model, in which every reproduction event involving level one converts the participating particles to $\heartsuit$. That acts as a mutation toward $\heartsuit$ at rate $a$ (pairwise events) and $y^{-1}\Lambda_0(dy)$ (the extra factor $y$ is the probability that level one participates); it operates only while the level-one lineage is in the active compartment, which switches like a single seed-bank lineage with rates $\alpha$ and $\sigma$. Exchangeability, sampling duality with the structured ancestral process and tightness pass this to the $N \to \infty$ limit. The genealogy of the conditioned process is the corresponding structured Λ-coalescent with coordinated mutations.

## Sources

- María Clara Fittipaldi, Adrián González Casanova and Julio Ernesto Nava Trejo, "Λ-Seed-Bank-Wright-Fisher process conditioned on fixation", arXiv:2511.20483 (2025), Theorems 1, 4 and 5, Proposition 1, Lemmas 8–9, <https://doi.org/10.48550/arXiv.2511.20483>.
