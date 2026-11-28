# ODE approximation of death-birth fixation probabilities on the star graph

**Model.** Two types live on the vertices of a star graph (one centre joined to every leaf, leaves joined only to the centre): residents $A$ and mutants $B$. Under weak selection the birth and death fitnesses of $B$ relative to $A$ are

$$\varphi_i(x) = 1 + \frac{\psi_i(x)}{N}, \qquad i = 1 \text{ (birth)},\ i = 2 \text{ (death)},$$

where $x$ is the mutant frequency and $\psi_1, \psi_2 \in C^\infty([0,1], \mathbb R)$ may be frequency dependent. In the death-birth (DB) process a vertex is chosen to die with probability proportional to its death fitness, and one of its neighbours, chosen with probability proportional to birth fitness, places an offspring there. The state is the type of the centre together with the fraction $x \in \{0, \bar z, 2\bar z, \dots, 1 - \bar z\}$ of mutant leaves, $\bar z = 1/N$. Write $p^N_{1,x}$ (resp. $p^N_{2,x}$) for the probability that $B$ fixes when the centre is a mutant (resp. a resident). One-step analysis gives the $2N$ linear equations

$$p^N_{1,x} = a_x(\bar z)\, p^N_{2,x} + b_x(\bar z)\, p^N_{1,x+\bar z}, \qquad p^N_{2,x} = c_x(\bar z)\, p^N_{2,x-\bar z} + d_x(\bar z)\, p^N_{1,x},$$

with $p^N_{2,0} = 0$, $p^N_{1,1-\bar z} = 1$ and explicit smooth coefficients $a_x, b_x, c_x, d_x$ (the jump chain conditioned on moving).

**Continuum candidate.** Let

$$f_1(x) = \frac{x+1}{2 - \bar z}, \qquad f_2(x) = \frac{x}{2 - \bar z},$$

the solution of the first-order system $f_2 - f_1 + f_1' = 0$, $f_1 - f_2 - f_2' = 0$ with $f_1(1-\bar z) = 1$, $f_2(0) = 0$, and let $(g_1, g_2)$ solve the second-order corrector system

$$g_2 + g_1' - g_1 = \frac{1 - x\psi_1(x) + \psi_2(x)}{2 - \bar z}, \qquad g_1 - g_2' - g_2 = \frac{(x-1)\psi_1(x) + \psi_2(x) - 1}{2 - \bar z},$$

with $g_1(1 - \bar z) = 0$, $g_2(0) = 0$ (it has an explicit solution by quadrature). Let $\overline{\mathbf F}$ be the vector with entries $f_2(x) + \bar z\, g_2(x)$ (resident centre) and $f_1(x) + \bar z\, g_1(x)$ (mutant centre) on the grid, and $\mathbf F$ the vector of exact fixation probabilities.

**Theorem.** There is a constant $C$, independent of $N$, such that

$$\bigl\|\mathbf F - \overline{\mathbf F}\bigr\|_\infty \le \frac{C}{N}.$$

So, to leading order, a single mutant placed at the centre fixes with probability close to $1/2$, and one placed on a leaf with probability of order $1/(2N)$, whatever the frequency-dependent weak-selection fitnesses.

**Amplification threshold.** Let the lone initial mutant sit at the centre with probability $\rho_N$ and on a uniformly chosen leaf otherwise, and compare its fixation probability with that of a single mutant on the complete graph, which is $\mathcal J(1/N)/\mathcal J(1) + O(N^{-1})$ with $\mathcal J(s) = \int_0^s \exp\bigl(\int_0^y (\psi_2 - \psi_1)\,du\bigr) dy$. Suppose $B$ is favoured on the complete graph and $N\rho_N \to \alpha \in [0, \infty]$. Then there is a finite $C_\star > 0$ such that under DB updating the star amplifies selection if $\alpha > C_\star$, suppresses it if $\alpha < C_\star$, and preserves the invasion probability asymptotically if $\alpha = C_\star$. In particular, any $\rho_N$ decaying more slowly than $1/N$ makes the star an amplifier, while uniform placement ($\rho_N = 1/N$) makes it a suppressor whenever $C_\star > 1$.

## Depends on

- [Moran fixation probability](../../../../population-genetics/moran-model/moran-fixation.md)

## Proof sketch

Substituting smooth functions $q_1(x, z), q_2(x, z)$ into the recursion and Taylor expanding in $z = \bar z$, the constant terms cancel; the first-order coefficients give the system for $(f_1, f_2)$ and the second-order ones the forced system for $(g_1, g_2)$. For the error, write the recursion as $\mathbf M \mathbf F = 0$ with $\mathbf M = \mathbf L - \mathbf I$ and restrict to the interior unknowns. The residual of the candidate is $O(\bar z^2)$ in sup norm, while the reduced matrix $\widetilde{\mathbf M}$ has non-positive off-diagonal entries and admits a positive vector $\mathbf r$ with $\widetilde{\mathbf M}\mathbf r$ bounded below, so the M-matrix bound $\|\mathbf K^{-1}\| \le \|\mathbf r\| / \min_i (\mathbf K\mathbf r)_i$ gives $\|\widetilde{\mathbf M}^{-1}\| \le C/\bar z$. Multiplying the two bounds gives the $O(\bar z)$ error. The threshold statement follows by inserting the centre and leaf asymptotics into the ratio of invasion probabilities; the exact value of $C_\star$ depends on the next-order leaf error, conjectured to vanish, which would give $C_\star = (2 - \mathcal J(1))/\mathcal J(1)$.

## Sources

- Poly H. da Silva and Max O. Souza, "Continuous approximations for the fixation probability of the Moran processes on star graphs", *Journal of Mathematical Biology* 92 (2026), 11, <https://doi.org/10.1007/s00285-025-02309-7>. Preprint version: arXiv:2209.04572 (2022), Section 3.1 and Theorem 1 (proof via Propositions 2-5 and Lemmas 1-3 of the appendix), Proposition 1, Definition 1 and Theorem 2 (Section 5), <https://doi.org/10.48550/arXiv.2209.04572>.
