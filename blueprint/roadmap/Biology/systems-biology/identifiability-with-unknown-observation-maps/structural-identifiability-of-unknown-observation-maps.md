# Structural identifiability of unknown observation maps in biological ODE models

**Setting.** A mechanistic model $\dot{\vec X}=\vec F(\vec X;\vec p)$ is observed only through an unknown map, $Y=h(\vec X)$; for scalar observations of one state variable, $h$ is differentiable with nowhere-zero derivative (a strictly monotone reporter). Examples are a fluorescent reporter of a gene circuit and a wastewater signal of prevalence. The pair $(h,\vec p)$ is **structurally identifiable** if any two admissible pairs that produce the same output $Y(t)$ for every admissible initial condition coincide. It is **non-identifiable** if a different pair produces the same output.

**Proposition.**

1. (Decay) For $\dot X=-dX$, $Y=h(X)$, neither $d$ nor $h$ is identifiable: $(h_1,d_1)$ and $\big(h_1((x/k)^{d_1/d_2}),\,d_2\big)$ give identical outputs for all $d_2,k>0$.
2. (Known production) For $\dot X=1-dX$, both $d$ and $h$ are identifiable.
3. (Unknown production) For $\dot X=p-dX$, $d$ is identifiable but $p$ and $h$ are not: $(h_1,p_1)\sim(h_1(p_1x/p_2),p_2)$.
4. (General scalar models) For $\dot X=F(X;\vec p)$ on a known interval $\mathcal D$, with $Y=h(X)$:
   - if $F\neq0$ on $\mathcal D$ for every admissible $\vec p$ and no solution leaves $\mathcal D$ in finite backward time, then $h$ and $\vec p$ are non-identifiable;
   - if the monotonicity direction of $h$ is known, all steady states are simple, their number and eigenvalues determine $\vec p$, and some solution leaves $\mathcal D$ in finite backward time, then $\vec p$ and $h$ are globally identifiable.
5. (SIR with indirectly measured prevalence) For $\dot S=-\beta SI$, $\dot I=\beta SI-\gamma I$, $\dot R=\gamma I$, $Y=h(I)$, the recovery rate $\gamma$ is globally identifiable. The equivalent choices are exactly $\beta_2=\beta_1/c$, $h_2(x)=h_1(x/c)$, $c>0$. If the total population $N=S+I+R$ is known, then $\beta$, $\gamma$ and $h$ are all identifiable.
6. (Lotka–Volterra with indirectly measured predators) For $\dot N=rN-aNP$, $\dot P=NP-mP$, $Y=h(P)$, the rates $r$ and $m$ are identifiable, while $a$ and $h$ are determined only up to $a_2=a_1/c$, $h_2(x)=h_1(x/c)$.

## Expansion

Non-identifiability comes from symmetries: a state reparametrization $X\mapsto\varphi(X)$ that maps the model family to itself can be absorbed into the observation map, $h_2=h_1\circ\varphi^{-1}$. For pure decay, power maps $x\mapsto kx^{d_2/d_1}$ conjugate exponential decays with different rates, which is why a reporter's half-life cannot be separated from its unknown calibration curve. Steady states and their eigenvalues are invariant under smooth monotone reparametrization, so when they pin down $\vec p$ and the domain boundary is reached in finite backward time (fixing the range of $h$), the map is identifiable. For multivariable models the general method eliminates unobserved states by differential algebra to obtain input–output equations, and treats $h$ through its derivatives along trajectories. This determines which hybrid models, with a neural network as $h$, can learn the true observation map rather than an arbitrary reparametrized version.

## Sources

- Torkel E Loman, Alexander P Browning, Ruth E Baker, "Structural functional identifiability of unknown differential equation observation maps", arXiv:2611.22018 (2026), Section 3: Propositions 3.1–3.8 (production–degradation, general scalar, SIR and Lotka–Volterra models), <https://doi.org/10.48550/arXiv.2611.22018>.
