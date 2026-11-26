# Threshold stability of the network SIRS model

**Setting.** Network SIRS model on populations $i\in\mathcal V$ with irreducible interaction matrix $W\ge 0$, recovery rates $\gamma_i>0$ and loss-of-immunity rates $\delta_i>0$:

$$\dot y=[\mathbf 1-y-z]\,W y-[\gamma]y,\qquad \dot z=[\gamma]y-[\delta]z,\qquad x=\mathbf 1-y-z ,$$

with $R_0=\rho([\gamma]^{-1}W)$ and (for $R_0>1$) unique endemic equilibrium $(x^\ast,y^\ast,z^\ast)$, $y^\ast>\mathbf 0$. Let $\bar v>\mathbf 0$ be the left Perron eigenvector of $[\gamma]^{-1}W$ and $V=\bar v^{\mathsf T}[\gamma]^{-1}y$.

**Lyapunov identity.** Along solutions,

$$\dot V=(R_0-1)\,\bar v^{\mathsf T}y-\bar v^{\mathsf T}[\gamma]^{-1}[y+z]\,Wy .$$

**Theorem.**
1. If $R_0\le 1$, the disease-free equilibrium $(\mathbf 1,\mathbf 0,\mathbf 0)$ is globally asymptotically stable on $\mathcal X$.
2. If $R_0>1$, the disease-free equilibrium is unstable and its region of attraction is exactly $\{y=\mathbf 0\}$.
3. If $R_0>1$, the endemic equilibrium is locally asymptotically stable: every eigenvalue $\lambda$ of the Jacobian there satisfies $\operatorname{Re}\lambda\le-\eta<0$, where $\eta=\min_i\min\{(Wy^\ast)_i,\delta_i\}$.
4. *(Rank-one interactions.)* If $W=ab^{\mathsf T}$ with $a,b>\mathbf 0$ and homogeneous recovery $\gamma=\bar\gamma\mathbf 1$, and $R_0=a^{\mathsf T}b/\bar\gamma>1$, then the endemic equilibrium attracts all of $\mathcal X\setminus\{y=\mathbf 0\}$.

For general irreducible $W$, global attraction of the endemic equilibrium on $\mathcal X\setminus\{y=\mathbf 0\}$ remains open; simulations support it.

## Expansion

For $R_0\le 1$ the identity gives $\dot V\le 0$ with $\{y=\mathbf 0\}$ the largest invariant set where $\dot V=0$; LaSalle gives $y\to\mathbf 0$, and then $z\to\mathbf 0$ by variation of constants. For $R_0>1$, if a trajectory with $y(0)\gneq\mathbf 0$ approached the disease-free state, eventually $y_i+z_i\le\varepsilon<(R_0-1)/R_0$ and $\dot V\ge(R_0-1-\varepsilon R_0)\bar v^{\mathsf T}y>0$, a contradiction. Local stability of the endemic state comes from the Schur complement $S(\lambda)=[x^\ast]W-[Wy^\ast]-[\gamma]-\lambda I-[\gamma]\,([\delta]+\lambda I)^{-1}[Wy^\ast]$, shown invertible for $\operatorname{Re}\lambda>-\eta$, which factors the characteristic polynomial as $(-1)^n\prod_i(\delta_i+\lambda)\det S(\lambda)$. The rank-one case uses the Lyapunov function $\sum_i\frac{b_i}{2x_i^\ast}(x_i-x_i^\ast)^2+\sum_i\frac{\delta_ib_i}{2\bar\gamma x_i^\ast}(z_i-z_i^\ast)^2+h-h^\ast+h^\ast\ln(h^\ast/h)$ with $h=b^{\mathsf T}y$.

## Depends on

- [Endemic equilibrium of the network SIRS model via a monotone fixed-point map](endemic-equilibrium-of-the-network-sirs-model-via-a-monotone-fixed-point-map.md)

## Sources

- Giulia Gatti and Giacomo Como, "On the dynamic behavior of the network SIRS epidemic model", arXiv:2604.21065 (2026), Lemmas 4–5, Theorems 2–3 and Proposition 2 (rank-one interaction matrices), <https://doi.org/10.48550/arXiv.2604.21065>.
