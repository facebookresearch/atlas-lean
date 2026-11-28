# Pseudo-first-order master equation under ligand excess

**Setting.** Partition the monomer microstates of an RNA into macrostates $\alpha_1,\dots,\alpha_n$ and the ligand-bound (dimer) microstates into macrostates $\beta_1,\dots,\beta_m$, with macrorates $r(\cdot\to\cdot)$ as in [Macrorates of a ligand-coupled RNA folding landscape](macrorates-of-a-ligand-coupled-rna-folding-landscape.md). The reactions are conformational change $R_i\to R_j$ and $LR_i\to LR_j$ (first order), dissociation $LR_i\to L+R_i$ (first order) and association $L+R_i\to LR_i$ (second order, rate proportional to $[L][\alpha_i]$).

**Ligand-excess assumption.** The free ligand concentration $[L]$ is constant in time, equal to its initial value $l_0$.

**Proposition.** Under ligand excess the vector of macrostate concentrations $\gamma=([\alpha_1],\dots,[\alpha_n],[\beta_1],\dots,[\beta_m])^{\top}$ satisfies the linear system

$$\frac{d\gamma}{dt}=\mathbf R(l_0)\,\gamma,\qquad \mathbf R(l_0)=\begin{pmatrix}\mathbf A & \mathbf C\\ l_0\,\mathbf D & \mathbf B\end{pmatrix},$$

where $a_{ij}=r(\alpha_j\to\alpha_i)$, $b_{ij}=r(\beta_j\to\beta_i)$, $c_{ij}=r(\beta_j\to\alpha_i)$, $d_{ij}=r(\alpha_j\to\beta_i)$ for $i\ne j$ (all entries of $\mathbf C,\mathbf D$), and the diagonals are

$$a_{ii}=-\sum_{k\ne i}r(\alpha_i\to\alpha_k)-l_0\sum_{k}r(\alpha_i\to\beta_k),\qquad b_{jj}=-\sum_{k}r(\beta_j\to\alpha_k)-\sum_{k\ne j}r(\beta_j\to\beta_k).$$

Every column of $\mathbf R(l_0)$ sums to zero, so total RNA is conserved, and the solution is $\gamma(t)=\exp(t\,\mathbf R(l_0))\,\gamma(0)$.

**Effective dissociation constant.** If the binding energy is calibrated from the measured dissociation constant $K_d^{A}$ of the isolated aptamer at temperature $T_A$ as $\theta=RT_A\ln\!\big(K_d^{A}\,\Pr[\text{pocket}\mid A,T_A]\big)$, then a longer riboswitch $RS$ that contains the aptamer has effective dissociation constant at temperature $T_R$

$$K_d^{RS}=\frac{\exp(\theta/(RT_R))}{\Pr[\text{pocket}\mid RS,T_R]}=\frac{\big(K_d^{A}\Pr[\text{pocket}\mid A,T_A]\big)^{T_A/T_R}}{\Pr[\text{pocket}\mid RS,T_R]},$$

where $\Pr[\text{pocket}\mid\cdot]$ is the equilibrium probability of the binding-pocket structure.

## Depends on

- [Macrorates of a ligand-coupled RNA folding landscape](macrorates-of-a-ligand-coupled-rna-folding-landscape.md)

## Expansion

Without the assumption the association flux $r(\alpha_i\to\beta_j)[L][\alpha_i]$ is bilinear and the system is nonlinear; fixing $[L]=l_0$ turns it into a first-order flux with rate $l_0\,r(\alpha_i\to\beta_j)$, so the full process is a continuous-time Markov chain on $n+m$ macrostates. Only the off-diagonal block $\mathbf D$ and the diagonal of $\mathbf A$ scale with $l_0$, so the expensive enumeration and basin computations are done once and the matrix is re-assembled for each ligand concentration; diagonalising it gives the time-dependent macrostate occupancies. The dissociation-constant relation follows because only pocket-containing structures bind: the apparent constant is the microscopic constant $e^{\theta/RT}$ divided by the fraction of RNA presenting the pocket.

## Sources

- Kühnl F, Stadler PF, Will S, "Tractable RNA-ligand interaction kinetics" (2017), Results ("A tractable model under ligand excess", the ODE system and the block matrix $\mathbf R(l_0)$) and Methods ("Parameters from empirical measurements"), <https://doi.org/10.1186/s12859-017-1823-5>, PMCID PMC5657077.
