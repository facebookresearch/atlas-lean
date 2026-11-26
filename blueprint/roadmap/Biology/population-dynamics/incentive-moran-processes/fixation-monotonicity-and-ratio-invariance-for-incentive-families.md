# Fixation monotonicity and ratio invariance for incentive families

**Setting.** In the incentive process on $\{0,\dots,N\}$ (incentive-proportional birth, uniform death), with positive incentives $\varphi_A,\varphi_B$, let $\rho_A$ be the fixation probability of a single $A$ mutant and $\rho_B$ that of a single $B$ mutant. From any incentive $\varphi$ build the one-parameter family

$$\psi_{A,q}(i)=i^{\,q}\,\varphi_A(i),\qquad \psi_{B,q}(i)=(N-i)^{q}\,\varphi_B(i),\qquad q\in\mathbb{R},$$

and write $\rho_{A,q},\rho_{B,q}$ for its fixation probabilities. Starting from the projection incentive $\varphi_T=f_T$ this produces the $q$-replicator family $x_T^{\,q}f_T$, and from the logit incentive it produces the $q$-Fermi family; $q=1$ in the first case is the Moran process.

**Theorem (monotonicity).** For $N>2$ and $p<q$,

$$\rho_{A,p}>\rho_{A,q}.$$

**Theorem (ratio invariance).** The ratio $\rho_{B,q}/\rho_{A,q}$ does not depend on $q$:

$$\frac{\rho_{B,q}}{\rho_{A,q}}=\prod_{k=1}^{N-1}\frac{\varphi_B(k)}{\varphi_A(k)}\cdot\prod_{k=1}^{N-1}\frac{k}{N-k}\quad\text{for every }q .$$

**Consequences.**

- Fixation of a single $A$ mutant is strictly more likely under the projection incentive than under the replicator (Moran) incentive, which in turn beats the $2$-replicator, and so on; closed forms at $q=1$ and $q=2$ give explicit bounds for intermediate $q$. Unlike the deterministic incentive dynamics, whose long-run outcome on the Moran landscape is the same for every incentive, the stochastic process depends on $q$.
- On the Moran landscape ($f_A=r$, $f_B=1$) the ratio equals the Moran value $r^{1-N}$ for every $q$-replicator incentive, so, for example, the $2$-replicator has $\rho_B=(1+r)^{1-N}$. For every $q$-Fermi incentive,

$$\log\frac{\rho_A}{\rho_B}=\beta\,(r-1)\,(N-1),$$

so larger populations and stronger selection both favor the fitter type.
- In the small-mutation limit the stationary weight of the all-$B$ state, $1/(1+\rho_B/\rho_A)$, is the same for all $q$, and the Mustonen–Lässig fitness-flux form of Fisher's fundamental theorem for the Moran process carries over to these families.

## Expansion

Fixation probabilities are $\rho_A=1/\sum_{j=0}^{N-1}t_j$ and $\rho_B=t_{N-1}/\sum_{j=0}^{N-1}t_j$ with $t_j=\prod_{k=1}^{j}\frac{k\varphi_B(k)}{(N-k)\varphi_A(k)}$. Replacing $\varphi$ by $\psi_q$ multiplies $t_j$ by $\prod_{k=1}^{j}\big(\frac{N-k}{k}\big)^{q}=\binom{N-1}{j}^{q}$. The factor is $1$ at $j=0$ and $j=N-1$, and exceeds $1$ for $1\le j\le N-2$, a nonempty range when $N>2$; so the interior terms strictly increase with $q$, the denominator grows and $\rho_{A,q}$ strictly decreases. For the ratio, $\rho_B/\rho_A=t_{N-1}$, and the extra factor at $j=N-1$ is $\binom{N-1}{N-1}^{q}=1$, so the ratio is unchanged. For the $q$-Fermi family on the Moran landscape the common normalizing denominators cancel in $\varphi_B/\varphi_A$, leaving $\prod_k e^{\beta(f_B-f_A)}=e^{-\beta(r-1)(N-1)}$ after the binomial factors cancel.

## Depends on

- [Fixation probabilities of the incentive process](fixation-probabilities-of-the-incentive-process.md)

## Sources

- Marc Harper, Dashiell Fryer, "Incentive Processes in Finite Populations", arXiv:1306.2389 (2013): Theorem 1 (monotonicity in $q$), Theorem 2 (ratio invariance), Sections 3.2–3.4 (consequences for $q$-Fermi, stationary distributions and the fitness-flux theorem). <https://doi.org/10.48550/arXiv.1306.2389>
