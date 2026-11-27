# Quorum-switching Filippov model of colony emigration

**Model.** A social-insect colony of size $N$ moves to a new nest. A fraction $\rho$ of the workers is active, divided into searchers $S$, assessors $A$, leaders (tandem runners) $L$ and carriers $C$, with $S+A+L+C=\rho N$; $P$ counts passive workers already carried. With positive rate constants,

$$\begin{aligned}
\dot S&=-\alpha_{sa}S-\beta_{ls}SL-\beta_{cs}SC+\alpha_{as}A+\alpha_{ls}L+\alpha_{cs}C,\\
\dot A&=\alpha_{sa}S+\beta_{ls}SL+\beta_{cs}SC-\alpha_{as}A-\alpha_{al}A,\\
\dot L&=\alpha_{al}A-\alpha_{lc}Q_1L-\alpha_{ls}L,\\
\dot C&=\alpha_{lc}Q_1L-\alpha_{cs}C,\\
\dot P&=\beta_{cs}C\,[(1-\rho)N-P],
\end{aligned}$$

where the *quorum switch* is $Q_1=0$ if $A+L+C<\Theta$ and $Q_1=1$ if $A+L+C>\Theta$, for a quorum threshold $\Theta>0$. Eliminating $S$ gives a three-dimensional Filippov system in $(A,L,C)$ with switching surface $\Sigma=\{A+L+C=\Theta\}$.

**Theorem.**

1. $\mathbb R^5_+$ is positively invariant, every trajectory is attracted to $\Omega=\{S+A+L+C=\rho N,\ 0\le P\le(1-\rho)N\}$, and $S$ is uniformly persistent.
2. Below the quorum ($Q_1=0$) the subsystem has a unique boundary equilibrium $E^f=(A^f,L^f,0)$ (*failed emigration*), globally asymptotically stable. Above the quorum ($Q_1=1$) it has a unique interior equilibrium $E^s=(A^s,L^s,C^s)$ (*successful emigration*), which is locally asymptotically stable, and globally asymptotically stable if $\alpha_{as}>\alpha_{ls}>\alpha_{cs}$ and $\beta_{cs}>\beta_{ls}$ (global stability for all parameters is conjectured from simulations). $E^f$ is a regular equilibrium of the Filippov system iff $A^f+L^f<\Theta$, and $E^s$ is regular iff $A^s+L^s+C^s>\Theta$.
3. The two vector fields have the same component normal to $\Sigma$, namely $\frac{d}{dt}(A+L+C) = (\alpha_{sa}+\beta_{ls}L+\beta_{cs}C)(\rho N-\Theta)-\alpha_{as}A-\alpha_{ls}L-\alpha_{cs}C$, so $\Sigma$ has no sliding region and there is no sliding motion: points of $\Sigma$ where this component is non-zero are crossing points, and the others are tangency points of both fields. (Lemma 3.1 of arXiv:2206.07016 states $\Sigma_C=\Sigma$, $\Sigma_S=\emptyset$; under its own definitions, with $\gamma$ the product of the two normal components (here the square of the common one), the tangency points have $\gamma=0$ and belong to $\Sigma_S=\{\gamma\le0\}$, and they exist, e.g. at $(A,L,C)\approx(24.18,5.82,0)$ for the parameters of its Figure 2.)
4. Let $\mathcal N_1,\mathcal N_2$ be the colony sizes at which $E^f$ and $E^s$ reach $\Sigma$. If $N<\min\{\mathcal N_1,\mathcal N_2\}$, only failed emigration is a regular, locally stable state. If $N>\max\{\mathcal N_1,\mathcal N_2\}$, only successful emigration is. If $\mathcal N_2<N<\mathcal N_1$, both are regular and locally stable (bistability). If $\mathcal N_1<N<\mathcal N_2$, both equilibria are virtual and trajectories keep crossing $\Sigma$.
5. With $\Theta_c=\dfrac{\alpha_{sa}(1-\alpha_{cs}/\alpha_{ls})}{\beta_{ls}(\alpha_{cs}/\alpha_{ls}-\beta_{cs}/\beta_{ls})}$: if $\Theta_c<0$ the order of $\mathcal N_1(\Theta)$ and $\mathcal N_2(\Theta)$ is the same for every $\Theta>0$, decided by how $\alpha_{cs}/\alpha_{ls}$ compares with $1$ and $\beta_{cs}/\beta_{ls}$. If $\Theta_c>0$ the order reverses at $\Theta=\Theta_c$.

## Proof sketch

Under either value of $Q_1$ the smooth subsystem has a single locally attracting equilibrium (globally attracting below the quorum, and above it under the stated rate inequalities), so the Filippov dynamics are set by where the two attractors sit relative to the quorum plane. The switch $Q_1$ enters only the exchange $L\to C$, which leaves $A+L+C$ unchanged, so on $\Sigma$ the two vector fields have the same normal component; they never point to opposite sides of $\Sigma$, which rules out sliding. Both thresholds increase with colony size, which gives the four regimes. Biologically, small colonies cannot muster enough active recruiters to hold a quorum and fail. Large colonies always succeed. Intermediate sizes are either bistable, so history decides the outcome, or oscillate. Whether intermediate sizes are bistable or oscillatory depends on the quorum threshold through the sign of $\Theta-\Theta_c$, which compares leader and carrier recruitment and quitting rates.

## Sources

- Lisha Wang, Zhipeng Qiu, Takao Sasaki and Yun Kang, "Dynamical Behavior of a Colony Migration System: Do Colony Size and Quorum Threshold Affect Collective Decision?", *SIAM Journal on Applied Mathematics* 84 (2024), S43–S64, <https://doi.org/10.1137/22m1478690>. Preprint version: arXiv:2206.07016 (2022), Section 2 (model), Theorem 3.1 (invariance and persistence), Theorems 3.2–3.4 (subsystem equilibria, regular/virtual equilibria), Lemma 3.1 (crossing set; corrected here at tangency points), Corollaries 4.1–4.4 (colony-size regimes), Theorem 5.1 (role of $\Theta_c$), <https://doi.org/10.48550/arXiv.2206.07016>.
