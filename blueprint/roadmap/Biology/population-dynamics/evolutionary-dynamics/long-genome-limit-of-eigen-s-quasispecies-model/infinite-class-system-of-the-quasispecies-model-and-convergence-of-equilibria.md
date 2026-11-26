# Infinite class system of the quasispecies model and convergence of equilibria

**Finite model.** Genotypes are sequences of length $\ell$ over an alphabet of $\kappa$ letters; class $k\in\{0,\dots,\ell\}$ collects genotypes at Hamming distance $k$ from a master sequence, with class-dependent fitness $f(k)>0$. Each site mutates independently with probability $q$ per replication, so a class-$i$ parent produces a class-$k$ offspring with probability $M(i,k)=\mathbb P\big(i-\mathrm{Bin}(i,\tfrac q{\kappa-1})+\mathrm{Bin}(\ell-i,q)=k\big)$. Eigen's system for class frequencies $x_k$ is

$$x_k'=\sum_{i=0}^{\ell}x_if(i)M(i,k)-x_k\sum_{i=0}^{\ell}x_if(i),$$

which has a unique stationary point $x^\ast$ in the simplex (the normalized left Perron eigenvector of $W=\mathrm{diag}(f)M$, with mean fitness its Perron eigenvalue), attracting every trajectory.

**Infinite system.** In the regime $\ell\to\infty$, $q\to0$, $\ell q\to a\in(0,\infty)$, back mutations vanish and forward mutations become Poisson($a$). Let $f_\infty:\mathbb N\to(0,\infty)$ extend $f$, with a strict maximum at $0$ and $f_\infty(k)\to1$. The limit system is

$$y_k'=\sum_{i=0}^{k}y_if_\infty(i)\,e^{-a}\frac{a^{k-i}}{(k-i)!}-y_k\sum_{i\ge0}y_if_\infty(i),\qquad k\ge0 .$$

Let $I(f_\infty)$ be the set of $i$ with $f_\infty(i)e^{-a}>1$ and $f_\infty(i)>f_\infty(j)$ for all $j>i$, listed $i_1<\dots<i_N$. For each $i\in I(f_\infty)$ there is exactly one stationary probability vector $\rho^i$, and $\rho^i_0=\dots=\rho^i_{i-1}=0<\rho^i_i$.

**Theorem (basins in the infinite system).** A solution satisfies $y_k(t)\to\rho^{i_h}_k$ for all $k$ iff $y_0(0)=\dots=y_{i_{h-1}}(0)=0$ and $\max_{i_{h-1}<i\le i_h}y_i(0)>0$; then $y(t)\to\rho^{i_h}$ in $\ell^1$. Otherwise $y_k(t)\to0$ for every $k$.

**Theorem (convergence of trajectories).** If $x_k(0)\to y_k(0)$ for every $k$ in the regime above, then $\sup_{0\le t\le T}|x_k(t)-y_k(t)|\to0$ for every $k$ and $T>0$.

**Theorem (error threshold for equilibria).** In the same regime, the finite stationary point satisfies

$$x^\ast_k\to\begin{cases}0 & \text{if } f(0)e^{-a}\le1,\\ \rho^0_k & \text{if } f(0)e^{-a}>1,\end{cases}\qquad k\ge0,$$

with $\rho^0$ the stationary solution of the infinite system with $\rho^0_0>0$. The same results hold for the discrete-time (deterministic Moran) version.

## Expansion

In the limit a class can only feed higher classes, so the infinite system is lower triangular: $y_0$ solves a closed logistic-type equation, and each $y_k$ solves a linear ODE driven by lower classes. A class $i$ can sustain itself only if its replication rate without mutation, $f_\infty(i)e^{-a}$, beats the asymptotic mean fitness, which is why stationary solutions are indexed by $I(f_\infty)$ and why the lowest occupied record class determines the limit. The threshold $f(0)e^{-a}=1$ is Eigen's error threshold in the long-genome limit: $e^{-a}$ is the probability of an error-free copy when the mean number of mutations per genome is $a$. Comparison lemmas for linear ODEs give the termwise convergence of trajectories and equilibria.

## Sources

- Joseba Dalmau, "Asymptotic behavior of Eigen's quasispecies model", arXiv:1704.07280: Section 2 (models; Propositions 2.1–2.2 on stationary solutions), Theorem 3.1 (basins of the infinite system), Theorem 3.2 (convergence of trajectories), Theorem 3.3 (convergence of equilibria and error threshold), Appendix Lemmas 1.1–1.3. <https://doi.org/10.48550/arXiv.1704.07280> Published version: Bulletin of Mathematical Biology 80 (2018) 1689–1712, <https://doi.org/10.1007/s11538-018-0420-8>.
