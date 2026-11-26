# Equilibrium of the birth, death and innovation model

Fix a maximal family size $N \ge 2$. Let $f_i(t) \ge 0$ be the number of gene (or protein-domain) families with exactly $i$ members, $1 \le i \le N$. A family of size $i$ gains a member (duplication, "birth") at rate $\lambda_i > 0$ for $1 \le i \le N-1$ and loses one ("death") at rate $\delta_i > 0$ for $1 \le i \le N$; a family of size $1$ that loses its member disappears, and new singleton families arise ("innovation") at a constant rate $\nu > 0$. The **master birth, death and innovation model (BDIM)** is the linear system

$$\begin{aligned}
\dot f_1 &= -(\lambda_1 + \delta_1) f_1 + \delta_2 f_2 + \nu,\\
\dot f_i &= \lambda_{i-1} f_{i-1} - (\lambda_i + \delta_i) f_i + \delta_{i+1} f_{i+1}, \qquad 1 < i < N,\\
\dot f_N &= \lambda_{N-1} f_{N-1} - \delta_N f_N,
\end{aligned}$$

and the total number of families $F = \sum_i f_i$ obeys $\dot F = \nu - \delta_1 f_1$. The **simple BDIM** is the special case $\lambda_i = \lambda i$, $\delta_i = \delta i$ (each member duplicates and is lost independently at per-member rates $\lambda, \delta$).

**Proposition (unique equilibrium).** The master BDIM has a unique equilibrium,

$$f_1 = \frac{\nu}{\delta_1}, \qquad f_i = \frac{\nu}{\delta_i} \prod_{j=1}^{i-1} \frac{\lambda_j}{\delta_j} \quad (2 \le i \le N), \qquad F_{\mathrm{eq}} = \nu \sum_{i=1}^{N} \frac{1}{\delta_i} \prod_{j=1}^{i-1} \frac{\lambda_j}{\delta_j},$$

and it is globally asymptotically stable: every solution converges to it exponentially fast. The equilibrium frequencies are $p_i = f_i / F_{\mathrm{eq}}$.

**Proposition (simple BDIM).** For the simple BDIM with $\theta = \lambda/\delta$,

$$f_i = \frac{\nu}{\lambda}\,\frac{\theta^i}{i}, \qquad p_i = \frac{\theta^i / i}{\sum_{j=1}^{N} \theta^j / j},$$

so the equilibrium frequencies follow the truncated logarithmic distribution; in the balanced case $\theta = 1$ they are $p_i = \big(i \sum_{j=1}^N 1/j\big)^{-1}$, a power law of exponent $-1$. Consequently no simple BDIM produces a power-law family-size distribution with exponent different from $-1$.

## Expansion

Setting the right-hand sides to zero, summing the equations for classes $i, i+1, \dots, N$ gives the flux balance $\lambda_{i-1} f_{i-1} = \delta_i f_i$ for $2 \le i \le N$, and the first equation then forces $\delta_1 f_1 = \nu$ (innovation balances loss of singletons). Iterating the flux balance gives the product formula, which is positive and unique. The system is linear, $\dot f = A f + \nu e_1$, with $A$ tridiagonal and irreducible, with negative diagonal and positive off-diagonal entries, whose column sums are $-\delta_1 < 0$ for the first column and $0$ for the others. Hence $-A$ is an irreducibly diagonally dominant Z-matrix, so a nonsingular M-matrix, the spectrum of $A$ lies in the open left half-plane, and convergence is exponential. For the simple BDIM, $\lambda_j/\delta_{j+1} = \lambda j/(\delta (j+1))$ telescopes to $\theta^{i-1}/i$. The system for the frequencies $p_i = f_i/F$ is nonlinear (it carries the factor $\nu/F$), so it is not the forward equation of any continuous-time Markov chain on $\{1, \dots, N\}$. Once $F$ has reached $F_{\mathrm{eq}}$ the frequencies satisfy the linear system (2.5) of the source, $\dot p = pQ$, whose rows other than the first sum to $\nu/F_{\mathrm{eq}} > 0$; for $\nu > 0$ it is still no Markov forward equation, and with $\nu = 0$ system (2.5) is the forward equation of a birth-death chain.

## Sources

- G. P. Karev, Y. I. Wolf, A. Y. Rzhetsky, F. S. Berezovskaya and E. V. Koonin, "Birth and death of protein domains: a simple model of evolution explains power law behavior", BMC Evolutionary Biology 2 (2002) 18, Eqs. (2.1)–(2.3), (3.1)–(3.8), Propositions 1 and 2, <https://doi.org/10.1186/1471-2148-2-18>, PMCID PMC137606.
