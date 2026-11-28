# Stationary law and convergence of the discrete bursting master equation

**Model.** Let $X(t)\in\{0,1,2,\dots\}$ count gene-product molecules in a cell. Molecules are degraded one at a time at state-dependent rate $\gamma_n$ ($n\to n-1$) and produced in bursts at rate $\lambda_n$ ($n\to n+k$), the burst size $k\ge1$ being drawn independently with probability $h_k$. The probabilities $P_n(t)=\Pr(X(t)=n)$ satisfy the master equation

$$\frac{dP_n}{dt}=\gamma_{n+1}P_{n+1}-\gamma_nP_n+\sum_{k=1}^{n}h_k\lambda_{n-k}P_{n-k}-\lambda_nP_n,\qquad n\ge0,$$

with $P_n(0)=v_n$ a probability vector. Assume

$$\lambda_0>0,\quad \gamma_0=0,\quad \gamma_n>0,\quad \lambda_n,h_n\ge0\ (n\ge1),\quad \sum_{n\ge1}h_n=1.$$

**Stationary candidate.** With tail probabilities $\overline h_l=\sum_{j>l}h_j$, any steady state satisfies the recursion

$$p^*_{n+1}=\frac{1}{\gamma_{n+1}}\sum_{k=0}^{n}\overline h_{n-k}\,\lambda_k\,p^*_k,\qquad n\ge0,$$

so it is unique up to the choice of $p^*_0$.

**Theorem.** Suppose the strictly positive sequence $p^*$ given by this recursion satisfies

$$\sum_{n\ge0}p^*_n=1\qquad\text{and}\qquad \sum_{n\ge0}(\lambda_n+\gamma_n)\,p^*_n<\infty.$$

Then for every initial probability vector $v$ with $\sum_n(\lambda_n+\gamma_n)v_n<\infty$ the master equation has a unique solution, it is a probability vector for each $t>0$, and

$$\lim_{t\to\infty}\sum_{n\ge0}\big|P_n(t)-p^*_n\big|=0.$$

**Geometric bursts.** If $h_k=(1-b)b^{k-1}$, $b\in(0,1)$, then $\overline h_l=b^l$ and the stationary law is explicit,

$$p^*_n=p^*_0\prod_{k=1}^{n}\frac{\lambda_{k-1}+b\,\gamma_{k-1}}{\gamma_k},\qquad n\ge1,$$

and the hypotheses of the theorem hold whenever

$$\limsup_{n\to\infty}\frac{\lambda_n}{\gamma_n}<1-b\qquad\text{and}\qquad \liminf_{n\to\infty}\gamma_n>0.$$

## Expansion

$X$ is the minimal pure-jump process with jump rate $\varphi(n)=\lambda_n+\gamma_n$ and embedded kernel that moves down with probability $q_n=\gamma_n/(\lambda_n+\gamma_n)$ and up by $j$ with probability $(1-q_n)h_j$. The master equation is the Cauchy problem $u'=Gu$, $Gu=-\varphi u+K(\varphi u)$, on $\ell^1$, which generates a substochastic semigroup $P(t)$; it is stochastic exactly when the process does not explode. Summing the stationary equations telescopically gives the recursion for $p^*$. If $p^*$ is a summable density with $\varphi p^*\in\ell^1$, then $G p^*=0$ and $K(\varphi p^*)=\varphi p^*$, which forces $P(t)$ to be stochastic; strict positivity and irreducibility then give $\ell^1$ convergence to $p^*$ (the discrete analog of the Pichór–Rudnicki asymptotic stability theorem for partially integral semigroups). Summing the recursion also yields the flux balance $\sum_n\gamma_{n+1}p^*_{n+1}=\mathbb E(h)\sum_n\lambda_np^*_n$. For geometric bursts the recursion collapses to $p^*_{n+1}/p^*_n=(\lambda_n+b\gamma_n)/\gamma_{n+1}$ and the ratio test gives summability.

The theorem and the geometric-burst corollary are the main results of the section on the discrete bursting model formulated as a Markov process.

## Sources

- M. C. Mackey, M. Tyran-Kamińska, R. Yvinec, *Dynamic behavior of stochastic gene expression models in the presence of bursting*, SIAM J. Appl. Math. 73 (2013); arXiv:1301.1797. <https://doi.org/10.48550/arXiv.1301.1797>
