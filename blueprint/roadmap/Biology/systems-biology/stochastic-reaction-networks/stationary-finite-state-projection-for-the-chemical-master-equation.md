# Stationary finite state projection for the chemical master equation

**Setting.** A reaction network with $K$ reactions, stoichiometric vectors $\zeta_k$ and propensities $\lambda_k$ defines a continuous-time Markov chain $X(t)$ on an irreducible state space $\mathcal{E}\subseteq\mathbb{N}_0^d$ with transition-rate matrix $Q$; the chemical master equation (CME) is $\dot p=Q^{\mathsf T}p$. For a finite truncation $\mathcal{E}_n=\{x_{j_1},\dots,x_{j_n}\}$ let $Q_n$ be the restriction of $Q$ to $\mathcal{E}_n$ and $c_n$ the vector of outflow rates

$$
c_{n,i}=\sum_{k:\ x_{j_i}+\zeta_k\notin\mathcal{E}_n}\lambda_k(x_{j_i}) .
$$

The classical finite state projection (FSP) solves $\dot p_n=Q_n^{\mathsf T}p_n$, i.e. sends leaving probability to an absorbing sink, and the lost mass $1-\mathbf 1^{\mathsf T}p_n(t)$ bounds the error at time $t$; this cannot work for $t\to\infty$, since all mass eventually leaks.

**Stationary FSP (sFSP).** Redirect every transition leaving $\mathcal{E}_n$ to a fixed **designated state** $x_\ell\in\mathcal{E}_n$: the projected chain has rate matrix

$$
\bar Q_n=Q_n+c_n b_\ell ,
$$

with $b_\ell$ the $\ell$-th unit row vector, and the stationary law $\pi$ is approximated by the stationary law $\bar\pi_n$ of $\bar Q_n$. The **outflow rate** $r^{(n)}_{\mathrm{out}}=c_n^{\mathsf T}\bar\pi_n$ and, for a Foster–Lyapunov function $V\ge1$, the **convergence factor**

$$
\gamma^{(n)}_V=r^{(n)}_{\mathrm{out}}\Big(V(x_\ell)+\max_{x\in\mathcal{B}(\mathcal{E}_n)}V(x)\Big)
$$

are computable from the sFSP output, where $\mathcal{B}(\mathcal{E}_n)$ is the set of states in $\mathcal{E}_n$ from which some positive-propensity reaction leaves $\mathcal{E}_n$. Write $\|\mu\|_V=\sum_x|\mu(x)|V(x)$.

**Theorem (Gupta–Mikelson–Khammash, Theorem 3.1).** Assume $\mathcal{E}$ is irreducible and there is a norm-like $V:\mathcal{E}\to[1,\infty)$ with the Foster–Lyapunov drift condition $\mathbb{Q}V\le C_1-C_2V$ for constants $C_1,C_2>0$, where $\mathbb{Q}$ is the generator. Let $\mathcal{E}_1\subset\mathcal{E}_2\subset\cdots$ be finite sets increasing to $\mathcal{E}$ and $x_\ell\in\mathcal{E}_1$. Then:

1. (A) $\bar\pi_n$ exists and is unique;
2. (B) $\|\pi-\bar\pi_n\|_{\ell_1}\to0$ as $n\to\infty$;
3. (C) there is $M>0$ with $\|\pi-\bar\pi_n\|_V\le M\gamma^{(n)}_V$ for all $n$;
4. (D) if $V(x)=1+\langle v,x\rangle$ with $v>0$ satisfies both the drift condition $\sum_k\lambda_k(x)\langle v,\zeta_k\rangle\le C_1-C_2(1+\langle v,x\rangle)$ and the diffusivity condition $\sum_k\lambda_k(x)\langle v,\zeta_k\rangle^2\le C_3+C_4(1+\langle v,x\rangle)$, and the truncations grow uniformly ($\min_{\mathcal{B}(\mathcal{E}_n)}V\ge\theta\max_{\mathcal{B}(\mathcal{E}_n)}V$ for some $\theta\in(0,1)$), then also $\|\pi-\bar\pi_n\|_V\ge M'\gamma^{(n)}_V$ for some $M'>0$, and $\gamma^{(n)}_V\to0$.

So the computable convergence factor is, up to constants, equivalent to the uncomputable error, and can be used as a stopping rule when enlarging $\mathcal{E}_n$; if $V$ is unknown but linear, $\max V$ on the boundary may be replaced by any norm of the boundary states (Remark 3.3).

## Proof sketch

Uniqueness: any closed class of the projected chain must contain $x_\ell$, because irreducibility of the original chain gives a reaction path from any state to $x_\ell$, and the first step of that path that leaves $\mathcal{E}_n$ is redirected to $x_\ell$. For the error bound, compare the projected and original generators: they differ only by the redirected outflow, whose total rate under $\bar\pi_n$ is $r^{(n)}_{\mathrm{out}}$, and the drift condition gives a bounded solution of the Poisson equation in the $V$-norm (Meyn–Tweedie), converting this rate discrepancy into a $V$-norm bound scaled by $V$ at the boundary and at $x_\ell$. Linear Foster–Lyapunov functions for many biochemical networks are found by linear programming.

## Sources

- Ankit Gupta, Jan Mikelson and Mustafa Khammash, "A finite state projection algorithm for the stationary solution of the chemical master equation", *The Journal of Chemical Physics* 147 (2017), 154101, <https://doi.org/10.1063/1.5006484>. Preprint version: arXiv:1704.07259 (2017), <https://doi.org/10.48550/arXiv.1704.07259>.
