# Extinction threshold for the switching stochastic SIS model on a network

**Model.** Consider $N$ nodes with infection probabilities $x=(x_1,\dots,x_N)\in[0,1]^N$, and an environment $s(t)$ that is an irreducible continuous-time Markov chain on $S=\{1,\dots,m\}$ with stationary distribution $(\rho_1,\dots,\rho_m)$, independent of the Brownian motions $W_i$. In regime $s$ the network has nonnegative adjacency matrix $A(s)=(a_{ij}(s))$ with largest eigenvalue $\lambda_1(s)$, infection rate $\beta(s)>0$ and recovery rate $\delta(s)>0$. With $b_i(x,s)=\sum_j a_{ij}(s)x_j$,
$$dx_i=\big[\beta(s)\,b_i(x,s)(1-x_i)-\delta(s)x_i\big]dt+\sigma_i(x_i,s)\,b_i(x,s)(1-x_i)\,dW_i(t),$$
where $\sigma_i(\cdot,s)$ is continuously differentiable, $\sigma_i(0,s)=0$ and $\sigma_i>0$ on $(0,1)$.

**Statement.** If
$$\Lambda:=\sum_{s=1}^m\rho_s\big(\beta(s)\lambda_1(s)-\delta(s)\big)<0,$$
then for every initial condition, almost surely
$$\limsup_{t\to\infty}\frac{\log\|x(t)\|}{t}\le\Lambda<0,$$
so the infection dies out exponentially fast. The threshold involves only the regime-averaged spectral growth rate, with no extra condition on the noise intensities.

## Depends on

- [Average Lyapunov function criterion for extinction of Markov processes](average-lyapunov-function-criterion-for-extinction-of-markov-processes.md)

## Expansion

Take $V(x,s)=-\tfrac12\log\|x\|^2$. Its generator does not extend continuously to $x=0$ because the drift term depends on the direction of approach, so lift to polar coordinates $x=rv$ with $v$ on the unit sphere. On the lifted boundary $r=0$ the extension is $H(v,0,s)=\delta(s)-\beta(s)\,v^{\top}A(s)v\ge\delta(s)-\beta(s)\lambda_1(s)$, since the noise vanishes at $x=0$ and $\|v\|=1$. Averaging over any invariant measure of the boundary process, whose $s$-marginal is $\rho$, gives $\mu H\ge-\Lambda>0$. Accessibility of $x=0$ follows from the Stroock-Varadhan support theorem, so the global extinction criterion applies.

## Sources

- Juraj Foldes, Declan Stacy, "Stochastic Extinction, An Average Lyapunov Function Approach", arXiv:2407.19606 (2024), Section 10.1 and Theorem 10.1, <https://doi.org/10.48550/arXiv.2407.19606>.
