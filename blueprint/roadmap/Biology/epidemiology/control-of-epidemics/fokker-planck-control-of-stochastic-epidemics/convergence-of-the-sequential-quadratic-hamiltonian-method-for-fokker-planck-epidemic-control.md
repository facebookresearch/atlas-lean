# Convergence of the sequential quadratic Hamiltonian method for Fokker–Planck epidemic control

**Setting.** Consider the Fokker–Planck control problem for a stochastic SIR model with controls $u=(\alpha,\eta,v)$, state density $f_u$, adjoint $q_u$ and Hamiltonian $H(t,f,q,w)$ from [Optimal control of the Fokker–Planck equation of a stochastic SIR model](optimal-control-of-the-fokker-planck-equation-of-a-stochastic-sir-model.md). The *sequential quadratic Hamiltonian* (SQH) method iterates: given $u^k$, solve the forward equation for $f^k$ and the adjoint for $q^k$, then set, pointwise in $t$,

$$u^{k+1}(t)\in\arg\min_{w\in R_U}\Big\{H\big(t,f^k(\cdot,t),q^k(\cdot,t),w\big)+\epsilon\,|w-u^k(t)|^2\Big\},$$

accepting the update and decreasing $\epsilon$ when the cost decreases enough, and increasing $\epsilon$ otherwise.

**Theorem.**

1. (Sufficient decrease.) For the accepted penalty $\epsilon>0$,

$$J(f^{k+1},u^{k+1})-J(f^k,u^k)\le-\epsilon\,\|u^{k+1}-u^k\|^2_{L^2(0,T)^3}.$$

2. With a fixed acceptance threshold $\epsilon=\mu$, the costs $J(f^k,u^k)$ decrease and converge to a limit $J^*\ge\inf J$, and $\|u^{k+1}-u^k\|_{L^2}\to0$.
3. ($L^2$–$L^1$ costs.) If $\ell(u)=\frac{\beta_2}{2}|u|^2+\beta_1|u|_1$ with $\beta_1,\beta_2>0$, write $H=\frac{\beta_2}{2}|w|^2+\beta_1|w|_1-r(w)$, and suppose $r$ is Lipschitz from $L^2$ to $L^2$ with constant $C_r$. If $\beta_2>C_r$, then for every $\epsilon>0$ the SQH update is a contraction, so $u^k$ converges strongly in $L^2$ to a unique fixed point $u^*$, which satisfies the Pontryagin minimum principle.

## Expansion

The penalty $\epsilon|w-u^k|^2$ makes each pointwise minimization well posed even for non-smooth $L^1$ costs that produce bang-bang controls, and it controls the error of using $f^k,q^k$ from the previous control: expanding $J(u^{k+1})-J(u^k)$ in terms of the Hamiltonian difference leaves a remainder bounded by a constant times $\|u^{k+1}-u^k\|^2$, which the penalty dominates once $\epsilon$ is large enough. Summing the decrease inequality shows the step sizes are square-summable. With an $L^2$–$L^1$ cost the pointwise minimizer is an explicit soft-thresholding of the linear part $r$, a $\beta_2^{-1}$-Lipschitz map, so the composition is a contraction when $\beta_2$ exceeds the Lipschitz constant of $r$.

## Depends on

- [Optimal control of the Fokker–Planck equation of a stochastic SIR model](optimal-control-of-the-fokker-planck-equation-of-a-stochastic-sir-model.md)

## Sources

- Christian Parkinson, Souvik Roy, "A Fokker-Planck Framework for Control of Epidemics", arXiv:2601.20181 (2026): Section 4 (SQH algorithm; sufficient-decrease theorem, termination theorem and the convergence theorem for $L^2$–$L^1$ costs). <https://doi.org/10.48550/arXiv.2601.20181> Published version: Journal of Mathematical Biology 93 (2026) 47, <https://doi.org/10.1007/s00285-026-02462-7>.
