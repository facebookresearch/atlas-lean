# Deterministic scaling limit of the two-scale selection process

**Model.** A population has $m$ groups of $n$ individuals each, of two types: type I (favored at the individual level) and type G (favored at the group level). Within a group, type I individuals reproduce at rate $1+s$ and type G at rate $1$, $s\ge0$; each birth replaces a uniformly chosen member of the same group. A group whose type-G fraction is $k/n$ replicates at rate $w(1+r\,k/n)$, $w>0$, $r\ge0$, and its identical copy replaces a uniformly chosen group. If $X^i_t$ is the number of type-G individuals in group $i$, the state is the empirical measure

$$
\mu^{m,n}_t=\frac1m\sum_{i=1}^m\delta_{X^i_t/n}\in\mathcal P(\{0,\tfrac1n,\dots,1\}).
$$

**Theorem.** Suppose the initial particle positions are i.i.d. with law $\mu^{m,n}_0\to\mu_0\in\mathcal P([0,1])$. Speed up time by the factor $s$ and set $\lambda=wr/s$. As $m,n\to\infty$, $\mu^{m,n}_t\to\mu_t$ weakly in $D([0,T],\mathcal P([0,1]))$, where $\mu_t$ is the unique solution of

$$
\frac{d}{dt}\langle f,\mu_t\rangle=-\langle x(1-x)f',\mu_t\rangle+\lambda\big[\langle xf,\mu_t\rangle-\langle f,\mu_t\rangle\langle x,\mu_t\rangle\big]
$$

for every positive $f\in C^1([0,1])$, with $\langle f,\mu\rangle=\int_0^1 f\,d\mu$.

**Explicit solution.** With $h(t)=\langle x,\mu_t\rangle$ the mean type-G fraction,

$$
\mu_t(dx)=(\mu_0\circ\phi_t^{-1})(dx)\,w_t(x),\qquad \phi_t^{-1}(x)=\frac{x}{e^{-t}+x(1-e^{-t})},\qquad w_t(x)=\Big[\big(e^{-t}+x(1-e^{-t})\big)e^{\,t-\int_0^t h(z)\,dz}\Big]^{\lambda}.
$$

Within-group selection transports mass toward $0$ along the logistic flow $\dot x=-x(1-x)$, and between-group selection reweights it by the replicator factor $\lambda(x-h(t))$.

## Expansion

The generator decomposes $\langle f,\mu^{m,n}_t\rangle$ into a finite-variation part and a martingale whose quadratic variation is $O(1/m)$, so the martingale vanishes in the limit. Under time speed-up by $s$, the within-group Moran drift becomes the transport term $-x(1-x)f'$ (the diffusive part is $O(1/(ns))$), and group replication at relative rate $wr/s$ gives the replicator term. Tightness of $\langle f,\mu^{m,n}_t\rangle$ and uniqueness of the limiting equation identify the limit. The explicit formula follows from the method of characteristics applied to the linear equation obtained by freezing $h(t)$; consistency (total mass one) holds exactly when $h$ equals the mean of the solution.

## Sources

- Shishi Luo and Jonathan C. Mattingly, *Scaling limits of a model for selection at two scales*, arXiv:1507.00397 (2015), Theorem 1 and Lemma 5; tightness and uniqueness in Lemmas 9–11. <https://doi.org/10.48550/arXiv.1507.00397>. Published version: Nonlinearity 30(4) (2017), 1682–1707, <https://doi.org/10.1088/1361-6544/aa5499>; locators above refer to the arXiv version.
