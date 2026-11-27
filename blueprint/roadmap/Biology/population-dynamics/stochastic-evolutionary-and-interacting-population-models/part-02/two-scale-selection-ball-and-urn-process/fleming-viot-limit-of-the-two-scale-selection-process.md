# Fleming–Viot limit of the two-scale selection process

Consider the two-scale selection particle process on $\{0,1/n,\dots,1\}$: $m$ groups of $n$ individuals; within-group Moran dynamics in which the individually favored type reproduces at rate $1+s$; group replication at rate $w(1+r\,k/n)$ for a group with type-G fraction $k/n$, the offspring group replacing a uniformly chosen group.

**Theorem (weak selection scaling).** Suppose $n/m\to\theta\in(0,\infty)$, $w=O(1)$, $s=\sigma/n$, $r=\rho/m$, and speed up time by the factor $n$. If the initial positions are i.i.d. with law $\nu^{m,n}_0\to\nu_0$, then the rescaled empirical measure converges weakly, as $m,n\to\infty$, to the measure-valued process $\nu_t$ that solves the martingale problem: for every $f\in C^2([0,1])$,

$$
N_t(f)=\langle f,\nu_t\rangle-\langle f,\nu_0\rangle-\int_0^t\langle Af,\nu_z\rangle\,dz-w\theta\rho\int_0^t\!\!\int_0^1\!\!\int_0^1 f(x)\,y\,Q(\nu_z;dx,dy)\,dz
$$

is a martingale with

$$
\langle N(f)\rangle_t=2w\theta\int_0^t\!\!\int_0^1\!\!\int_0^1 f(x)f(y)\,Q(\nu_z;dx,dy)\,dz,
$$

where

$$
Af(x)=x(1-x)\big[f''(x)-\sigma f'(x)\big],\qquad Q(\nu;dx,dy)=\nu(dx)\big(\delta_x(dy)-\nu(dy)\big).
$$

This martingale problem has a unique solution. It is a Fleming–Viot process whose mutation operator $A$ is the Wright–Fisher diffusion generator with selection $-\sigma$ against the group-favored type inside each group, whose selection is the group-level fitness $V(x)=x$ with strength $w\theta\rho$, and whose resampling rate $2w\theta$ comes from random group replacement.

## Expansion

Under $s=\sigma/n$ and time speed-up by $n$, the within-group Moran chain converges to the Wright–Fisher diffusion with drift $-\sigma x(1-x)$, which acts on each particle like a mutation (type-change) operator. Group events at rate $w$ with $r=\rho/m$ contribute an $O(1)$ selection drift after multiplying by $n\approx\theta m$, and group birth–death replacement contributes a martingale term whose bracket, of order $nw/m\to w\theta$, gives the Fleming–Viot sampling covariance $Q$. Tightness of $\langle f,\nu^{m,n}_t\rangle$ for $f\in C^2$ and uniqueness of the martingale problem complete the proof.

## Sources

- Shishi Luo and Jonathan C. Mattingly, *Scaling limits of a model for selection at two scales*, arXiv:1507.00397 (2015), Theorem 4, Lemmas 12–13. <https://doi.org/10.48550/arXiv.1507.00397>. Published version: Nonlinearity 30(4) (2017), 1682–1707, <https://doi.org/10.1088/1361-6544/aa5499>; locators above refer to the arXiv version.
