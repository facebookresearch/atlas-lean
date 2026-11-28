# Backward bifurcation from viral-load-dependent transmission

In the [multiscale within- and between-host model](basic-reproduction-number-of-a-multiscale-model-with-environmental-transmission.md), set $\epsilon=0$ and replace the viral load by its quasi-steady state $V=f(Z)$. The slow system is

$$\begin{aligned}
\dot S&=\Lambda-\beta_E(f(Z),E)SE-\beta_I(f(Z),I)SI-\beta_Z(Z)SZ-\mu S,\\
\dot E&=\beta_E(f(Z),E)SE+\beta_I(f(Z),I)SI+\beta_Z(Z)SZ-(\alpha+\mu)E,\\
\dot I&=\alpha E-(\omega+\gamma+\mu)I,\qquad \dot R=\gamma I-\mu R,\qquad \dot Z=\xi_EE+\xi_II-\delta Z .
\end{aligned}$$

At an equilibrium, $E=\theta_EI$, $R=\theta_RI$, $Z=\theta_ZI$ with $\theta_E=(\omega+\gamma+\mu)/\alpha$, $\theta_R=\gamma/\mu$, $\theta_Z=(\alpha\xi_I+(\omega+\gamma+\mu)\xi_E)/(\delta\alpha)$, and $S$ must lie on both curves

$$\phi(I)=S_0-mI,\qquad \psi(I)=\frac{\mu m}{g(I)},\qquad m=\frac{(\alpha+\mu)(\omega+\gamma+\mu)}{\alpha\mu},$$

where $g(I)=\beta_E(f(\theta_ZI),\theta_EI)\theta_E+\beta_I(f(\theta_ZI),I)+\beta_Z(\theta_ZI)\theta_Z$. Under the standing assumptions $g$ is strictly concave, so $\psi$ is strictly convex, and $\phi(0)>\psi(0)$ iff $\mathcal R_0^b>1$.

1. **Bifurcation type.** With $S_0=\Lambda/\mu$ as the bifurcation parameter, the slow system has a transcritical bifurcation at $\mathcal R_0^b=1$. It is backward if $\psi'(0)<-m$ and forward if $\psi'(0)\ge-m$. In the backward case there is $\mathcal R_0^{b,c}\in(0,1)$ such that for $\mathcal R_0^b\in(\mathcal R_0^{b,c},1)$ two endemic equilibria coexist with the disease-free one.
2. **Forward case, global dynamics.** Suppose $\psi'(0)\ge-m$ and either $\eta'(0)=0$ or $\partial_V\beta_E(0,0)=\partial_V\beta_I(0,0)=0$. On $\Omega_s=\{S+E+I+R\le S_0,\ 0\le Z\le(\xi_E+\xi_I)S_0/\delta\}$, if $\mathcal R_0^b<1$ the disease-free equilibrium is globally asymptotically stable, and if $\mathcal R_0^b>1$ the disease is uniformly persistent in the interior.

## Depends on

- [Basic reproduction number of a multiscale model with environmental transmission](basic-reproduction-number-of-a-multiscale-model-with-environmental-transmission.md)

## Expansion

Positive equilibria are intersections of the decreasing line $\phi$ with the convex curve $\psi$. Writing $S_0=h(I)=mI+\psi(I)$ along equilibria, $h$ is strictly convex; if $h'(0)=m+\psi'(0)\ge0$ then $I=h^{-1}(S_0)$ is a single increasing branch emanating from $S_0=\psi(0)$ (forward), whereas if $h'(0)<0$ then $h$ has a minimum at some $I_c>0$, giving two branches over $S_0\in(h(I_c),\psi(0))$ that meet at a fold (backward). Viral-load dependence enters through $f'$: transmission rises with prevalence because more environmental virus raises within-host load, which can outweigh the prevalence-driven reduction in contact. The global result uses a linear Lyapunov function $L$ with $L'\le(\mathcal R_0^b-1)\,u\cdot Y$, where $Y$ collects the infected compartments, so that $L'=0$ forces $u\cdot Y=0$ when $\mathcal R_0^b<1$.

## Sources

- X. Wang, S. Wang, J. Wang, L. Rong, "A Multiscale Model of COVID-19 Dynamics", Bulletin of Mathematical Biology (2022), slow system Eq. (13), equilibria Eqs. (14)–(20), bifurcation analysis Eqs. (21)–(23) and Lemma 1, Theorem 1 with its proof in the appendix, <https://doi.org/10.1007/s11538-022-01058-8>, PMCID PMC9360740.
