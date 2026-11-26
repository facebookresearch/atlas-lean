# Piecewise-linear approximation of log-observables via Hilbert's projective metric

**Setting.** Let $V$ be an ordered vector space with closed pointed cone $V_{\ge0}$. Two nonzero vectors $u,v\in V_{\ge0}$ lie in the same *part* if $\alpha v\le u\le\beta v$ for some $\alpha,\beta>0$. On a part, **Hilbert's projective metric** is

$$d_H(u,v)=\log\inf\{\beta/\alpha:\ \alpha v\le u\le\beta v\}.$$

On $V=\mathbb R^n$ with the positive orthant this reads $d_H(u,v)=\log\max_i(u_i/v_i)+\log\max_i(v_i/u_i)$. Its distances are invariant under scaling of either argument.

Epidemic control regimes, such as successive lockdown phases, are modeled by switching times $t_0=0<t_1<\dots<t_m$. On $[t_{j-1},t_j)$ the state evolves under a linear order-preserving semigroup $S^j$ with a nonnegative eigenvector $u^j$: $S^j_tu^j=e^{\lambda_jt}u^j$. Let $v_t$ be the resulting state from $v_0$, and let $\varphi$ be a nonnegative linear form, the observable. Put $y_t=\log\varphi(v_t)$.

**Theorem.** Suppose the semigroups are order preserving, and that $v_0,u^1,\dots,u^m$ all lie in one nontrivial part of $V_{\ge0}$ on which $\varphi$ is positive. Then there is a constant $\gamma$ such that the piecewise-linear function

$$y^{\mathrm{trop}}_t=\lambda_{j+1}(t-t_j)+\lambda_j(t_j-t_{j-1})+\dots+\lambda_1(t_1-t_0)+\gamma,\qquad t\in[t_j,t_{j+1}),$$

satisfies, for all $t\ge0$,

$$\big|y_t-y^{\mathrm{trop}}_t\big|\le\frac\Delta2,\qquad \Delta=d_H(v_0,u^1)+d_H(u^1,u^2)+\dots+d_H(u^{m-1},u^m).$$

If $\dim V=1$, as in an SIR ODE linearized at the start of an epidemic, then $\Delta=0$ and the approximation is exact. The theorem holds verbatim in discrete time. For the transport PDE SEIR model with contact intensities $\mu^1,\mu^2$, whose Perron–Frobenius eigenpairs are $(\lambda^i,\bar n^i)$,

$$d_H(\bar n^1,\bar n^2)\le|\lambda^1-\lambda^2|\,(x_E^*+x_I^*),$$

where $x_E^*,x_I^*$ are the maximal exposed and infectious durations. So the error of reading the log of an observable as a broken line with slopes $\lambda_j$ is controlled by the jumps in growth rate times the maximal generation time.

## Expansion

Order-preserving linear maps are nonexpansive in $d_H$, and $S^j_t$ maps $u^j$ to a multiple of itself. Hence $d_H(v_t,u^j)$ does not increase within phase $j$, and by the triangle inequality $d_H(v_{t_j},u^{j+1})\le d_H(v_0,u^1)+\sum_{i\le j}d_H(u^i,u^{i+1})$. On a part, $\alpha u\le v\le\beta u$ with $\log(\beta/\alpha)=d_H(u,v)$. Applying $\varphi$ and the exact growth $e^{\lambda_jt}$ of $\varphi(u^j)$ traps $y_t$ in a band of width $\Delta$ around a broken line, and centering gives the bound $\Delta/2$. The broken line is a max-plus (tropical) object, hence the label "trop". In the PDE example the eigenvectors are explicit exponentials in the duration variable. Comparing two of them gives the ratio $\bar n^1/\bar n^2\propto e^{-(\lambda^1-\lambda^2)x}$, which varies by at most $|\lambda^1-\lambda^2|(x_E^*+x_I^*)$ in logarithm.

These are the main theorem and its remarks in the source's Hilbert-geometry section, and the bound proposition of its application to the transport PDE model.

## Depends on

- [Universal log-rate of epidemic observables in a transport PDE SEIR model](universal-log-rate-of-epidemic-observables-in-a-transport-seir-model.md)

## Sources

- S. Gaubert, M. Akian, X. Allamigeon, M. Boyet et al., "Understanding and monitoring the evolution of the Covid-19 epidemic from medical emergency calls: the example of the Paris area", arXiv:2005.14186 (2020). <https://doi.org/10.48550/arXiv.2005.14186>
