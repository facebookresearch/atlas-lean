# Small-gain theorem for balancing kinetics and input-to-state stability of the SIR model

**Networks with balancing kinetics.** For $x = (x_1,\dots,x_n) \in \mathbb{R}_+^n$ (indices circular mod $n$) and inputs $w(t) \in \mathbb{R}_+^n$, consider

$$

\dot x_i = -\eta_{i-1,i}(x) + \sigma_{i,i-1}(x) - \eta_{i+1,i}(x) + \sigma_{i,i+1}(x) - \theta_i(x_i) + \kappa_i(w_i), \qquad i = 1,\dots,n,

$$

where consumption of $x_i$ at rate $\eta_{j,i}$ produces neighbour $x_j$ at rate $\sigma_{j,i}$, $\theta_i$ is positive definite (extra loss), $\kappa_i$ is a class-$\mathcal K$ function or zero, all functions are locally Lipschitz and nonnegative, and $x_i = 0$ implies $\eta_{i\pm1,i}(x) = 0$. Assume the conversion bounds

$$

\sigma_{i,j}(x) \le \ell_{i,j}\,\eta_{i,j}(x) \qquad (j = i \pm 1,\ x \in \mathbb{R}_+^n)

$$

for constants $\ell_{i,j} \ge 0$.

**Theorem.** Suppose

1. $\ell_{i,i+1}\,\ell_{i+1,i} \le 1$ for every $i$ (no gain around any two-cycle), and
2. for some $k$, $\displaystyle \ell_{k,k+1}\ell_{k+1,k} \le \prod_{i=1}^n \frac{\ell_{i,i+1}}{\ell_{i+1,i}} \le \frac{1}{\ell_{k,k+1}\ell_{k+1,k}}$ (no gain around the $n$-cycle in either direction).

Then the network is integral input-to-state stable (iISS) with respect to $w$; if every $\theta_i$ is of class $\mathcal K$ it is strongly iISS, and if every $\theta_i$ is of class $\mathcal K_\infty$ it is input-to-state stable (ISS). An iISS/ISS Lyapunov function is linear, $V(x) = \sum_i \lambda_i x_i$ with $\lambda_i = \prod_{j=k+2}^{i}\sqrt{\ell_{j-1,j}/\ell_{j,j-1}}$ for $i = k+1,\dots,k+n$.

**Application to SIR.** The SIR endemic model with time-varying recruitment $B(t) \ge 0$,

$$

\dot S = B - \mu S - \beta IS, \qquad \dot I = \beta IS - (\gamma+\mu)I, \qquad \dot R = \gamma I - \mu R,

$$

fits this form with $\ell_{i+1,i} = \ell_{i,i+1} = 1$ and $\theta_i(s) = \mu s$, so it is ISS with respect to $B$, with Lyapunov function $S + I + R$. This holds although the infected subsystem alone is not ISS with respect to $S$: for constant $S > (\gamma+\mu)/\beta$ it produces unbounded $I$. It is only strongly iISS, via $V_I = \log(1+I)$.

## Expansion

Along solutions, $\dot V = \sum_i \lambda_i\big(\sigma_{i,i-1} + \sigma_{i,i+1} - \eta_{i-1,i} - \eta_{i+1,i}\big) - \sum_i\lambda_i\theta_i(x_i) + \sum_i \lambda_i\kappa_i(w_i)$. Regrouping by edges, each transfer $\eta_{j,i}$ contributes $(\lambda_j\ell_{j,i} - \lambda_i)\,\eta_{j,i}$ at most, and the stated choice of weights makes all these coefficients nonpositive exactly under the two cycle conditions: the two-cycle condition handles back-and-forth transfers and the product condition closes the weights consistently around the ring. What remains is $\dot V \le -\sum_i\lambda_i\theta_i(x_i) + \sum_i\lambda_i\kappa_i(w_i)$, the iISS (or ISS) dissipation inequality. For SIR the infection term moves mass from $S$ to $I$ and recovery from $I$ to $R$, all with unit conversion, so total population is the Lyapunov function.

## Sources

- Hiroshi Ito, "Interpreting models of infectious diseases in terms of integral input-to-state stability", arXiv (2020); Mathematics of Control, Signals, and Systems (2020). Section "A Small-Gain Theorem for Generalized Balancing Kinetics" (main theorem), Section "SIR Model"; further sections treat MSIR, SEIR, SEIS and vaccination models. <https://doi.org/10.48550/arXiv.2004.02552>. Published version: Mathematics of Control, Signals, and Systems 32(4) (2020), 611–631, <https://doi.org/10.1007/s00498-020-00272-w>; locators above refer to the arXiv version.
