# Extended Kalman filter for diffusion-approximation epidemic models with hidden states

**State model.** A compartmental epidemic with $d$ compartments and $K$ independent transition types is a continuous-time Markov chain $X(t)=X(0)+\sum_{k=1}^K\xi_k\Pi_k\big(\int_0^t\lambda_k(s,X(s))ds\big)$, with $\Pi_k$ unit-rate Poisson processes and $\xi_k\in\{0,\pm1\}^d$ the transition vectors. For large populations its diffusion approximation is
$$dX^D=f_X(t,X^D)\,dt+\sigma_X(t,X^D)\,dW,\qquad f_X=\sum_k\xi_k\lambda_k,\quad \sigma_X=\big(\xi_1\sqrt{\lambda_1},\dots,\xi_K\sqrt{\lambda_K}\big),$$
and an Euler-Maruyama step $\Delta t$ gives a nonlinear stochastic recursion. Split the state into hidden compartments $Y$ and observed ones $Z$, with noises $\varepsilon^1$ (driving only $Y$) and $\varepsilon^2$ (shared):
$$Y_{n+1}=f(n,Y_n,Z_n)+\sigma\,\varepsilon^1_{n+1}+g\,\varepsilon^2_{n+1},\qquad Z_{n+1}=h(n,Y_n,Z_n)+\ell\,\varepsilon^2_{n+1}.$$

**Theorem (Kalman filter for conditionally Gaussian sequences; Liptser-Shiryaev).** Suppose instead that
$$Y_{n+1}=\tilde f_0+\tilde f_1Y_n+\tilde\sigma\,\varepsilon^1_{n+1}+\tilde g\,\varepsilon^2_{n+1},\qquad Z_{n+1}=\tilde h_0+\tilde h_1Y_n+\tilde\ell\,\varepsilon^2_{n+1},$$
with coefficients that are measurable square-integrable functions of the observation path $(Z_0,\dots,Z_n)$, bounded $\tilde f_1,\tilde h_1$, square-integrable initial data and Gaussian $Y_0\mid Z_0$. Then $Y_n$ given $\mathcal F^Z_n$ is Gaussian $\mathcal N(M_n,Q_n)$, and with $B_n=\tilde g\tilde\ell^{\mathsf T}+\tilde f_1Q_n\tilde h_1^{\mathsf T}$ and $D_n=\tilde\ell\tilde\ell^{\mathsf T}+\tilde h_1Q_n\tilde h_1^{\mathsf T}$,
$$M_{n+1}=\tilde f_0+\tilde f_1M_n+B_nD_n^{+}\big(Z_{n+1}-\tilde h_0-\tilde h_1M_n\big),$$
$$Q_{n+1}=\tilde f_1Q_n\tilde f_1^{\mathsf T}+\tilde\sigma\tilde\sigma^{\mathsf T}+\tilde g\tilde g^{\mathsf T}-B_nD_n^{+}B_n^{\mathsf T},$$
where $^+$ is the Moore-Penrose pseudoinverse. Because the coefficients depend on the observed path, $Q_n$ must be computed online, unlike the offline Riccati recursion of the constant-coefficient Kalman filter.

**Extended Kalman filter.** For the epidemic recursion, whose drift is quadratic in the hidden states (mass-action incidence) and whose noise coefficients depend on the state, linearize $f$ by a first-order Taylor expansion around the current estimate, $\bar Y_n=M^{\mathrm{EKF}}_n$, freeze the diffusion coefficients at the same point, and apply the recursions above. With an observation drift already linear in $Y$, $h=h_0(n,z)+h_1(n,z)y$, this yields a recursive nowcast of hidden compartments together with its conditional covariance. The pseudoinverse keeps the filter well defined when $\ell\ell^{\mathsf T}$ is singular, as happens with deterministic cascade (time-since-recovery) states.

## Depends on

- [Diffusion approximation of the stochastic SIR epidemic](../diffusion-approximation-of-the-stochastic-sir-ep/README.md)

## Expansion

The conditional Gaussianity holds because, given the observation path, the system is linear in the signal with Gaussian innovations, and correlated signal and observation noise ($\tilde g\ne0$) enters through the cross term $\tilde g\tilde\ell^{\mathsf T}$ in the gain. The EKF replaces the exact nonlinear filter by this conditionally Gaussian surrogate at each step, so it is exact only to first order. Numerical experiments on COVID-19 models with undetected infectious and asymptomatic compartments show accurate tracking of the hidden states, sensitivity to the initial estimate that decays over time, and improvements when cascade states encode the time since recovery or vaccination.

## Sources

- F. Ouabo Kamkumo, I. Mbouandi Njiasse, R. Wunderlich, "Estimating unobservable states in stochastic epidemic models with partial information", arXiv:2506.00906 (2025), Section 2.1 (microscopic and macroscopic models, hidden-state recursion), Section 3.1 (Assumption, Theorem citing Liptser-Shiryaev Theorem 13.4), Sections 3.2-3.3 (EKF linearization) and Section 5 (numerical results), <https://doi.org/10.48550/arXiv.2506.00906>.
