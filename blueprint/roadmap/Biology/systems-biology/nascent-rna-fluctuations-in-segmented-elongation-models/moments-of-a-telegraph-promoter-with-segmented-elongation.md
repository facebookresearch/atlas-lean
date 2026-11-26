# Moments of a telegraph promoter with segmented elongation

**Model.** A promoter switches $G_{\mathrm{on}} \to G_{\mathrm{off}}$ at rate $s_b$ and back at rate $s_u$. In the on state it initiates a polymerase on segment $1$ at rate $r$. A polymerase on segment $i$ moves to $i + 1$ at rate $k$ (for $i < L$), detaches at rate $d$, and from segment $L$ terminates at rate $k$, producing a mature RNA $M$ that degrades at rate $d_m$. Polymerases do not interact (low traffic). Let $n_0 \in \{0, 1\}$ be the promoter state, $n_i$ the number of polymerases (equivalently nascent RNAs) on segment $i$, and $n$ the number of mature RNAs.

**Elongation time.** Conditional on reaching termination, the time from initiation to termination is Erlang with shape $L$ and rate $k + d$: mean $L/(k + d)$ and coefficient of variation $1/\sqrt{L}$. The probability of completing elongation is $\mu^L$ with $\mu = k/(k + d)$.

**Proposition (means).** With $\eta = s_u/(s_u + s_b)$, $\rho_k = r/k$ and $\rho = r/d_m$, the stationary means are

$$\langle n_0 \rangle = \eta, \qquad \langle n_i \rangle = \eta \rho_k \mu^i \quad (i = 1, \dots, L), \qquad \langle n \rangle = \eta \rho \mu^L,$$

so the mean total nascent RNA is $\eta \rho_k \mu (1 - \mu^L)/(1 - \mu)$, which tends to $\eta r L / k$ as $d \to 0$.

**Proposition (second moments).** Let $\tau_p = 1/(k + d)$, $\tau_g = 1/(s_u + s_b)$, $\tau_m = 1/d_m$, $\alpha = 1/(1 + \tau_p/\tau_g)$, $\theta = 1/(1 + \tau_m/\tau_g)$ and $\beta = s_b/s_u$. The covariance matrix $C$ of $(n_0, n_1, \dots, n_L, n)$ is the unique solution of the Lyapunov equation

$$J C + C J^\top + D = 0,$$

with $J$ the Jacobian of the mean dynamics and $D = S\, \mathrm{Diag}(f)\, S^\top$ ($S$ the stoichiometric matrix, $f$ the reaction rates at the stationary means); this is exact, not an approximation, because all propensities are linear. In particular

$$\mathrm{Var}(n_0) = \langle n_0 \rangle^2 \beta, \qquad \mathrm{Cov}(n_0, n_i) = \langle n_0 \rangle \langle n_i \rangle\, \alpha \beta\, \alpha^{i-1}, \qquad \mathrm{Cov}(n_0, n) = \langle n_0 \rangle \langle n \rangle\, \alpha \beta\, \theta \alpha^{L-1},$$

and every variance has the form "Poisson term plus promoter term", e.g. $\mathrm{Var}(n) = \langle n \rangle + \langle n \rangle^2 \alpha \beta f_{MM}$ with an explicit function $f_{MM}$ of $\alpha, \theta$ and $\tau_p/\tau_m$. With a constitutive promoter ($s_b \to 0$) all $n_i$ and $n$ are independent Poisson variables.

## Expansion

The mean equations $0 = s_u(1 - \langle n_0\rangle) - s_b \langle n_0 \rangle$, $0 = r\langle n_0 \rangle - (k + d)\langle n_1 \rangle$, $0 = k\langle n_{i-1}\rangle - (k + d)\langle n_i \rangle$, $0 = k \langle n_L \rangle - d_m \langle n \rangle$ form a triangular system solved recursively, giving the geometric profile $\mu^i$ along the gene. The Bernoulli promoter has $\mathrm{Var}(n_0) = \eta(1 - \eta) = \eta^2 s_b/s_u$. Promoter-induced covariance decays along the gene by the factor $\alpha < 1$ per segment, the ratio of the gene-switching rate to the sum of switching and segment-exit rates: slow switching ($\alpha \to 1$) correlates the whole gene, fast switching decorrelates it. The general $\mathrm{Cov}(n_i, n_j)$ involves a Gauss hypergeometric function of $1/(2\alpha)$, and the total nascent count $\sum_i n_i$ inherits its Fano factor from these covariances. In the bursty limit $r, s_b \to \infty$ with burst size $b = r/s_b$ fixed, the expressions simplify to burst-size-weighted binomial-coefficient sums.

## Sources

- T. Filatova, N. Popović, R. Grima, "Statistics of nascent and mature RNA fluctuations in a stochastic model of transcriptional initiation, elongation, pausing, and termination", Bulletin of Mathematical Biology 83 (2021) 3, Section 2 (stoichiometry Equation (1); Propositions 1 and 2, Equations (2)–(8)) and Appendix A, <https://doi.org/10.1007/s11538-020-00827-7> (PMC7755674).
