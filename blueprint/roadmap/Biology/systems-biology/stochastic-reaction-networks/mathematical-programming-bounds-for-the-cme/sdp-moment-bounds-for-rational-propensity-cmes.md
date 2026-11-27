# Semidefinite-programming bounds on stationary moments of the chemical master equation

Consider a stochastic reaction network with $n$ species and $m$ reactions with net stoichiometric vectors $v_j$ and propensities $a_j$ on a state space $\mathcal{S} \subseteq \mathbb{N}^n$, with rate matrix $q(x,y) = \sum_j a_j(x)(1_{x+v_j}(y) - 1_x(y))$. A stationary solution of the chemical master equation (CME) is a probability distribution $\pi$ with $\pi Q = 0$; let $\mathcal{P}$ be the set of them. Assume rational propensities $a_j = b_j/s$ with polynomials $b_j$ and a common denominator $s > 0$ on $\mathcal{S}$, of degrees $\le d_b$ and $d_s$. For multi-indices $\beta$ define the rational moments $z_\beta = \langle x^\beta/s\rangle_\pi$ and the polynomials $g_\alpha(x) = s(x)\,Qx^\alpha = \sum_j b_j(x)\big((x+v_j)^\alpha - x^\alpha\big)$ with coefficient vectors $\mathbf{g}_\alpha$.

**Assumption 1.** For an order $d \ge d_s$, every $\pi \in \mathcal{P}$ has finite rational moments $z_\beta$ for $|\beta| \le d+1$ (checkable with a Foster–Lyapunov criterion).

**Lemma 3 (moment equations).** Under Assumption 1, every $\pi \in \mathcal{P}$ satisfies $z^T\mathbf{g}_\alpha = 0$ for all $|\alpha| \le d - d_b + 1$, where $z = (z_\beta)_{|\beta| \le d}$.

**Lemma 5 (outer approximation).** Under Assumption 1, for every $\pi \in \mathcal{P}$ the vector $z$ lies in the spectrahedron

$$\mathcal{E}^d = \Big\{ y : y^T\mathbf{g}_\alpha = 0\ (|\alpha| \le d - d_b + 1),\ \ y^T\mathbf{s} = 1,\ \ M_d^i(y) \succeq 0\ (i = 0, 1, \dots, n)\Big\},$$

where $\mathbf{s}$ is the coefficient vector of $s$, $[M_d^0(y)]_{\alpha\beta} = y_{\alpha+\beta}$ and $[M_d^i(y)]_{\alpha\beta} = y_{\alpha+\beta+e_i}$ are moment and localizing matrices.

**Corollary 6 (monotone moment bounds).** If $f$ is a polynomial of degree $d_f \le d$ with coefficient vector $\mathbf{f}$, and $L_f^{d'} = \inf\{\mathbf{f}^Ty : y \in \mathcal{E}^{d'}\}$, $U_f^{d'} = \sup\{\mathbf{f}^Ty : y \in \mathcal{E}^{d'}\}$ (semidefinite programs), then

$$L_f^{d_f} \le L_f^{d_f+1} \le \dots \le L_f^{d} \le \Big\langle \frac{f}{s}\Big\rangle_\pi \le U_f^{d} \le \dots \le U_f^{d_f+1} \le U_f^{d_f} .$$

The bounds tighten as the order grows but need not converge to the true moment; they hold for every stationary solution, including networks with several.

## Expansion

Stationarity means $\langle Qh\rangle_\pi = 0$ for test functions $h$ whose generator image is $\pi$-integrable; with $h = x^\alpha$, finiteness of rational moments up to order $d+1$ justifies the exchange of sums (Fubini), and multiplying through by $s$ gives linear equations in $z$. Positivity of $\pi$ on $\mathbb{N}^n$ gives $\langle f^2/s\rangle_\pi \ge 0$ and $\langle x_i f^2/s\rangle_\pi \ge 0$ for every polynomial $f$, i.e. positive semidefinite moment and localizing matrices, and normalization gives $y^T\mathbf{s} = 1$. Since $M_d^i$ is a principal submatrix of $M_{d+1}^i$ and $\mathcal{E}^{d+1}$ contains all constraints of $\mathcal{E}^d$, the feasible sets shrink with $d$, which gives monotonicity. For Schlögl's model ($s = 1$, $d_b = 3$) the first moment equation and two $2\times2$ moment matrices already give analytic bounds.

## Sources

- Juan Kuntz, Philipp Thomas, Guy-Bart Stan and Mauricio Barahona, "Bounding the stationary distributions of the chemical master equation via mathematical programming", The Journal of Chemical Physics 151 (2019), 034109, <https://doi.org/10.1063/1.5100670>; numbering as in arXiv:1702.05468: Lemmas 3, 5, 14, Corollaries 6, 17 and Theorem 15.
