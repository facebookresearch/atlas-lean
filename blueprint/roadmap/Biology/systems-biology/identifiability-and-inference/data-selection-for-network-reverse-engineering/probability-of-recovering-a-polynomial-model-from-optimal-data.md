# Probability of recovering a polynomial model from optimal data in finite-field reverse engineering

**Setting.** A time-discrete finite dynamical system on $n$ variables with values in a finite field $\mathbb{F}_q$ (e.g. discretised gene expression levels) has coordinate functions $f \in F_n(\mathbb{F}_q)$, the space of all functions $\mathbb{F}_q^n \to \mathbb{F}_q$. Every such function is a unique polynomial function in the *fundamental monomials* $g_\alpha(x) = x^\alpha$ with exponents $\alpha \in \{0, \dots, q-1\}^n$, so $d := \dim F_n(\mathbb{F}_q) = q^n$. Given $m$ distinct data points $X = (x_1, \dots, x_m)$, the evaluation map $\Phi_X(g) = (g(x_1), \dots, g(x_m))$ is a surjective linear map with $\dim\ker\Phi_X = d - m$. The Laubenbacher–Stigler algorithm returns the normal form of an interpolant modulo the ideal of the points; generalising away from term orders, one chooses an inner product making a basis $(u_1, \dots, u_s)$ of $\ker\Phi_X$ ($s = d-m$) together with $m$ fundamental monomials $u_{s+1}, \dots, u_d$ orthonormal, and returns the interpolant $g^*$ orthogonal to $\ker\Phi_X$.

**Optimal data.** A subspace $U$ of dimension $s$ is in *general position* with respect to the monomial basis if, for every basis $v_1, \dots, v_s$ of $U$ and every choice of $d - s$ distinct monomials, the $v_i$ and these monomials form a basis of $F_n(\mathbb{F}_q)$. A data set $X$ is *optimal* if $\ker\Phi_X$ is in general position.

**Theorem.** Let $X$ be an optimal set of $m < q^n$ distinct points, let $f \ne 0$ be a linear combination of exactly $t$ fundamental monomials, and let the $m$ monomials completing the kernel basis be chosen uniformly at random. Then the probability that the orthogonal interpolant of the data $b_i = f(x_i)$ equals $f$ is

$$P = \frac{\binom{q^n - t}{q^n - m}}{\binom{q^n}{m}} \quad (t \le m), \qquad P = 0 \quad (t > m).$$

In particular, recovering $f$ requires at least as many data points as $f$ has terms, and $f$ is recovered exactly when its support is contained in the chosen monomials. For $t \le m$, $P = \prod_{j=0}^{t-1}\frac{m-j}{q^n-j} \le r^t$ with $r = m/q^n$ the fraction of all states observed; for a fixed number of terms $t$ and a fixed fraction $r$, $P \to r^t$ as $n \to \infty$ (for $t = 1$, $P = r$ exactly), and for a fixed number $m$ of data points, $P \to 0$ as $n$ grows.

## Proof sketch

The orthogonal solution equals $f$ iff $f \in \mathrm{span}(u_{s+1}, \dots, u_d)$, i.e. iff every monomial of $f$ is among the $m$ completing monomials. General position guarantees that every $m$-subset of monomials completes the kernel basis, so the completing set is a uniformly random $m$-subset of $q^n$ monomials, and the probability that it contains the $t$ given monomials is $\binom{q^n - t}{m - t}/\binom{q^n}{m}$. Optimal sets can be built as the variety of a subspace in general position satisfying a codimension condition. Cancelling factorials gives the product form. Since $P$ is at most the observed fraction $r$ raised to the number of terms, even with optimal data and no term-order bias, exact reverse engineering from a small fraction of the state space succeeds only for models with very few terms, unless the model class is restricted in advance.

## Sources

- Edgar Delgado-Eckert, "Reverse Engineering Time Discrete Finite Dynamical Systems: A Feasible Undertaking?", *PLoS ONE* 4 (2009), e4939, <https://doi.org/10.1371/journal.pone.0004939>. Preprint version: arXiv:0706.3234 (2007), Section 3 (orthogonal solutions, general position, optimal data sets and the probability formula), <https://doi.org/10.48550/arXiv.0706.3234>.
