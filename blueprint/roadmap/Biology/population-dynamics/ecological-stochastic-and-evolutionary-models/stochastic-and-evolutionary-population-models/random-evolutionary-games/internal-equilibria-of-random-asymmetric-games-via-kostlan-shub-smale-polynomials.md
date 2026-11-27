# Number of internal equilibria of random asymmetric multiplayer games via Kostlan–Shub–Smale polynomials

**Setting.** An infinite population plays $d$-player games with $n$ strategies at frequencies $x_1,\dots,x_n$. The focal player using strategy $i_0$ against the ordered group $(i_1,\dots,i_{d-1})$ receives payoff $\alpha^{i_0}_{i_1,\dots,i_{d-1}}$, so its fitness is $\pi_{i_0} = \sum \alpha^{i_0}_{i_1,\dots,i_{d-1}}x_{i_1}\cdots x_{i_{d-1}}$, and the replicator dynamics are $\dot x_i = x_i(\pi_i - \langle\pi\rangle)$. The game is *asymmetric* when payoffs depend on the order of co-players, so that the aggregated payoff differences $\beta^i_{k_1,\dots,k_{n-1}}$ (between strategy $i$ and strategy $n$, for co-player compositions $(k_1,\dots,k_{n-1})$) are independent. An internal equilibrium is a rest point with all $x_i \in (0,1)$; after the substitution $y_i = x_i/x_n$, internal equilibria are the positive common roots of

$$\sum_{k_1+\dots+k_{n-1}\le d-1}\beta^i_{k_1,\dots,k_{n-1}}\binom{d-1}{k_1,\dots,k_{n-1}}y_1^{k_1}\cdots y_{n-1}^{k_{n-1}} = 0,\qquad i = 1,\dots,n-1.$$

With i.i.d. Gaussian $\beta$'s these form exactly a Kostlan–Shub–Smale (elliptic) system of random polynomials of degree $d-1$ in $n-1$ variables. Let $\mathcal{N}_{d,n}$ be the number of internal equilibria.

**Theorem.** Let the $\beta^i_{k}$ be i.i.d. standard Gaussian.
1. (Mean.) $\mathbb{E}(\mathcal{N}_{d,n}) = 2^{-(n-1)}(d-1)^{(n-1)/2}$.
2. (Variance and CLT.) $\lim_{d\to\infty} 4^{n-1}\operatorname{Var}(\mathcal{N}_{d,n})/(d-1)^{(n-1)/2} = V_\infty^2$ for an explicit $0 < V_\infty < \infty$, and $\big(4^{n-1}\mathcal{N}_{d,n} - (d-1)^{(n-1)/2}\big)/(d-1)^{(n-1)/4}$ converges in distribution to a centered normal law with positive variance.
3. (Distribution, $n = 2$.) If the coefficients have a joint density, the probability $p_m$ of exactly $m$ internal equilibria ($0 \le m \le d-1$) is an explicit sum over the numbers of complex-conjugate and negative roots of integrals of the joint density.
4. (Universality, $n = 2$.) If the underlying coefficients are independent with mean $0$, variance $1$ and finite $(2+\varepsilon)$-moment, then $\mathbb{E}(\mathcal{N}_{d,2}) = \tfrac12\sqrt{d-1} + O\big((d-1)^{1/2 - c}\big)$ for some $c = c(\varepsilon) > 0$.
5. (Symmetry increases diversity.) For random polynomials $\sum_{i=0}^m a_i\xi_i x^i$ with symmetric coefficients $a_i = a_{m-i}$ and $\sum a_i^2 x^i$ real-rooted, the expected number of positive roots is at least $\sqrt m/2$, with equality for $a_i = \sqrt{\binom mi}$. Hence random symmetric two-strategy $d$-player games, for which $\mathbb{E}(\mathcal{N}^{\mathrm{sym}}_{d,2}) \sim \sqrt{(d-1)/2}$, have at least as many internal equilibria on average as asymmetric ones.

## Expansion

The multinomial weights $\binom{d-1}{k}$ multiplying independent Gaussian coefficients are exactly the Kostlan–Shub–Smale variances, whose distribution is invariant under orthogonal changes of variables on projective space. Kac–Rice formulas then give the expected number of real roots of the system, $(d-1)^{(n-1)/2}$ (Shub–Smale), and the positivity constraint keeps a $2^{-(n-1)}$ fraction by symmetry under $y_i \mapsto -y_i$. Variance asymptotics and the CLT are imported from results of Armentano, Azaïs, Dalmao and León on real zeros of Kostlan–Shub–Smale systems, the root-count distribution from a general formula for the joint density of zeros of random polynomials, and universality from Tao–Vu. Biologically, the number of internal equilibria measures the potential for stable coexistence of strategies, i.e. behavioral or biological diversity.

## Sources

- Manh Hong Duong and The Anh Han, "Random evolutionary games and random polynomials", Proceedings of the Royal Society A: Mathematical, Physical and Engineering Sciences 481 (2025), 20240911, <https://doi.org/10.1098/rspa.2024.0911>; numbering as in arXiv:2304.13831: Section 2 (replicator equations and the polynomial system), Theorems 3.1–3.4 (Section 3), Theorem 4.1 (Section 4).
