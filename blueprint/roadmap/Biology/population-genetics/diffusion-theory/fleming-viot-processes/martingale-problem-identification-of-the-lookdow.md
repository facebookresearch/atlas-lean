# The finite-type lookdown directing process solves the Fleming–Viot martingale problem

Let $E$ be nonempty and finite, and let $Z$ be the [common continuous directing process](common-directing-process-of-the-infinite-lookdow.md) of the shifting lookdown, with independent future clocks, conditionally iid initial types directed by $\mu_0$, and mutation matrix $Q=\frac\theta2(P-I)$. Let $L$ and $\mathcal A$ be the equivalent polynomial operators in the [finite-type Fleming–Viot/Wright–Fisher correspondence](finite-type-fleming-viot-k-allele-wright-fisher.md). For every polynomial $p$ on the simplex,

$$M_t^p=p(Z_t)-p(Z_0)-\int_0^t Lp(Z_s)\,ds$$

is a martingale for the natural filtration of $Z$. Equivalently, for each finite-input $f$, the compensated process for $F_f(\mu)=\langle f,\mu^{\otimes m}\rangle$ has compensator $\int_0^t\mathcal A F_f(Z_s)\,ds$. Thus the construction supplies a continuous-path solution with initial law that of $\mu_0$. Under parent-independent mutation, $p_{ab}=\nu_b$, the drift is exactly $\frac\theta2(\nu_b-z_b)$, with the stated pairwise resampling coefficient $1/2$.

## Finite empirical martingales

For the unordered population of size $N$, write $z$ for its empirical mass vector on the grid $\Delta_N$ and let $e_a$ denote coordinate unit vectors. Its empirical generator is

$$\begin{aligned}
G_Np(z)={}&\frac{N^2}{2}\sum_{a,b}z_az_b\left[p\left(z+\frac{e_b-e_a}{N}\right)-p(z)\right]\\
&+N\sum_{a\ne b}z_aq_{ab}\left[p\left(z+\frac{e_b-e_a}{N}\right)-p(z)\right].
\end{aligned}$$

A positive-rate transition lies in the simplex; zero-rate summands are harmless because $p$ is an ambient polynomial. The first term uses directed reproduction rate $1/2$, not one. The second term uses the off-diagonal mutation rates. This finite chain gives its compensated polynomial martingales. Since the ordered and unordered empirical **path laws** agree, the ordered $Z_N$ also has these martingale identities for its own natural filtration. They are not asserted for the entire ordered-level filtration.

Taylor expansion on the simplex yields

$$\sup_{z\in\Delta_N}|G_Np(z)-Lp(z)|\le\frac{C_p}{N}.$$

For an explicit bound, put $q_*=\max_a\sum_{b\ne a}q_{ab}$ and $H_r=\max_{|\alpha|=r}\sup_{z\in\Delta}|\partial^\alpha p(z)|$ for $r=2,3$. One may take $C_p=2q_*H_2+\frac23H_3$. The reproduction first-order term cancels by symmetry; its quadratic term is the Wright–Fisher covariance, and its third-order remainder has this bound. Mutation gives the linear drift and an order-$1/N$ quadratic remainder. Derivatives above the degree of $p$ are zero, so constants and linear polynomials are included. In particular the finite empirical drift agrees exactly on linear tests, while mutation can add finite-$N$ variance on quadratic tests.

## Passing to the limit in the correct filtration

Fix $0\le t_1,\ldots,t_r\le s\le t\le T$ and a bounded continuous function $H$ of the past empirical values. The finite-chain identity gives

$$\mathbb E\left[\left(p(Z_N(t))-p(Z_N(s))-\int_s^tG_Np(Z_N(u))\,du\right)H(Z_N(t_1),\ldots,Z_N(t_r))\right]=0.$$

Uniform almost-sure convergence of $Z_N$ on $[0,T]$, uniform generator convergence on $\Delta_N$, and boundedness on the compact simplex permit dominated convergence. The resulting identity has $Z$ and $L$ in place of $Z_N$ and $G_N$. A monotone-class argument on past cylinder functions proves the martingale property for the natural filtration of $Z$. Completion does not change it. One can use a countable family of monomials and rational-time cylinders before extending by continuity and linearity.

The finite-type operator correspondence identifies $LF_f=\mathcal A F_f$ and supplies the $C^2$ test-function extension when desired. A fixed-time de Finetti conditional identity alone would not justify conditioning on the whole past of the directing process; this proof does not make that inference or assume the stronger filtering identity.

## Depends on

- [A common continuous directing process for the finite-type lookdown](common-directing-process-of-the-infinite-lookdow.md)
- [Finite-type Fleming–Viot and Wright–Fisher martingale problems](finite-type-fleming-viot-k-allele-wright-fisher.md)

## Scope

This is existence and generator identification on a finite type space. Uniqueness in law, the function-valued duality argument, and any resulting Markov-family assertion remain separate. A proof page must still supply the finite-chain martingale, the uniform Taylor estimate and the passage to the limit with a monotone-class argument. The related lookdown overview states the martingale-problem scope; its broader well-posedness claim is not proved here.

## Sources

- M. Birkner, *Stochastic population models*, lecture notes, Johannes Gutenberg-Universität Mainz, 2025/26, <https://www.staff.uni-mainz.de/birkner/SPM2526/StochPopModels_25-26.pdf>, Sec. 1.5, unordered generator (1.26), Lemma 1.5.1, (1.42)–(1.43), the existence part of Theorem 1.5.8, and Remark 1.5.10. The finite-empirical martingale limit above supplies an alternative finite-type proof without importing the source's filtration projection as a consequence of fixed-time de Finetti alone.
