# Lieb–Oxford inequality

The indirect Coulomb energy of any $N$-particle state with a Lebesgue density is bounded below by $-1.58\int\rho^{4/3}$; $1.58$ is an admissible constant, and the best constant is known to exceed $1.44$.

Let $N\ge1$ and let $\mathbb P$ be a symmetric probability measure on $(\mathbb R^3)^N$ whose one-particle marginal satisfies $N(\pi_1)_\#\mathbb P=\rho\,dx$ for a function $\rho\in L^1\cap L^{4/3}(\mathbb R^3)$ with finite direct term $D(\rho)=\frac12\iint\rho(x)\rho(y)|x-y|^{-1}dx\,dy$. Its indirect energy is

$$
\mathcal E_{\mathrm{ind}}[\mathbb P]=\int\sum_{1\le j<k\le N}\frac{1}{|x_j-x_k|}\,d\mathbb P(x_1,\dots,x_N)-D(\rho)\in(-\infty,+\infty],
$$

where the pair integral may be $+\infty$. Then

$$
\mathcal E_{\mathrm{ind}}[\mathbb P]\ge-1.58\int_{\mathbb R^3}\rho(x)^{4/3}\,dx .
$$

It applies to quantum states through $\mathbb P=\sum_{\sigma}|\Psi(x_1,\sigma_1,\dots,x_N,\sigma_N)|^2dx$. Equivalently the best constant $c_{\mathrm{LO}}$ satisfies $c_{\mathrm{LO}}\le1.58$; it also satisfies $c_{\mathrm{LO}}\ge1.44$. Lieb first proved such a bound with constant $8.52$ (1979), and Lieb and Oxford improved it to $1.68$ (1981).

## Context

Research (established). The inequality is an exact constraint built into non-empirical exchange-correlation functionals such as PBE and SCAN. Determining the optimal constant is a separate open problem, recorded on the page of the optimal Lieb–Oxford constant in this field.

## Depends on

None.

## Proof depends on

None.

## Expansion

Lewin, Lieb and Seiringer bound the indirect energy at fixed density (their Eq. (3) infimum) by $-\mathcal K(\mu,\nu)\int\rho^{4/3}$ for every pair of radial probability measures $\mu,\nu$ with finite self-energy $D(\mu,\mu)<\infty$ (their Theorem 1, Eq. (26), with $\mathcal K(\mu,\nu)=\frac32(2I(\mu,\nu)D(\mu,\mu)^2)^{1/3}$; $\mu=\delta_0$ is excluded): smear the point charges by $\mu$, apply Onsager's electrostatic lemma, control the smearing error with $\nu$, and optimize locally in the density, giving $c_{\mathrm{LO}}\le\inf_{\mu,\nu}\mathcal K(\mu,\nu)$ over that class (their Eqs. (8) and (26)). In §5 they evaluate $\mathcal K$ at explicit trial measures with rigorous error control, obtaining $c_{\mathrm{LO}}\le1.5765$ (their Eq. (79)); no global optimality of the trial data is needed. Missing prerequisites on the graph: Onsager's lemma, the potential theory of radial charge distributions and the verified numerical evaluation.

## Sources

- Mathieu Lewin, Elliott H. Lieb and Robert Seiringer, *Improved Lieb-Oxford bound on the indirect and exchange energies*, Lett. Math. Phys. (2022); numbers from arXiv:2203.12473v3, §1, Eqs. (1)–(4), (7) and (8), Theorem 1, Eq. (26), and §5, Eq. (79). <https://arxiv.org/abs/2203.12473v3>
- Elliott H. Lieb, *A lower bound for Coulomb energies*, Phys. Lett. A 70 (1979) 444–446 (constant 8.52), and Elliott H. Lieb and Stephen Oxford, *Improved lower bound on the indirect Coulomb energy*, Int. J. Quantum Chem. 19 (1981) 427–439 (constant 1.68), as cited in the preceding source and in Lieb's publication list. [web.math.princeton.edu/~lieb/publications.html](https://web.math.princeton.edu/~lieb/publications.html)
