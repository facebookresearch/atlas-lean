# Stationary distribution of the reversible mutation–selection model for phase-variable genes

**Model.** A very large clonal bacterial population carries $\ell$ phase-variable genes, each in state $1$ or $2$ (for example ON/OFF), so a genotype is one of $2^\ell$ states and the population is described by the genotype distribution $\pi(n)$ in generation $n$. Each gene $i$ switches independently per generation by the reversible mutation matrix

$$T_i = \begin{pmatrix} 1 - p_i & p_i\\ q_i & 1 - q_i\end{pmatrix}, \qquad 0 < p_i, q_i < 1,$$

and $T = T_1\otimes\cdots\otimes T_\ell$ (Assumption 2.2). The pure mutation model is $\pi(n) = \pi(n-1)T$. With a fitness vector $\gamma = (\gamma^1,\dots,\gamma^{2^\ell})$ and $I_\gamma = \mathrm{diag}(\gamma)$, the mutation–selection model is

$$\pi_{\mathrm{sel}}(n) = \frac{\pi_{\mathrm{sel}}(n-1)\,T\,I_\gamma}{\gamma\cdot\pi_{\mathrm{sel}}(n-1)T}.$$

**Proposition.**

1. *Mutation only.* As $n\to\infty$, $\pi(n)$ converges, from any initial distribution, to the product $\pi^\infty = \pi^\infty_1\otimes\cdots\otimes\pi^\infty_\ell$ of single-gene stationary laws $\pi^\infty_i = \big(q_i/(p_i+q_i),\ p_i/(p_i+q_i)\big)$.
2. *Mutation and selection.* $\pi_{\mathrm{sel}}(n)$ converges for every initial distribution; the limit is unique if the selection map is a contraction in $\ell^1$ after some number of steps.
3. *Multiplicative fitness.* If $\gamma = \gamma_1\otimes\cdots\otimes\gamma_\ell$ (Assumption 2.3), there is a product-form stationary distribution $\pi^\infty_{\mathrm{sel}} = \pi^\infty_{\mathrm{sel},1}\otimes\cdots\otimes\pi^\infty_{\mathrm{sel},\ell}$ with, for $\gamma_i = (\gamma_i^1, \gamma_i^2)$ and $\Delta\gamma_i = \gamma_i^2 - \gamma_i^1$,

    $$\pi^{\infty,1}_{\mathrm{sel},i} = \frac{2\gamma_i^1 q_i}{(1-q_i)\Delta\gamma_i + \gamma_i^1(p_i+q_i) + \sqrt{(\gamma_i^1p_i + \gamma_i^2q_i)^2 + 2(\gamma_i^1p_i - \gamma_i^2q_i)\Delta\gamma_i + (\Delta\gamma_i)^2}},$$

    and $\pi^{\infty,2}_{\mathrm{sel},i} = 1 - \pi^{\infty,1}_{\mathrm{sel},i}$. For equal fitness ($\Delta\gamma_i = 0$) this reduces to the mutation-only value $q_i/(p_i+q_i)$.

## Proof depends on

- [Perron–Frobenius theorem for primitive nonnegative matrices](../../../../LinearAlgebra/special-matrices/perron-frobenius-theorem/perron-frobenius-for-primitive-nonnegative-matri.md)

## Expansion

Item 1 is the Perron–Frobenius theorem for the positive stochastic matrix $T_i$, combined with $T^n = T_1^n\otimes\cdots\otimes T_\ell^n$. Under selection the update is a normalized linear map, i.e. power iteration for the positive matrix $TI_\gamma$, so $\pi_{\mathrm{sel}}(n)$ converges to the normalized left Perron eigenvector of $TI_\gamma$. With multiplicative fitness, $TI_\gamma = \bigotimes_i T_iI_{\gamma_i}$ and its Perron vector is the tensor product of the single-gene Perron vectors. For one gene the fixed point $x = \pi^1$ satisfies a quadratic equation with leading coefficient $(p+q-1)\Delta\gamma$; its root in $(0,1)$, written in rationalized form, is the displayed formula. These explicit stationary laws are used to test whether observed ON/OFF frequencies of phase-variable genes are consistent with mutation alone, and fitness parameters are then fitted by approximate Bayesian computation.

## Sources

- C. D. Bayliss, C. Fallaize, R. Howitt and M. V. Tretyakov, "Mutation and Selection in Bacteria: Modelling and Calibration", *Bulletin of Mathematical Biology* 81 (2019), 639–675, <https://doi.org/10.1007/s11538-018-0529-9>. Numbering as in the preprint arXiv:1803.01767v2, <https://arxiv.org/abs/1803.01767v2>: Assumptions 2.2–2.3, Propositions 2.1–2.4 (limits of the mutation and mutation–selection models and the product-form stationary distribution) and Lemma A.1 (single gene).
