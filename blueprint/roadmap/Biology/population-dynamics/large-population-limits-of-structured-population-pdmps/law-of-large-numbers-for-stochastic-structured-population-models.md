# Law of large numbers for stochastic structured population models

Let $E$ be a separable, metrizable, locally compact space with a continuous flow $\varphi_t$ (individual dynamics), lifted to finite measures by $\phi_t(m) = \varphi_t \sharp m$. A stochastic structured population model is the piecewise-deterministic Markov process $\nu_t$ on finite measures $\mathcal{M}_F(E)$ that follows $\phi_t$ between jumps and jumps according to

$$ \mu(m, dm') = \int_E m(dx) \sum_i \alpha_i(m,x)\, \delta_{m + k_i(m,x)}(dm') , $$

where $\alpha_i(m,x) \ge 0$ is the rate of event type $i$ for individual $x$ in population $m$ and $k_i(m,x)$ is a signed finite measure (the change it causes).

**Mass control.** If the jump sizes are uniformly bounded in total variation and every population-increasing rate satisfies $q_i(m) \le C_q(1 + \langle m, 1\rangle)$, and $\mathbb{E}\langle\nu_0,1\rangle^p < \infty$ for some $p \ge 1$, then the process is defined for all times and $\mathbb{E}\langle \nu_t, 1\rangle^p \le C e^{Ct}$.

**Law of large numbers.** Let $\nu^n$ have rates and kernels scaled by $\alpha^{(n)}_i(nm,x) = \alpha_i(m,x)$ and $k^{(n)}_i(nm,x) = k_i(m,x)$, where the $\alpha_i k_i$ are locally Lipschitz in $m$ for the total variation norm, the $\alpha_i$ are locally bounded, and the total rate satisfies $q(m) \le C'(1 + \langle m,1\rangle + \langle m,1\rangle^2)$. Suppose $\sup_n \mathbb{E}\langle X^n_0,1\rangle^p<\infty$ for some $p \ge 3$, that $X^n_0 = \nu^n_0/n \to \xi_0$ in probability, and that the domain of the flow generator $A_\varphi$ is dense in $C_0(E)$. Then $X^n_t = \nu^n_t / n$ converges in probability in the Skorokhod space $\mathbb{D}([0,T], \mathcal{M}_F(E))$ to the unique deterministic continuous solution $\xi_t$ of

$$ \frac{d}{dt}\langle \xi_t, h\rangle = \big\langle \xi_t, \partial_t h + A_\varphi h \big\rangle + \sum_i \int \xi_t(dx)\, \alpha_i(\xi_t, x)\, \langle h(t,\cdot), k_i(\xi_t, x, \cdot)\rangle $$

for all test functions $h(t,x)$ that are $C^1$ in $t$ and in the domain of $A_\varphi$ in $x$.

## Expansion

The moment bound uses a Gronwall argument on $\langle\nu_t,1\rangle^p$ together with the fact that each jump changes the mass by at most a constant. The limit theorem follows the classical three-step route: tightness of $X^n$ from the martingale decomposition of $\langle X^n_t,h\rangle$, whose quadratic variation is of order $1/n$; identification of every limit point as a solution of the weak equation; and uniqueness of that equation from the total-variation Lipschitz bound via Gronwall. In the SIR example $E$ is a finite set of compartments and the limit is the Kermack–McKendrick system; with an age variable the flow is $\varphi_t(a) = a + t$.

## Sources

- P. Carmona, "Some deterministic structured population models which are limit of stochastic individual based models", arXiv:1804.04913 (2018), Section 2 (definitions and Definition 2.1), Section 3 (Assumptions 1–2, Proposition 3.2 and Theorem 3.4) and Section 5 (proofs, Proposition 5.1 on uniqueness). <https://doi.org/10.48550/arXiv.1804.04913>
