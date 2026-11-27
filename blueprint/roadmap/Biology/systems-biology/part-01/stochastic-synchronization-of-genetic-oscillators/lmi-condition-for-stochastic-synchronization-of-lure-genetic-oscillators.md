# LMI condition for stochastic synchronization of Lur'e genetic oscillators

**Network.** Consider $N$ coupled oscillators $x_i \in \mathbb R^n$,

$$dx_i = \Big[F(x_i) + \sum_{j=1}^N G_{ij} D x_j\Big]dt + v_i(t)\,dw_i(t),\qquad i = 1,\dots,N, \tag{1}$$

with inner coupling matrix $D \in \mathbb R^{n\times n}$, coupling matrix $G$ with $G_{ij} \ge 0$ for $i \ne j$ and $G_{ii} = -\sum_{j\ne i} G_{ij}$, noise intensities $v_i \in L^2[0,\infty)$ and independent scalar Wiener processes $w_i$. Let $U$ be a symmetric combination matrix with zero row sums and nonpositive off-diagonal entries, and $\|z\|_{E_2}^2 = \mathbb E\int_0^\infty |z|^2\,dt$.

**Definition.** For $\gamma > 0$, network (1) is stochastically synchronous with disturbance attenuation $\gamma$ if it synchronizes asymptotically when $v_i \equiv 0$, and, from identical initial conditions,

$$\sum_{i<j}(-U_{ij})\,\|x_i - x_j\|_{E_2}^2 < \gamma \sum_i \|v_i\|_2^2 \quad \text{for all nonzero } v. \tag{2}$$

**General condition.** If there are $P > 0$, $T \in \mathbb R^{n\times n}$ and $\rho > 0$ with

$$2(y_1-y_2)^{\mathsf T}P\big[F(y_1) - F(y_2) - T(y_1-y_2)\big] + \frac{\rho}{\gamma}|y_1-y_2|^2 < 0\quad (y_1 \ne y_2),$$

$$(U\otimes P)(G\otimes D + I\otimes T) + (G\otimes D + I\otimes T)^{\mathsf T}(U\otimes P) \le 0,\qquad U\otimes P \le \rho I, \tag{3}$$

then (1) is stochastically synchronous with attenuation $\gamma$.

**Proposition (Lur'e oscillators).** Suppose each oscillator has the form

$$\dot y = Ay + B_1 f(y) - B_2 g(y) + B_2, \tag{5}$$

where $f_i(y_i) = (y_i/\beta_{1i})^{H_{1i}}/(1 + (y_i/\beta_{1i})^{H_{1i}})$ and $g_i = 1 - 1/(1 + (y_i/\beta_{2i})^{H_{2i}})$ are Hill functions, so that the sector conditions $0 \le \frac{f_i(a)-f_i(b)}{a-b} \le k_{1i}$ and $0 \le \frac{g_i(a)-g_i(b)}{a-b} \le k_{2i}$ hold; put $K_l = \mathrm{diag}(k_{l1},\dots,k_{ln})$. If there are $P > 0$, diagonal $\Lambda_1,\Lambda_2 > 0$, $Q \in \mathbb R^{n\times n}$ and $\rho > 0$ with

$$\begin{bmatrix} PA + A^{\mathsf T}P - Q - Q^{\mathsf T} + \frac{\rho}{\gamma}I & PB_1 + K_1\Lambda_1 & -PB_2 + K_2\Lambda_2\\ B_1^{\mathsf T}P + K_1\Lambda_1 & -2\Lambda_1 & 0\\ -B_2^{\mathsf T}P + K_2\Lambda_2 & 0 & -2\Lambda_2\end{bmatrix} < 0,$$

$$(UG\otimes PD + U\otimes Q)^{\mathsf T} + (UG\otimes PD + U\otimes Q) \le 0,\qquad U\otimes P \le \rho I, \tag{8}$$

then the noisy network of oscillators (5) is stochastically synchronous with attenuation $\gamma$. For fixed $U$ these are linear matrix inequalities.

## Expansion

With $V(x) = x^{\mathsf T}(U\otimes P)x$ and Itô's formula, the zero-row-sum structure of $U$ rewrites the drift term as $\sum_{i<j}(-U_{ij})\,2(x_i-x_j)^{\mathsf T}P(F(x_i)-F(x_j))$ plus the coupling term, while the Itô correction is bounded by $\rho\sum_i|v_i|^2$ through $U\otimes P \le \rho I$; conditions (3) then make $\mathbb E\int_0^t\big[\sum_{i<j}(-U_{ij})|x_i-x_j|^2 - \gamma\sum_i|v_i|^2\big]ds \le \mathbb E V(x(0)) = 0$. For Lur'e oscillators, choosing $Q = PT$ and adding the S-procedure terms $-2\sum_i \lambda_{li}\Delta f_i(\Delta f_i - k_{li}\Delta y_i) \ge 0$ from the sector conditions turns the nonlinear first inequality of (3) into the first LMI of (8). Because $\gamma$ enters linearly, minimizing $\gamma$ subject to (8) gives a design rule for coupling strength and topology that best attenuates noise; mean-square synchronization is generally not achievable under persistent additive noise, which motivates the attenuation definition.

## Sources

- C. Li, L. Chen, K. Aihara, "Stochastic synchronization of genetic oscillator networks", BMC Systems Biology 1:6 (2007), Eqs (1)–(8), Definition 1, Proposition 1 and Appendices C–D, <https://doi.org/10.1186/1752-0509-1-6>, PMCID PMC1839896.
