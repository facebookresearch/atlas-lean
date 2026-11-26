# Reduced next-generation operator of a size–condition structured population

**Setting.** Consider one zone of the size–condition transport–renewal model (size $l\in[l_0,l_m]$, condition $c\in[0,c_m]$, growth velocity $g$, condition drift $h$, mortality $\mu$, harvest effort $\bar q$ with selectivity $\sigma$, fecundity $\beta$ and recruit-condition law $\Pi$), with the environment frozen at $y^\ast$ and constant effort $\bar q$. Assume the extinction resource level $R^\circ$ is the unique root of $F(R^\circ,y^\ast)=0$ with $\partial_RF(R^\circ,y^\ast)<0$, and freeze every rate at $(x,R)=(0,R^\circ)$: $g^\circ,h^\circ,\mu^\circ,\beta^\circ,\Pi^\circ$ and $u^\circ=\bar q\,\sigma\,\eta(0,y^\ast)$, with $g^\circ\ge g_{\min}>0$.

For a newborn of condition $c_0$ let $(L(\tau;c_0),C(\tau;c_0))$ solve $\dot L=g^\circ(L,C)$, $\dot C=h^\circ(L,C)$, $L(0)=l_0$, $C(0)=c_0$, leaving the domain at time $\tau_{\max}(c_0)\le(l_m-l_0)/g_{\min}$, and let
$$\ell(\tau;c_0)=\exp\Big(-\int_0^\tau\big[\partial_lg^\circ+\partial_ch^\circ+\mu^\circ+u^\circ\big]\,(L(s),C(s))\,ds\Big)$$
be the density survival factor. The next-generation kernel and operator on $\mathcal V=L^1(\Omega_c)$ are
$$\mathscr K(c,c_0)=\int_0^{\tau_{\max}(c_0)}\beta^\circ(L,C)\,\Pi^\circ(c\mid L,C)\,\ell(\tau;c_0)\,d\tau,\qquad (\mathcal K\psi)(c)=\int_{\Omega_c}\mathscr K(c,c_0)\psi(c_0)\,dc_0 ,$$
and the reduced basic reproduction number is $\mathcal R_0(y^\ast,\bar q)=r(\mathcal K)$, the spectral radius.

**Theorem.** Assume the integrand of $\mathscr K$ is dominated by an integrable majorant and $\mathscr K\in C(\Omega_c\times\Omega_c)$.
1. $\mathcal K$ is bounded, positive and compact on $L^1(\Omega_c)$, and maps $L^1$ into $C(\Omega_c)$.
2. $r(\mathcal K)$ is an eigenvalue with an eigenfunction $\psi^\ast\ge 0$, $\psi^\ast\ne 0$ (Krein–Rutman).
3. $\mathcal R_0$ is nonincreasing in the harvest effort $\bar q$, nondecreasing in $\beta^\circ$ and nonincreasing in $\mu^\circ$.
4. If the frozen coefficients and $R^\circ$ depend continuously on $y^\ast$ in a compact set $\mathscr Y$ (with uniform domination), then $y^\ast\mapsto\mathcal R_0(y^\ast,\bar q)$ is continuous on $\mathscr Y$.
5. If in addition the linearization at extinction is $\dot z=(\mathcal A_0+\mathcal F)z$, with $\mathcal A_0$ resolvent-positive, $0\in\rho(\mathcal A_0)$, $\mathcal F$ the positive boundary-recruitment operator, $\mathcal A_0+\mathcal F$ generating a positive $C_0$-semigroup and $\mathcal K=-\mathcal F\mathcal A_0^{-1}$, then the spectral bound satisfies $\operatorname{sign} s(\mathcal A_0+\mathcal F)=\operatorname{sign}(\mathcal R_0-1)$. If moreover the nonlinear semiflow is Fréchet differentiable at $(0,R^\circ)$ with this linearization, then $\mathcal R_0<1$ gives local asymptotic stability of extinction and $\mathcal R_0>1$ gives linear instability.

## Expansion

$\mathscr K(c,c_0)$ is the expected density of offspring born with condition $c$ produced over the lifetime of one recruit born with condition $c_0$, obtained by integrating fecundity times survival along the characteristic curve. A continuous kernel on a compact square gives equicontinuity, hence compactness by Arzelà–Ascoli. More harvest or mortality shrinks $\ell$ and hence $\mathscr K$ pointwise, and the spectral radius is monotone on positive operators. Continuity in $y^\ast$ combines upper semicontinuity of $r(T)=\inf_p\|T^p\|^{1/p}$ with a Riesz-projection argument for lower semicontinuity. The threshold sign is the reproduction-number theorem for resolvent-positive operators; the paper takes the semigroup identity $\mathcal K=-\mathcal F\mathcal A_0^{-1}$ as a hypothesis rather than deriving it.

## Depends on

- [Well-posedness of the size–condition transport–renewal system with resource feedback](well-posedness-of-the-size-condition-transport-renewal-system-with-resource-feedback.md)

## Sources

- Jiguang Yu, Louis Shuo Wang and Ye Liang, "Rigorous Analysis of a Nonlocal Transport–Renewal System for Physiologically Structured Populations", arXiv:2609.00735 (2026), Section 4: Assumptions 4.1, 4.2, 4.6, 4.8, 4.11, Proposition 4.3, Definition 4.4, Theorems 4.5, 4.7, 4.10 and Proposition 4.12, <https://doi.org/10.48550/arXiv.2609.00735>.
