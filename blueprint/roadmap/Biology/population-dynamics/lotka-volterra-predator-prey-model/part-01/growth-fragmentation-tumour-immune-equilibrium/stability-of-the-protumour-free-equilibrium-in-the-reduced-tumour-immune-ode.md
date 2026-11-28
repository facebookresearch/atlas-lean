# Stability of the protumour-free equilibrium in the reduced tumour-immune ODE

**Model.** In the space-homogeneous reduction of the size-structured tumour-immune model with constant growth rate $V$, constant division rate $a>0$, activation $g(\mu_1)=\mu_1$, and constant source $S$, the tumour cell number $\mu_0$, tumour mass $\mu_1$, effector cells $c$, protumour cells $c_r$ and cytokines $I$ satisfy

$$
\begin{aligned}
\mu_0'&=\mu_0(a-\delta c), & \mu_1'&=V(1+b_1c_r)\mu_0-\delta\mu_1c,\\
c'&=\mu_1S-\gamma c-k_rcI-k_cc\,c_r, & c_r'&=k_rcI-\gamma_rc_r,\qquad I'=\psi(\mu_1)-\tau I,
\end{aligned}
$$

where $\psi(\mu_1)=\bar\psi(\mu_1-m)_+$ switches on cytokine production above a critical mass $m>0$, and all rates are positive.

**Statement.**

1. The healthy state $(0,0,0,0,0)$ is linearly unstable (its Jacobian has eigenvalue $a>0$).
2. The protumour-free equilibrium

$$
(\mu_0,\mu_1,c,c_r,I)^{NP}=\Bigl(\frac{\gamma a^2}{\delta VS},\ \frac{\gamma a}{\delta S},\ \frac{a}{\delta},\ 0,\ 0\Bigr)
$$

is admissible exactly when $\mu_1^{NP}\le m$, that is $a/\delta\le mS/\gamma$. Its characteristic polynomial is

$$
p(\lambda)=-(\gamma_r+\lambda)(\tau+\lambda)\bigl(\lambda^3+(\gamma+a)\lambda^2+2a\gamma\lambda+\gamma a^2\bigr),
$$

and whenever admissible with $\mu_1^{NP}<m$ it is linearly stable for all positive parameters.

## Depends on

- [Existence of small-tumour equilibrium phases in a size- and space-structured immune model](existence-of-small-tumour-equilibrium-phases-in-a-size-and-space-structured-immune-model.md)

## Proof depends on

- [Routh–Hurwitz criterion for cubic polynomials](../../../../../Analysis/control-theory/feedback-stability-and-classical-design/routh-hurwitz-criterion-for-cubic-polynomials.md)

## Expansion

At $NP$ cytokines vanish below threshold, so $c_r$ and $I$ decouple with eigenvalues $-\gamma_r$ and $-\tau$. The remaining cubic has positive coefficients and satisfies the Routh-Hurwitz inequality $(\gamma+a)\cdot 2a\gamma-\gamma a^2=\gamma a(2\gamma+a)>0$, so all roots lie in the left half-plane; the ratio $\gamma/a$ decides whether the approach is monotone or oscillatory. The effector level at equilibrium, $a/\delta$, is the per-capita kill that exactly offsets division, the ODE shadow of the eigenvalue balance in the structured model. Once $a/\delta$ exceeds $mS/\gamma$ the protumour-free state ceases to exist, cytokines switch on, and protumour cells can drive tumour escape.

## Sources

- Atsou K, Anjuère F, Braud VM, Goudon T. A size and space structured model of tumor growth describes a key role for protumor immune cells in breaking equilibrium states in tumorigenesis. *PLoS ONE* (2021) e0259291. <https://doi.org/10.1371/journal.pone.0259291>. PMCID: PMC8608488. Eqs. (11), (13), (16), equilibrium (NP) and the discussion of stability of equilibrium points.
