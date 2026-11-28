# Stability thresholds of the LPAA flour beetle model

**Model.** The LPAA model splits the adult class of the classical larva–pupa–adult (LPA) model of *Tribolium* into newly emerged (callow) adults $A_1$ and mature adults $A_2$. With a two-week time step,

$$\begin{aligned}
L(t+1)&=bA_2(t)e^{-c_1A_2(t)},\\
P(t+1)&=(1-\mu_l)L(t),\\
A_1(t+1)&=(1-\mu_p)P(t),\\
A_2(t+1)&=A_1(t)e^{-c_2A_2(t)}+(1-\mu_a)A_2(t),
\end{aligned}$$

where $b>0$ is fecundity, $\mu_l,\mu_p,\mu_a\in(0,1)$ are larval, pupal and adult mortalities, and $c_1,c_2>0$ measure cannibalism of eggs and of callow adults by mature adults. The inherent net reproductive number is

$$R_0=\frac{b(1-\mu_l)(1-\mu_p)}{\mu_a}.$$

**Theorem.**

1. The region $\Omega=\{L\le\hat L,\ P\le\hat P,\ A_1\le\hat A_1,\ A_2\le\hat A_1/\mu_a+A_2(0)\}$, with $\hat L=\frac{b}{ec_1}$, $\hat P=(1-\mu_l)\hat L$ and $\hat A_1=(1-\mu_p)\hat P$, is positively invariant.
2. The extinction equilibrium $E^0$ is locally and globally asymptotically stable if $R_0<1$, and unstable if $R_0>1$.
3. For $R_0>1$ there is a unique positive equilibrium $E^*$, with $A_2^*=\dfrac{\ln R_0}{c_1+c_2}$, $A_1^*=\mu_aA_2^*e^{c_2A_2^*}$, $L^*=bA_2^*e^{-c_1A_2^*}$ and $P^*=(1-\mu_l)L^*$. It is locally asymptotically stable when

$$1<R_0<\min\Big\{\exp\Big(1+\frac{c_2}{c_1}\Big),\ \exp\Big(\frac{1-\mu_a}{\mu_a}\Big(1+\frac{c_1}{c_2}\Big)\Big)\Big\}$$

and globally asymptotically stable when

$$1<R_0<\min\Big\{e,\ \frac{ec_1(1-\mu_a)}{c_2\mu_a}\Big\}.$$

Bifurcations of $E^*$ outside these ranges, and the resulting oscillatory and chaotic regimes, are explored numerically.

## Proof sketch

At $E^0$ the linearization is a non-negative projection matrix, and by Perron–Frobenius its dominant eigenvalue is below $1$ iff $R_0<1$. The full projection matrix is dominated entrywise by the inherent one, so a comparison argument upgrades local to global stability. At $E^*$ the balance $\mu_a=b(1-\mu_l)(1-\mu_p)e^{-(c_1+c_2)A_2^*}$ gives $A_2^*=\ln R_0/(c_1+c_2)$. Local stability follows the Cushing–Zhou argument for the LPA model: the Jacobian at $E^*$ is non-negative and primitive exactly when $A_2^*<1/c_1$ and $A_2^*<\frac{1-\mu_a}{c_2\mu_a}$, which translate into the stated bounds on $R_0$. The stronger condition gives global stability. Separating callow from mature adults reproduces the laboratory observation that chaos can be induced by manipulating adult mortality and recruitment. When fitted to new laboratory census data on *Tribolium confusum*, the LPA model gave biologically implausible parameters, while the LPAA model fitted better.

## Sources

- Samantha J. Brozak, Sophia Peralta, Tin Phan, John D. Nagy and Yang Kuang, "Dynamics of an LPAA Model for Tribolium Growth: Insights into Population Chaos", *SIAM Journal on Applied Mathematics* 84 (2024), 2300–2320, <https://doi.org/10.1137/24m1633881>. Preprint version: arXiv:2411.14603 (2024), Section 2 (LPAA model), Lemma 4.1 (invariant region), Theorem 5.1 (extinction equilibrium and $R_0$), Theorem 6.1 (local stability of the positive steady state), Theorem 7.1 (global stability), Section 8 (bifurcations), <https://doi.org/10.48550/arXiv.2411.14603>.
