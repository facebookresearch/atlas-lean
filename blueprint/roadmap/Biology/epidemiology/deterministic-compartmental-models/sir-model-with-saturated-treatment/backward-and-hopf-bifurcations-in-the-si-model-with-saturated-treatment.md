# Backward and Hopf bifurcations in the SI model with saturated treatment

Consider the reduced SIR dynamics with recruitment $A>0$, natural death $d>0$, mass-action transmission $\beta>0$, and removal of infecteds by death, disease mortality and natural recovery at total rate $\delta=d+\alpha+n$. Add a saturating treatment term $bI/(I+b)$ with capacity parameter $b>0$:

$$
\dot S=A-dS-\beta IS,\qquad \dot I=\beta IS-\delta I-\frac{bI}{I+b}.
$$

Let

$$
R_0=\frac{\beta A}{d(\delta+1)}.
$$

The disease-free equilibrium is $E_0=(A/d,0)$. Endemic equilibria $X^*=(S^*,I^*)$ with $I^*>0$ correspond to positive roots of

$$
P(I)=\delta I^2+\Big(b(\delta+1)+\frac{\delta d}{\beta}-A\Big)I+\frac{bd(\delta+1)}{\beta}(1-R_0),
$$

with $S^*=\beta^{-1}\big(\delta+b/(I^*+b)\big)$. Then:

1. If $R_0>1$ there is exactly one endemic equilibrium.
2. If $R_0<\delta/(\delta+1)$ there is none.
3. If $\delta/(\delta+1)<R_0<1$: when $b>\frac{d}{\beta(\delta+1)}$ there is none; when $b<\frac{d}{\beta(\delta+1)}$ there are two, for $R_0$ close enough to $1$.
4. $E_0$ is a stable node for $R_0<1$ and a saddle for $R_0>1$.
5. At $R_0=1$, with $d>1/4$, the bifurcation is forward if $b>\frac{d}{(\delta+1)\beta}$ and backward if $b<\frac{d}{(\delta+1)\beta}$.
6. **Hopf.** Suppose $\frac{b(2\delta+1)}{2}<A$ and $\frac{d}{(\delta+1)\beta}<b$, and set $\Delta=A-\frac{b(2\delta+1)}{2}$ and $\beta_{\max}=\frac{(\delta+1)d}{\Delta}$. If $d\big(1+\frac{(\delta+1)b}{\Delta}\big)<\frac14$, the endemic equilibrium undergoes a Hopf bifurcation for some $\beta\in(\beta_0,\beta_{\max})$, equivalently for some $R_0\in(1,A/\Delta)$, where $\beta_0$ is the value with $R_0=1$.

So limited treatment capacity, meaning small $b$, can create bistability below $R_0=1$; with slow demography it can also produce sustained oscillations above threshold.

## Depends on

- [Basic reproduction number from the next-generation matrix](../../next-generation-matrix-and-the-basic-reproductio/r0.md)

## Proof sketch

Near $I=0$ the treatment term behaves like $I$, so the effective linear removal rate is $\delta+1$; this is why $\delta+1$ appears in $R_0$. Counting roots is Descartes' rule on $P$: the sign of $c_0$ is the sign of $1-R_0$, and $c_1<0$ is needed for two positive roots when $R_0<1$. The bifurcation direction is read off the slope of the endemic branch $I^*(R_0)$ at $R_0=1$. The Hopf condition comes from the trace of the Jacobian at $X^*$ changing sign while its determinant stays positive.

## Sources

- Arash Roostaei, Hadi Barzegar and Fakhteh Ghanbarnejad, "Emergence of Hopf bifurcation in an extended SIR dynamic", *PLOS ONE* 17 (2022), e0276969, <https://doi.org/10.1371/journal.pone.0276969>. Preprint version: arXiv:2107.10583 (2021), system (SIHR), Theorems 3.1–3.3, Corollary 3.1, Theorems 4.1, 5.1–5.3, <https://doi.org/10.48550/arXiv.2107.10583>.
