# Reproduction number under infection-blocking and disease-blocking vaccination

**Model.** In an SIR model with births and deaths (rates $\mu = \nu$, population normalized to one), a fraction $w$ of newborns receives a vaccine that blocks infection (whole-cell-type, entering $R$) and a fraction $a$ receives a vaccine that blocks disease but not infection (acellular-type, entering a vaccinated class $V$), with $w + a \le 1$. Unvaccinated susceptibles $S$ are infected at rate $\beta(I_s + I_a)$ and become symptomatic ($I_s$) with probability $\sigma$ or asymptomatic ($I_a$) otherwise; vaccinated individuals in $V$ are infected at the same rate but always asymptomatically. Symptomatic and asymptomatic infections are equally infectious and recover at rates $\gamma_s, \gamma_a$; immunity wanes at rate $\omega$:

$$\begin{aligned}
S' &= \mu(1 - w - a) - \beta(I_s + I_a)S + \omega R - \nu S,\\
I_s' &= \beta\sigma(I_s + I_a)S - (\gamma_s + \nu) I_s,\\
I_a' &= \beta(1 - \sigma)(I_s + I_a)S + \beta(I_s + I_a)V - (\gamma_a + \nu) I_a,\\
V' &= \mu a - \beta(I_s + I_a)V - \nu V,\\
R' &= \mu w + \gamma_s I_s + \gamma_a I_a - \omega R - \nu R .
\end{aligned}$$

**Proposition.** The infection-free equilibrium is

$$S^* = 1 - a - \frac{\nu w}{\omega + \nu}, \qquad V^* = a, \qquad R^* = \frac{\nu w}{\omega + \nu},$$

(so $S^* = 1 - w - a$, $R^* = w$ without waning), and the reproduction number of the vaccinated population is

$$R_v = \beta\left[\frac{\sigma S^*}{\gamma_s + \nu} + \frac{(1 - \sigma)S^* + V^*}{\gamma_a + \nu}\right].$$

In particular, if $\gamma_s = \gamma_a = \gamma$,

$$R_v = \frac{\beta\,(S^* + V^*)}{\gamma + \nu} = \frac{\beta}{\gamma + \nu}\left(1 - \frac{\nu w}{\omega + \nu}\right),$$

so disease-blocking vaccination ($a$) does not reduce transmission at all: it converts symptomatic infections into asymptomatic ones, while only infection-blocking vaccination ($w$) lowers $R_v$. The infection-free equilibrium is locally asymptotically stable if $R_v < 1$ and unstable if $R_v > 1$.

## Depends on

- [Basic reproduction number of the next-generation matrix](../../next-generation-matrix-and-the-basic-reproductio/r0.md)

## Expansion

With $\nu = \mu$ the infection-free equilibrium follows by setting $I_s = I_a = 0$: the $V$ equation gives $V^* = a$, the $R$ equation gives $R^* = \nu w/(\omega + \nu)$, and the $S$ equation gives $S^* = (1 - w - a) + \omega R^*/\nu$, which simplifies to the stated value; the three sum to one. For the infected compartments $(I_s, I_a)$ the new-infection matrix is

$$F = \beta\begin{pmatrix} \sigma S^* & \sigma S^* \\ (1-\sigma)S^* + V^* & (1-\sigma)S^* + V^* \end{pmatrix}, \qquad V_{\text{tr}} = \operatorname{diag}(\gamma_s + \nu,\ \gamma_a + \nu),$$

and $F V_{\text{tr}}^{-1}$ has identical columns up to scaling, so it has rank one and its spectral radius is its trace, which gives $R_v$. With equal recovery rates the bracket becomes $(S^* + V^*)/(\gamma + \nu)$, and $S^* + V^* = 1 - \nu w/(\omega + \nu)$ does not involve $a$. The model explains how replacing an infection-blocking vaccine by a disease-blocking one can permit resurgence driven by unobserved asymptomatic transmission.

## Sources

- Althouse BM, Scarpino SV, "Asymptomatic transmission and the resurgence of Bordetella pertussis" (2015), Methods, "The model", Equations (1)–(5); the reproduction number is derived here from those equations by the next-generation method, <https://doi.org/10.1186/s12916-015-0382-8>, PMCID PMC4482312.
