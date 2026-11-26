# Endemic equilibrium of an SVIR model with a vaccine-unwilling fraction

**Setting.** A constant population (normalized to $1$) with birth and death rate $\mu$ is born willing to be vaccinated with probability $W$ and unwilling with probability $U=1-W$. Susceptibles $S=S_W+S_U$ (willing and unwilling), vaccinated $V$, unvaccinated infectives $I$, vaccinated infectives $I_V$ and removed $R$ evolve by

$$\begin{aligned}
\dot I&=-(\gamma+\mu)I+\beta S\hat I, & \dot I_V&=-(\alpha\gamma+\mu)I_V+\sigma\beta V\hat I,\\
\dot S&=\mu-\mu S-\phi S_W-\beta S\hat I, & \dot V&=\phi S_W-\mu V-\sigma\beta V\hat I,\\
\dot S_W&=\mu W-(\phi+\mu)S_W-\beta S_W\hat I, & \hat I&=I+\eta I_V,
\end{aligned}$$

where vaccination (rate $\phi$) acts only on willing susceptibles, and the imperfect vaccine multiplies infection risk by $\sigma\le1$ and infectiousness by $\eta\le1$ and speeds recovery by $\alpha\ge1$. Let

$$\mathcal R_0=\frac{\beta}{\gamma+\mu},\qquad \xi=\frac{\sigma\eta}{\alpha},\qquad \epsilon=\frac{\mu}{\gamma+\mu}\ll1,\qquad \theta=\frac{\phi}{\gamma+\mu},$$

and work in the endemic scaling (time $\mu t$, with $I=\epsilon Y$, $\eta I_V=\epsilon X$, $\mathcal R_0\hat I=\epsilon Z$, $\theta S_W=\epsilon P$), with the simplifying assumption $\alpha\sigma=1$ in the stability argument.

**Statement.**

1. The vaccine reproduction number is

$$\mathcal R_v=\mathcal R_0\Bigl[1-\frac{W}{1-\epsilon\theta^{-1}}+\frac{\xi W}{(1-\epsilon\theta^{-1})(1-\epsilon a)}\Bigr]\ \sim\ \mathcal R_0\,(U+\xi W)\qquad(\epsilon\to0),\quad a=1-\alpha^{-1},$$

and the disease-free equilibrium is asymptotically stable if and only if $\mathcal R_v<1$.
2. There is a unique, asymptotically stable endemic equilibrium if and only if $\mathcal R_v>1$. To leading order in $\epsilon$ it is

$$P=W,\qquad Z=\frac{\mathcal R_v-1}{\sigma+(1-\sigma)\mathcal R_0 S},\qquad V=\frac{W}{1+\sigma Z},\qquad Y=SZ,\qquad X=\xi VZ,$$

where $S$ is the unique root in $0\le S\le U/\mathcal R_v$ of

$$(U-S)\bigl[\sigma+(1-\sigma)\mathcal R_0S\bigr]=(\mathcal R_v-1)\,S ,$$

and the equilibrium rate of new infections is $1-S-V$.
3. Neither $\mathcal R_v$ nor the endemic state depends on the vaccination rate $\theta$ at leading order, so the effect of unwillingness cannot be reproduced by applying a reduced vaccination rate to all susceptibles.

## Depends on

- [Next-generation matrix and the basic reproduction number](../next-generation-matrix-and-the-basic-reproductio/README.md)

## Expansion

At the disease-free state $X=Y=0$, $V=P=W/(1-\epsilon\theta^{-1})$ and $S=1-P$. The Jacobian is block triangular; the susceptible block has negative diagonal, and the infection block equals $\hat F-\hat V$, whose next-generation matrix $\hat F\hat V^{-1}$ has rank one, so its spectral radius is its trace $\mathcal R_0[S+\xi V/(1-\epsilon a)]$. Its determinant is a positive multiple of $1-\mathcal R_v$, and substituting the inequality $\mathcal R_v<1$ into the trace shows the trace condition is then automatic. At an endemic state the infective equations give $Y=SZ$ and $X\approx\xi VZ$, hence $\mathcal R_0S+\xi\mathcal R_0V\approx1$; with $S(1+Z)=U$ and $V(1+\sigma Z)=W$ this yields $[\sigma+(1-\sigma)\mathcal R_0S]Z=\mathcal R_v-1$, so an endemic state needs $\mathcal R_v>1$, and eliminating $Z$ gives the quadratic for $S$. Since $\mathcal R_0S\le1$ the bracket is at most $1$, giving $S\le U/\mathcal R_v$ and a unique admissible root. Stability uses a simplified form of the four-variable Routh-Hurwitz conditions applied to the leading-order Jacobian.

## Sources

- Glenn Ledder, "The Impact of Neglecting Vaccine Unwillingness in Epidemiology Models", arXiv:2603.05626 (2026), Theorem 1 and Theorem 2, and Section "Endemic Analysis", <https://doi.org/10.48550/arXiv.2603.05626>
