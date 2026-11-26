# Prevalence PDE of the illness–death model with migration

**Model.** In the illness–death model, healthy people get the disease with incidence $i$, recover with remission rate $r$, and die with mortality $m_0$ if healthy and $m_1$ if diseased. All rates depend on age $a$ and calendar time $t$ but not on disease duration. Let $S(t,a)$ and $C(t,a)$ be the numbers of non-diseased and diseased persons aged $a$ at time $t$, with $N=S+C$. Net migration contributes $\sigma N$ non-diseased and $\gamma N$ diseased persons per unit time, so that

$$\Big(\frac{\partial}{\partial t}+\frac{\partial}{\partial a}\Big)S=\sigma N-(i+m_0)S+rC,\qquad \Big(\frac{\partial}{\partial t}+\frac{\partial}{\partial a}\Big)C=\gamma N+iS-(m_1+r)C .$$

**Theorem.** On $D=\{(t,a):S,C\ge0,\ S+C>0\}$, the age-specific prevalence $p=C/(S+C)$ is partially differentiable and satisfies

$$\Big(\frac{\partial}{\partial a}+\frac{\partial}{\partial t}\Big)p=(1-p)\big[i-p\,(m_1-m_0)\big]-r\,p+\mu,\qquad \mu:=\gamma(1-p)-\sigma p .$$

Conversely, $p$ solves this PDE iff $S=(1-p)N$ and $C=pN$ solve the system, so $p\in[0,1]$ on $D$. Decompose migration into immigration and emigration, $f=f_+-f_-$ for $f\in\{\varphi,\sigma,\gamma\}$ with $\varphi=\sigma+\gamma$. Let $p^{(m)}_\pm=\gamma_\pm/\varphi_\pm$ be the prevalences among immigrants and emigrants. Then

$$\mu=\varphi_+\big(p^{(m)}_+-p\big)-\varphi_-\big(p^{(m)}_--p\big)\quad\text{when }\varphi_+,\varphi_->0,$$

with the obvious one-sided forms when only immigration or only emigration occurs, and $\mu=0$ without migration. In particular, migration changes prevalence only insofar as migrants' prevalence differs from the resident prevalence $p$.

Two cases are worth recording.

- Without migration and calendar-time effects the PDE reduces to the ODE $p'(a)=(1-p)\big[i-p(m_1-m_0)\big]-rp$ along age.
- For an irreversible disease ($r=0$) it can be solved for incidence, $i=\frac{(\partial_a+\partial_t)p-\mu}{1-p}+p\,(m_1-m_0)$. This expresses incidence through prevalence, the mortality difference and migration, as used to estimate incidence from cross-sectional prevalence data. The inverse problem is ill-posed.

## Expansion

Differentiate $p=C/N$ along the characteristic direction $\partial_t+\partial_a$, which follows a birth cohort:

$$(\partial_t+\partial_a)p=\frac{(\partial_t+\partial_a)C}{N}-p\,\frac{(\partial_t+\partial_a)N}{N} .$$

Here $(\partial_t+\partial_a)N=\varphi N-m_0S-m_1C$. Substituting and collecting terms gives $\gamma+i(1-p)-(m_1+r)p-p\big[\varphi-m_0(1-p)-m_1p\big]$, which rearranges to the stated right-hand side. The migration term follows from $\gamma=\gamma_+-\gamma_-=\varphi_+p^{(m)}_+-\varphi_-p^{(m)}_-$ and $\sigma=\varphi-\gamma$. The forward problem (rates to prevalence) is a first-order Riccati-type PDE in $p$, solved along characteristics from the age-0 and time-0 boundary data. The source illustrates both the forward and the inverse problem on a simulated register of a chronic disease.

These are the main theorem, the equivalence theorem and the migration proposition of Section 2 of the source.

## Sources

- R. Brinks, "On the age-, time- and migration dependent dynamics of diseases", arXiv:1209.1371 (2012). <https://doi.org/10.48550/arXiv.1209.1371>
