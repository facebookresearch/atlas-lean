# Race model inequality from the Fréchet–Hoeffding bounds

**Setting.** In a redundant-signals reaction-time experiment, $F_V$, $F_A$ and $F_{VA}$ denote the distribution functions of reaction time to a visual stimulus alone, an auditory stimulus alone, and both together. These come from different experimental conditions, so the unimodal reaction times $V$ and $A$ have no joint law a priori. A **coupling** of $V$ and $A$ is a random pair $(\hat V,\hat A)$ on one probability space with $\hat V\overset d=V$ and $\hat A\overset d=A$; let $\hat H_{VA}$ be its joint distribution function.

**Race model.** Assume a coupling exists and the bimodal response is triggered by whichever channel finishes first:

$$F_{VA}(t)=\mathbb P(\hat V\le t\ \text{or}\ \hat A\le t)=F_V(t)+F_A(t)-\hat H_{VA}(t,t).$$

**Theorem (race model inequality).** Under the race model, for all $t\ge0$,

$$\max\{F_V(t),F_A(t)\}\le F_{VA}(t)\le\min\{F_V(t)+F_A(t),\,1\}.$$

The upper bound is attained when $\hat V$ and $\hat A$ are countermonotone (maximal negative dependence) and the lower bound when they are comonotone (maximal positive dependence).

## Proof sketch

By Sklar's theorem $\hat H_{VA}(s,t)=C(F_V(s),F_A(t))$ for a copula $C$, unique when the margins are continuous. Every bivariate copula satisfies the Fréchet–Hoeffding bounds

$$W(u,v)=\max\{u+v-1,0\}\le C(u,v)\le\min\{u,v\}=M(u,v),$$

where $M$ is the law of $(U,U)$ and $W$ the law of $(U,1-U)$ for $U$ uniform on $[0,1]$. Taking the diagonal $s=t$ and substituting into $F_{VA}=F_V+F_A-\hat H_{VA}(t,t)$ turns the upper copula bound into the lower bound on $F_{VA}$ and the lower copula bound into the upper bound. An empirical violation of the upper bound at small $t$ (bimodal responses faster than any race could produce) is evidence against the race mechanism, or against the assumption that a coupling exists at all.

## Sources

- Hans Colonius, "An invitation to coupling and copulas: With applications to multisensory modeling", *Journal of Mathematical Psychology* 74 (2016), 2–10, <https://doi.org/10.1016/j.jmp.2016.02.004>. Preprint version: arXiv:1511.05303 (2015), Section 3.1 (Theorems 12 and 14), Section 3.5 (Example 16) and Section 4 (Example 20), <https://doi.org/10.48550/arXiv.1511.05303>.
