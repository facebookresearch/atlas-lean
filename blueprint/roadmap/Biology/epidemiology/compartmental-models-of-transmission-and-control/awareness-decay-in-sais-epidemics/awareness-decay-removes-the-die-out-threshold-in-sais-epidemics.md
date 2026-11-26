# Awareness decay removes the die-out threshold in SAIS epidemics

**Model.** On a $k$-regular random network, individuals are susceptible ($s$), aware ($a$) or infectious ($i=1-s-a$). Infectious individuals recover at rate $\delta$; susceptibles are infected at per-node rate $\beta$ and become aware at rate $\kappa$ through contact with infectious neighbours; aware individuals are infected at the reduced rate $\beta_a<\beta$ and lose awareness at rate $\delta_a$. The mean-field system on regular random networks (with $\beta,\kappa,\beta_a$ per-node rates, $k$ times the per-contact rates) is

$$\dot s=(1-s-a)\bigl(\delta-(\kappa+\beta)s\bigr)+\delta_aa,\qquad \dot a=(1-s-a)(\kappa s-\beta_aa)-\delta_aa,$$

on the triangle $R=\{s,a\ge0,\ s+a\le1\}$, whose edge $L=\{s+a=1\}$ consists of disease-free states.

**Theorem (no awareness decay, $\delta_a=0$).**
1. If $\beta\le\delta$, every trajectory ends at a point of $L$, with $s+a$ increasing to $1$.
2. If $\beta_a<\delta<\beta$, the point $s_0^*=\frac{\delta-\beta_a}{\beta-\beta_a}$ splits $L$ into a continuum of unstable equilibria ($s\ge s_0^*$) and a continuum of locally stable ones. If $\kappa\ge\kappa^*=\frac{\beta_a(\beta-\delta)}{\delta-\beta_a}$, all trajectories die out onto the stable part of $L$; if $\kappa<\kappa^*$, an endemic equilibrium $\bigl(\frac{\delta}{\kappa+\beta},\frac{\kappa\delta}{\beta_a(\kappa+\beta)}\bigr)$ bifurcates from $(s_0^*,1-s_0^*)$ at $\kappa=\kappa^*$ and attracts trajectories with $a<1-s_0^*$.
3. If $\delta<\beta_a<\beta$, the endemic equilibrium is globally asymptotically stable.

So without decay there is a second, die-out threshold $\kappa^*$ with slow extinction along a line of equilibria.

**Theorem (with awareness decay, $\delta_a>0$).** The continuum collapses to the single disease-free equilibrium $(1,0)$. If $\delta<\beta$, there is a unique interior equilibrium, which is globally asymptotically stable; if $\delta>\beta$, the disease-free equilibrium is the only equilibrium and is globally asymptotically stable. The threshold is the classical $\beta=\delta$, independent of the awareness parameters, however small $\delta_a$ is.

## Expansion

Without decay, any mixture of susceptible and aware individuals with no infection is an equilibrium, so the disease-free set is a line whose stability depends on the fraction of aware individuals, $\beta s+\beta_a a<\delta$. Awareness decay drives every disease-free state back to fully susceptible, where invasion is governed by $\beta$ versus $\delta$ alone, and the bifurcation becomes the standard transcritical one of the SIS model.

## Sources

- David Juher, Istvan Z. Kiss and Joan Saldana, "Analysis of an epidemic model with awareness decay on regular random networks", arXiv:1406.3075 (2014), Sections 2–5 (mean-field system, Theorems 4.2, 5.3 and 5.7, Corollary 5.5), <https://doi.org/10.48550/arXiv.1406.3075>.
