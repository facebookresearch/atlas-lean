# Disease-free thresholds of the opinion-switching SIS model

**Opinion dynamics.** In the $q$-voter model a fraction $x$ holds opinion $A$ and $1-x$ holds $B$, and $x'=px(1-x)\big(x^{q-1}-(1-x)^{q-1}\big)$. For $q>1$ the polarized states $x=0,1$ are asymptotically stable ($f'=-p$) and the balanced state $x=\frac12$ is unstable ($f'(\frac12)=p(q-1)/2^{q-1}$): the initial majority wins.

**Coupled model.** With susceptible and infectious fractions $S_a,S_b,I_a,I_b$ (summing to $1$), transmission rate $\beta$, reduced infectivity $\alpha\in[0,1]$ of opinion-$B$ infectives, susceptibility factor $\delta$ of $B$-susceptibles, recovery $\gamma$ and a $2$-voter persuasion rate $\tilde p$,

$$S_a'=-\beta S_a(I_a+\alpha I_b)+\gamma I_a+\tilde pS_aS_b(S_a-S_b),\qquad S_b'=-\beta\delta S_b(I_a+\alpha I_b)+\gamma I_b+\tilde pS_aS_b(S_b-S_a),$$

$$I_a'=\beta\delta S_b(I_a+\alpha I_b)-\gamma I_a,\qquad I_b'=\beta S_a(I_a+\alpha I_b)-\gamma I_b .$$

Infection switches the opinion (an infected $A$-susceptible becomes an infectious $B$ and vice versa), modelling reassessment of behaviour upon infection. Recovered individuals keep their opinion.

**Disease-free equilibria** (for $\delta=1$, in rescaled time with $R=\beta/\gamma$ and persuasion rate $p$).

- All susceptibles of opinion $B$: asymptotically stable iff $R<1$.
- All susceptibles of opinion $A$: asymptotically stable iff $R<1/\alpha$; for $\alpha=0$ it is stable for every $R$.
- The balanced state $S_a=S_b=\frac12$ is unstable for all $R>0$.

**Balanced endemic state.** Writing $s=S_a+S_b$, $z=\alpha S_a+S_b$ and $v=I_a+\alpha I_b$, endemic equilibria satisfy $z=1/R$ and $v=(1-s)/(Rs)$, and the balanced endemic equilibrium has $s_b=2/((1+\alpha)R)$, $v_b=((1+\alpha)R-2)/(2R)$; it is feasible iff $(1+\alpha)R>2$, and its stability reduces to explicit inequalities in $p$ and $Q=(1+\alpha)R$ via the $3\times3$ Routh–Hurwitz conditions.

## Depends on

- [SIS epidemic model](../sis-epidemic-model/README.md)

## Expansion

The thresholds are reversed from intuition because of the switch upon infection. In a population of cautious $B$-susceptibles, every new infective becomes an $A$-infective with full infectivity, so invasion requires only $R>1$. In a population of $A$-susceptibles, new infectives become $B$-infectives with infectivity $\alpha\beta$, so invasion needs $\alpha R>1$. For $R<1$ both polarized disease-free states are stable, for $1<R<1/\alpha$ only the all-$A$ state is, and combined with majority persuasion and the endemic branches this creates alternative basins of attraction in which the long-run prevalence depends on the initial opinion split.

## Sources

- T. Goetz, T. Krueger, K. Niedzielewski, J. Schneider, "Coupling opinion dynamics and epidemiology", arXiv:2512.10612 (2025), Section 2 (q-voter model, Eqs. (E:Voter) and (E:SIsystem)), Section 3 (lemma on disease-free equilibria, remark for $\alpha=0$, Eq. (E:Endemic:s)), <https://doi.org/10.48550/arXiv.2512.10612>.
