# Sharp switch of the optimal two-group vaccine allocation

**Model.** A homogeneously mixing population consists of two groups of fractions $N_1,N_2$ ($N_1+N_2=1$) that differ only in susceptibility: group 2 is more susceptible by a factor $\sigma>1$. A leaky vaccine with efficacy $1-\varepsilon$, $\varepsilon\in(0,1)$, is given before the outbreak to fractions $v_1,v_2\ge 0$ of the population in the two groups, with $v_1+v_2=v$. With $S_i,V_i$ the unvaccinated and vaccinated susceptibles of group $i$ and $I$ the total infected fraction,

$$S_1'=-\beta S_1I,\qquad V_1'=-\beta\varepsilon V_1I,\qquad S_2'=-\sigma\beta S_2I,\qquad V_2'=-\sigma\beta\varepsilon V_2I,\qquad I'=\beta\,[S_1+\sigma S_2+\varepsilon V_1+\sigma\varepsilon V_2]\,I-\gamma I,$$

and $R_0=\frac{\beta}{\gamma}(N_1+\sigma N_2)$. For a vanishing initial infection the final size $Z=Z(v_1,v_2)$ is the positive solution of

$$1-(N_1-v_1)e^{-\frac{\beta}{\gamma}Z}-(N_2-v_2)e^{-\sigma\frac{\beta}{\gamma}Z}-v_1e^{-\varepsilon\frac{\beta}{\gamma}Z}-v_2e^{-\sigma\varepsilon\frac{\beta}{\gamma}Z}=Z ,$$

and the problem is to minimize $Z(v_1,v_2)$ subject to $v_1,v_2\ge0$, $v_1+v_2=v$.

**Theorem (all-or-nothing allocation with an explicit switch).** Assume $v<\min(N_1,N_2)$. Let $\alpha\in(0,1)$ be the unique root in $(0,1)$ of

$$\alpha-\alpha^{\sigma}-\alpha^{\varepsilon}+\alpha^{\sigma\varepsilon}=0,$$

and define

$$R_0^*=\frac{(N_1+\sigma N_2)\ln(1/\alpha)}{1-N_1\alpha-N_2\alpha^{\sigma}-v\,(\alpha^{\varepsilon}-\alpha)} .$$

Then:

1. if $R_0<R_0^*$, the optimal allocation is $(v_1,v_2)=(0,v)$: all doses to the more susceptible group;
2. if $R_0>R_0^*$, the optimal allocation is $(v_1,v_2)=(v,0)$: all doses to the less susceptible group.

In particular a split allocation is never optimal, and the optimal allocation changes discontinuously at $R_0^*$.

## Depends on

- [Lowest-exposure-first vaccine allocation is asymptotically optimal at high $R_0$](lowest-exposure-first-vaccine-allocation-is-asymptotically-optimal.md)
- [Final-size equation (Kermack–McKendrick 1927)](../../kermack-mckendrick-sir-model/final-size-eq.md)

## Expansion

The proof has two parts. First, any allocation that gives doses to both groups yields a larger final size than one of the two extreme allocations, so only $(v,0)$ and $(0,v)$ compete. Second, the two extreme final-size curves cross exactly once as functions of $R_0$. At a crossing both allocations share the same final size $Z$; writing $\alpha=e^{-\beta Z/\gamma}$ and subtracting the two final size equations leaves $v(\alpha-\alpha^{\sigma}-\alpha^{\varepsilon}+\alpha^{\sigma\varepsilon})=0$, which fixes $\alpha$ independently of the remaining parameters. Substituting $\alpha$ back into the final size equation for $(v,0)$ gives $Z=1-N_1\alpha-N_2\alpha^{\sigma}-v(\alpha^{\varepsilon}-\alpha)$, and $R_0=\frac{\beta}{\gamma}(N_1+\sigma N_2)=(N_1+\sigma N_2)\ln(1/\alpha)/Z$ is the stated $R_0^*$. Below the threshold, protecting the more susceptible (higher exposure index) group removes more transmission; above it, consistent with the high-$R_0$ asymptotics, the vaccine is worth more in the less exposed group, whose vaccinated members are more likely to escape infection altogether. In the source's example (equal groups, one half as susceptible as the other, 40% coverage, 80% efficacy) the final-size curves of the two extreme allocations cross at $R_0^*$ and the optimal curve has a kink there.

## Sources

- Nir Gavish, Guy Katriel, "Optimal vaccination at high reproductive numbers: sharp transitions and counterintuitive allocations", Proceedings of the Royal Society B: Biological Sciences 289 (2022), 20221525, <https://doi.org/10.1098/rspb.2022.1525>. Published version of arXiv:2202.03909, cited next; locators there refer to the arXiv version.
- N. Gavish and G. Katriel, "Optimal vaccination at high reproductive numbers: sharp transitions and counter-intuitive allocations", arXiv:2202.03909 (2022), Section 3 (two-group model, Theorem 2) and Appendix B (proof; Appendix B.3 on the suboptimality of split allocations), <https://doi.org/10.48550/arXiv.2202.03909>.
