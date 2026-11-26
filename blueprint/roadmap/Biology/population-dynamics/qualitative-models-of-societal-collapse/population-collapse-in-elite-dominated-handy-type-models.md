# Population collapse in Elite-dominated HANDY-type models

**Setting.** The HANDY model of Motesharrei, Rivas and Kalnay couples a human population, split into Commoners $C$ (who produce wealth) and Elites $E$ (who consume it at a higher rate), to natural resources and accumulated wealth. The analysis replaces its explicit equations by a generic system for total food resources $B$,

$$B'=B\,R_B(B,C,E),\qquad C'=C\,R_C(B,C,E),\qquad E'=E\,R_E(B,C,E),$$

with $B,C,E>0$, subject to qualitative hypotheses:

- **H$_1$** $R_B,R_C,R_E$ are $C^1$ and $(B,C,E)$ is a solution;
- **H$_2$** (mild shortage) $R_E>0$ whenever $R_C=0$;
- **H$_3$** (Elite domination) $E'/E\ge C'/C$ for all $t$;
- **H$_B$** every trajectory is bounded;
- **H$_Z$** (dependence) if $C(t)\to0$ then $E(t)\to0$.

A trajectory satisfying these is an *H trajectory*. A purely trajectory-level version (*H$^*$*) drops the differential equations. It replaces H$_1$ by regularity of $(B,C,E)$ (bounded derivative, uniformly continuous per capita rates), and H$_2$ by H$^*_2$: for a bounded trajectory there are $\varepsilon_2^*,\delta_2^*>0$ such that $|C'/C|\le\delta_2^*$ implies $E'/E-C'/C>\varepsilon_2^*$. Boundedness follows from H$^*_1$ together with H$_4$ ($B'<0$ once $B\ge B_4$) and H$_5$ ($C',E'\le0$ once $B\le B_4$ and $C+E\ge C_5$), which give a trapping box $[0,B_4]\times[0,C_5]^2$.

**Theorem.**

1. Under H$_1$–H$_2$ there is no equilibrium with $C>0$ and $E>0$.
2. Every H trajectory is an H$^*$ trajectory.
3. (Population collapse) For every H$^*$ trajectory, $C(t)\to0$ and $E(t)\to0$ as $t\to\infty$.
4. Every trajectory of the HANDY model with Elite-dominated parameters and strictly positive initial data is an H$^*$ trajectory, and therefore collapses.

## Expansion

H$_3$ says that $\log(E/C)$ is nondecreasing, so the Elite fraction never declines. H$^*_2$ says that whenever Commoners are nearly stationary, the ratio $E/C$ grows at a definite rate $\varepsilon_2^*$. A bounded trajectory cannot have $C'/C$ stay away from zero forever, since that would force $C$ to $0$ or to infinity. Each time $|C'/C|\le\delta_2^*$, therefore, $E/C$ gains a fixed increment, and summing these gains forces $E/C\to\infty$. Boundedness of $E$ then yields $C\to0$, and H$_Z$ gives $E\to0$. A generalized Barbashin–Krasovskii–LaSalle invariance principle handles the limit sets. The point is structural: collapse follows from Elite domination plus dependence on Commoners' labor, not from the particular functional forms of HANDY.

## Sources

- Naghmeh Akhavan, James A. Yorke, "Population collapse in Elite-dominated societies: A differential equations model without differential equations", arXiv:1908.02870 (2019), Section 2 (H model, hypotheses H$_1$–H$_3$, H$_B$, H$_Z$, H$^*_1$–H$^*_2$, H$_4$–H$_5$), Proposition 1, Theorems 2–3, Propositions 4–5, Theorem 6 and Proposition 8, <https://doi.org/10.48550/arXiv.1908.02870>.
