# Mean generation interval contracts under competing infectious contacts

**General stochastic SIR model.** Each person $i$ in a finite population is infected at time $t_i$ ($t_i=\infty$ if never) and stops being infectious at $t_i+r_i$, with a finite random recovery period $r_i$. Once infected, $i$ makes infectious contact with person $j$ after an **infectious contact interval** $\tau_{ij}$, a positive random variable with conditional cdf $F_{ij}(\tau\mid r_i)$ that may put mass at $\infty$ (no contact); $F_{ij}(\tau\mid r_i)=F_{ij}(\infty\mid r_i)$ for $\tau\ge r_i$. If $j$ is still susceptible at the contact time $t_{ij}=t_i+\tau_{ij}$, then $i$ infects $j$, $t_j=t_{ij}$, and we write $v_j=i$ (the infector of $j$). Imported infections arrive at importation times $t_{0j}$. The **generation interval** of the pair is $t_j-t_i=\tau_{ij}$ on the event $v_j=i$.

**Lemma (Lemma 1).**

$$
\mathbb E\bigl[\tau_{ij}\bigm| v_j=i\bigr]\le\mathbb E\bigl[\tau_{ij}\bigm|\tau_{ij}<\infty\bigr].
$$

Equality holds if and only if, given $r_i$ and $\tau_{ij}<\infty$, either $\tau_{ij}$ is almost surely constant or $j$ is at no risk of infectious contact from any source other than $i$. In particular the inequality is strict whenever $j$ can be reached by another infective or by importation and $\tau_{ij}$ is non-degenerate, and the mean generation interval decreases further as the risk to $j$ from other sources increases.

**Consequence.** As an epidemic grows, the mean observed generation interval contracts relative to the intrinsic infectious-contact-interval distribution (**global competition**, driven by overall prevalence); with clustered contacts it contracts early even at low global prevalence (**local competition**, driven by prevalence within households or clusters). Estimating $R$ from the growth rate with an uncontracted generation interval distribution therefore misestimates it.

## Expansion

Condition on $r_i$ and $\tau_{ij}<\infty$, and let $F^*_{ij}=F_{ij}/F_{ij}(\infty\mid r_i)$. Then $v_j=i$ exactly when $j$ escapes contact from all other sources during $(t_i,t_i+\tau_{ij})$; call that escape probability $S_{*j}(t_i+\tau)$. The law of $\tau_{ij}$ given $v_j=i$ has density proportional to $S_{*j}(t_i+\tau)\,dF^*_{ij}(\tau\mid r_i)$, so

$$
\mathbb E[\tau_{ij}\mid r_i,v_j=i]-\mathbb E[\tau_{ij}\mid r_i,\tau_{ij}<\infty]=\operatorname{Cov}\Bigl(\tau_{ij},\ \tfrac{S_{*j}(t_i+\tau_{ij})}{\psi}\Bigm| r_i,\tau_{ij}<\infty\Bigr)\le0,
$$

where $\psi$ normalizes, because $S_{*j}$ is nonincreasing in $\tau$ (Chebyshev's covariance inequality for a function and a monotone decreasing transform of the same variable). Averaging over $r_i$ by iterated expectation gives the lemma. The covariance vanishes only if one of the two variables is constant.

## Depends on

- [Reproductive number from growth rate and generation interval](../../euler-lotka-equation-and-the-reproduction-number/reproduction-number.md)

## Sources

- E. Kenah, M. Lipsitch and J. M. Robins, "Generation interval contraction and epidemic data analysis", arXiv:0706.2024 (2007), Section 2 (general stochastic SIR model) and Section 3 (Lemma 1, Eqs. for $\mathbb E[\tau_{ij}\mid r_i,\tau_{ij}<\infty]$ and the equality conditions), <https://doi.org/10.48550/arXiv.0706.2024>.
