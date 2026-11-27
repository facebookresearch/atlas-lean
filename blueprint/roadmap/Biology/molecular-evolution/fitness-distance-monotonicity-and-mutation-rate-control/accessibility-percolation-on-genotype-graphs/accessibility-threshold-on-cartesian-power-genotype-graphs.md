# Accessibility threshold on Cartesian power genotype graphs

Let $\mathcal A$ be a finite directed **allele graph** with adjacency matrix $A$ (vertices are alleles of one locus, arrows are allowed mutations). The genotype space with $L$ loci is the Cartesian power $\mathcal A^{\square L}$: genotypes are $L$-tuples of alleles, and an arrow changes exactly one locus along an arrow of $\mathcal A$. In the **House-of-Cards (HoC)** model every genotype $g$ gets an i.i.d. fitness $F_g \sim U(0,1)$. A walk is **accessible** if fitness strictly increases along it, and $Z_{gh}$ counts accessible walks from $g$ to $h$. For $0 \le \beta \le 1$, **$\beta$-accessibility** of $h$ from $g$ is $P(Z_{gh} \ge 1 \mid F_h - F_g = \beta)$.

Consider genotype pairs $(a_L, b_L)$ whose allele-pair counts $M_{vw}^{(L)} = \#\{l : a_l = v,\ b_l = w\}$ satisfy $M^{(L)}_{vw}/L \to p_{vw}$, with some off-diagonal $p_{vw} > 0$ (so the distance is linear in $L$) and every locus pair joined by a nonzero-length walk. Define

$$\Gamma_{vw}(t) = \ln\bigl(e^{tA}\bigr)_{vw}, \qquad \boldsymbol\Gamma_{a_L b_L}(t) = \frac1L\sum_{l=1}^L \Gamma_{a_l b_l}(t),$$

so that $e^{L\boldsymbol\Gamma(t)}$ is the expected number of quasi-accessible walks spanning fitness range $t$. $\boldsymbol\Gamma$ is strictly increasing from $-\infty$ to $\infty$. Let $\hat\beta$ be its unique zero and $\beta^* = \lim_L \hat\beta$, which solves $\sum_{v,w} p_{vw}\Gamma_{vw}(\beta^*) = 0$.

**Theorem 1 (threshold).** With

$$c_L = \hat\beta - \frac{1}{\boldsymbol\Gamma'_{a_L b_L}(\hat\beta)}\,\frac{\ln L}{L},$$

$\beta$-accessibility tends to $0$ whenever $\beta \le c_L - g(L)$ with $g(L)\,L \to \infty$. If the setup is **regular** (a refined Martinsson function is strictly negative inside its domain with non-vanishing slope at the boundary), $\beta$-accessibility has a positive $\liminf$ whenever $\beta \ge c_L + g(L)$, so $c_L$ is a $1/L$-threshold and the critical value is $\beta_c = \beta^*$.

**Theorem 2.** In irregular setups, $\beta_c > \beta^*$ whenever $\beta_c$ exists.

**Theorem 3 (critical path length).** At $\beta = c_L + \eta/L$, with probability tending to $1$ every $\beta$-accessible path has length $\boldsymbol\Gamma'_{a_L b_L}(\hat\beta)\,\hat\beta\,L \pm g(L)\sqrt L$ for any $g(L) \to \infty$.

**Examples (all loci differing).**
- Directed hypercube ($\mathcal A$ = two alleles, forward mutation only): $\boldsymbol\Gamma(\beta) = \ln\beta$, so $\beta^* = 1$ and the threshold is $1 - \ln L/L$; the hypercube is marginally accessible.
- Complete graph on $|\mathcal A|$ alleles: $e^{\beta^*}$ is the unique positive root of $x^{|\mathcal A|} - |\mathcal A|\,x - 1 = 0$, and $\beta^* = \frac{\ln|\mathcal A|}{|\mathcal A|} + O\bigl(\frac{\ln|\mathcal A|}{|\mathcal A|^2}\bigr) \to 0$.
- Complete graph without back-mutation to the initial allele: $\boldsymbol\Gamma(\beta) = \ln\frac{e^{(|\mathcal A|-2)\beta} - 1}{|\mathcal A| - 2}$ and $\beta^* = \frac{\ln(|\mathcal A|-1)}{|\mathcal A|-2}$.
- Path graph on three alleles, end to end: $(e^{tA})_{13} = (\cosh(\sqrt2\,t) - 1)/2$, giving $\beta^* = \ln(3 + 2\sqrt2)/\sqrt2 \approx 1.25 > 1$, so such pairs are asymptotically inaccessible.

## Expansion

Conditioning on $F_{a_L} = 0$ and $F_{b_L} = \beta$, a fixed walk of length $n$ with distinct interior vertices is accessible with probability $\beta^{n-1}/(n-1)!$. Allowing every genotype infinitely many interchangeable copies (quasi-accessibility) turns the expected walk count into $\sum_n \frac{\beta^n}{n!}(\text{number of walks of length } n) = \prod_l (e^{\beta A})_{a_l b_l}$ up to polynomial factors, which is $e^{L\boldsymbol\Gamma(\beta)}$. Markov's inequality then gives the lower side of the threshold, the $\ln L/L$ correction coming from the polynomial prefactor, and the first-moment calculation separated by walk length gives Theorem 3. The upper side is a second-moment argument: the refined Martinsson function compares walks that share a middle segment, and regularity says the walk count is not dominated by clustered walks, so $P(Z \ge 1) \ge (EZ)^2/E Z^2$ stays bounded away from $0$. Richer mutational connectivity, with more alleles or more arrows, lowers $\beta^*$ and raises accessibility. Requiring a unique order of mutations, as on a path, can push $\beta^*$ above $1$.

## Depends on

- [Accessible mutational paths in the House-of-Cards landscape](../../../population-genetics/selection-migration-and-transmission/fitness-landscapes/accessible-adaptive-paths.md)

## Sources

- B. Schmiegelt, J. Krug, "Accessibility percolation on Cartesian power graphs", Journal of Mathematical Biology (2023), Definitions 1–13, Propositions 1–4, Theorems 1–3 and Eqs. (28)–(38), <https://doi.org/10.1007/s00285-023-01882-z>, PMCID PMC9931871.
