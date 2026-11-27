# Independence of genus ages and sizes in the Yule model

**Yule's model.** Species within a genus multiply as a pure-birth (Yule) process $(Y_t)$ with rate $s$ started from one species, and each genus independently founds new genera at rate $g$; the number of genera $(N_t)$ is a Yule process with rate $g$ started from one genus. A newly founded (daughter) genus starts with one species; the mother genus is unaffected.

**Theorem (ages and sizes).** At time $T$, the pairs $(A_i, S_i)$, $1 \le i \le N_T - 1$, of ages and species numbers of the derived genera are independent and identically distributed as a pair $(A, S)$ killed at the first value of $A$ exceeding $T$, where $A \sim \mathrm{Exp}(g)$ and $\mathbb P(S = k \mid A = a) = \mathbb P(Y_a = k)$. Hence

$$\mathbb P(S = k,\ A \in da) = g e^{-(g+s)a}\big(1 - e^{-sa}\big)^{k-1}\,da, \qquad a > 0,\ k \ge 1,$$

and $N_T$ is geometric with success probability $e^{-gT}$. As $T \to \infty$ the size frequency distribution is the **Yule–Simon law** $\mathbb P(S = k) = \int_0^\infty ge^{-ga}e^{-sa}(1 - e^{-sa})^{k-1}da$, with a power-law tail of exponent $1 + g/s$.

**Theorem (general diversification, sampled genera).** If within-genus diversification $Z$ is a general process with extinction, genera have a lifetime $L$ (the extinction time of $Z$), generic births occur at rate $g$ with $g\mathbb E[L] > 1$, and extant genera are sampled independently with probability $f$, then the coalescence times, ages and sizes $(H_i, A_i, S_i)$ of the sampled genera form an i.i.d. sequence killed at the first $H_i > T$ (a coalescent point process), with $H$ and $S$ independent conditionally on the age structure as described by explicit scale functions.

**Proposition (birth–death within genera).** If $Z$ is linear birth–death with rates $\lambda, \mu$ and $r = \lambda - \mu$, let $\eta$ be the Malthusian parameter of the generation process and $F(t) = 1 + \lambda(e^{rt} - 1)/r$ ($F(t) = 1 + \lambda t$ if $r = 0$). Then

$$\mathbb P(S = n) = \frac{g}{\lambda}\int_0^\infty e^{-\eta t}\frac{F'(t)}{F(t)^2}\Big(1 - \frac{1}{F(t)}\Big)^{n-1}dt .$$

If $\lambda > \mu$, $S$ has a power-law tail, $\ln\mathbb P(S = n)/\ln n \to -1 - \eta/r$; if $\lambda = \mu$, $\ln\mathbb P(S = n)/\sqrt n \to -2\sqrt{\eta/\lambda}$ (heavy but not power-law); if $\lambda < \mu$ the tail is geometrically light, bounded by a multiple of $(\lambda/\mu)^n/n$.

**Proposition (pure birth with state-dependent rates).** If $Z$ jumps from $k$ to $k+1$ at rate $\lambda_k$, then

$$\mathbb P(S = n) = \frac{g}{g + \lambda_n}\prod_{k=1}^{n-1}\frac{\lambda_k}{g + \lambda_k}, \qquad \mathbb E[A \mid S = n] = \sum_{k=1}^n \frac{1}{g + \lambda_k},$$

and $S$ has a power-law tail if and only if $\lambda_n/n$ converges to a finite nonzero limit (linear preferential attachment); the same dichotomy governs urn schemes with ball additions and removals.

## Proof sketch

Reading the genealogy of genera backward from time $T$, the founding times of extant derived genera are the atoms of a Poisson-like point process, and conditioning on a founding time $T - a$ the genus has evolved for time $a$ independently of everything else, so its size is $Y_a$; the independence of the pairs is the key structural fact behind Yule's 1925 frequency formula. With extinction, the reconstructed tree of sampled genera is a coalescent point process with i.i.d. node depths $H_i$, which carries the independence to the general case. The tail of $S$ is governed by the competition between the exponential growth rate $\eta$ of the number of genera and the growth rate $r$ of genus size: the ratio $\eta/r$ is the power-law exponent.

## Sources

- Amaury Lambert, "Ages, sizes and (trees within) trees of taxa and of urns, from Yule to today", *Philosophical Transactions of the Royal Society B: Biological Sciences* 380 (2025), 20230305, <https://doi.org/10.1098/rstb.2023.0305>. Preprint version: arXiv:2409.14536 (2024), Theorems 3.1–3.2 and Propositions 3.1–3.3 (Section 3), <https://doi.org/10.48550/arXiv.2409.14536>.
