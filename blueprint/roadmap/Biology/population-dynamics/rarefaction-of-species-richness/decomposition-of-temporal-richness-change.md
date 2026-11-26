# Decomposition of temporal richness change and what rarefaction measures

In the multinomial–Poisson community model with $k$ species, sample sizes $n_t$ and relative abundances $p_{it}$ varying smoothly in time, write $\gamma_j(\Lambda) = e^{-\Lambda}\Lambda^j/j!$ for Poisson probabilities.

**Theorem (gradient of richness).** For large $n_t$, in the Poisson approximation $E\,S_j(n_t) \approx \sum_i \gamma_j(n_t p_{it})$,

$$\frac{d}{dt} E\,S(n_t) \approx \sum_{i=1}^k \gamma_1(n_t p_{it})\, \frac{d}{dt}\log(n_t p_{it}) = E\,S_1(n_t)\,\frac{d}{dt}\log n_t + \sum_{i=1}^k \gamma_1(n_t p_{it})\,\frac{d}{dt}\log p_{it},$$

so the change in expected richness splits additively into a community-size term, weighted by the expected number of singletons, and a composition term.

**Corollary (size-based rarefaction).** With the common rarefied size $n^* = \min_t n_t = n_t - m_t$ and $m_t \ll n_t$,

$$\frac{d}{dt} E\,R_t(n^*) \approx \sum_{i=1}^k w_{it}\,\gamma_1(n_t p_{it})\,\frac{d}{dt}\log p_{it}, \qquad w_{it} = \gamma_0\Big(\frac{m_t}{n_t} - m_t p_{it}\Big) = e^{\,m_t p_{it} - m_t/n_t},$$

so size-based rarefied richness tracks only changes in community composition.

**Corollary (coverage-based rarefaction).** With $n_t^* = E\,S_1(n_t)/(1 - q)$ for coverage $q \in (0, 1]$,

$$\frac{d}{dt} E\,\tilde R(n_t^*) \approx \tilde w_{1t}\,\frac{d}{dt} E\,S_1(n_t) + \frac{d}{dt} E\,R_t(n_t^*), \qquad \tilde w_{1t} = \frac{E\,S_1(n_t^*)}{E\,S_1(n_t)},$$

so coverage-based rarefied richness responds to both community size and composition, and the two techniques can report trends of opposite sign.

## Depends on

- [Expected rarefied richness and sample coverage](expected-rarefied-richness-and-sample-coverage.md)

## Expansion

Differentiating $\gamma_j(\Lambda)$ gives $\gamma_j' = \gamma_{j-1} - \gamma_j$, so summing over $j \ge 1$ telescopes to $\gamma_0(\Lambda)\,\Lambda' = \gamma_1(\Lambda)\,(\log \Lambda)'$ for each species, which is the theorem. Size-based rarefaction freezes $n^*$, killing the $\log n$ term. Coverage-based rarefaction lets $n_t^*$ move with the singleton count, which reintroduces a size term; since $E\,S + E\,S_0 = k$, that term is linear in the richness gradient and is a fair proxy only when the changes in unobserved and singleton species offset.

## Sources

- H. Shimadzu, *On species richness and rarefaction: size- and coverage-based techniques quantify different characteristics of richness change in biodiversity*, J. Math. Biol. 77 (2018), 1363–1381 (Lemma 1, Theorem 1, Eqs. (13)–(17), Corollaries 1–2). <https://doi.org/10.1007/s00285-018-1255-5> (PMCID: PMC6182778)
