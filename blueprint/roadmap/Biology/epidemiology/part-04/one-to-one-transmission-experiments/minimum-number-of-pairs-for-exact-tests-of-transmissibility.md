# Minimum number of pairs for exact tests of transmissibility

**Setting.** In $n$ independent one-to-one transmission pairs, the number $K$ of pairs with transmission is $\mathrm{Binomial}(n, q)$ with $q = R_0/(R_0 + 1)$ (see [Reproduction number from one-to-one transmission trials](reproduction-number-from-one-to-one-transmission-trials.md)).

**One-sample test.** To test $H_0 \colon R_0 \le R_{0,\mathrm{ref}}$ against $H_1 \colon R_0 > R_{0,\mathrm{ref}}$, put $q_{\mathrm{ref}} = R_{0,\mathrm{ref}}/(R_{0,\mathrm{ref}} + 1)$. The exact one-sided p-value after observing $k$ infected pairs is

$$p(k) = \Pr(K \ge k \,;\, n, q_{\mathrm{ref}}) = \sum_{j = k}^{n} \binom{n}{j} q_{\mathrm{ref}}^{\,j} (1 - q_{\mathrm{ref}})^{n-j},$$

and its power at a true value $R_0$ is $\sum_{k} \binom{n}{k} q^k (1-q)^{n-k}\, \mathbf{1}\{p(k) \le \alpha\}$.

**Proposition (minimum sample sizes).** The most extreme outcome $k = n$ has $p(n) = q_{\mathrm{ref}}^{\,n}$, so $H_0$ can be rejected at level $\alpha$ only if $n \ge \log \alpha / \log q_{\mathrm{ref}}$. Consequently:

- for $R_{0,\mathrm{ref}} = 1$ ($q_{\mathrm{ref}} = 1/2$) at $\alpha = 0.05$: $3$ pairs never suffice, even if all three transmit ($p = 1/8 = 0.125$), while $5$ pairs all transmitting give $p = 1/32 \approx 0.031$; at $\alpha = 0.01$ at least $7$ pairs are needed ($2^{-7} \approx 0.0078$, $2^{-6} \approx 0.016$);
- for $R_{0,\mathrm{ref}} = 2$ ($q_{\mathrm{ref}} = 2/3$) at $\alpha = 0.05$: at least $8$ pairs, all transmitting, are needed ($(2/3)^7 \approx 0.059$, $(2/3)^8 \approx 0.039$).

**Two-sample test.** Comparing two groups of $n$ pairs each via the two-sided Fisher exact test of $H_0 \colon q_1 = q_2$ (equivalently $R_{0,1} = R_{0,2}$): with $n = 3$ no outcome is significant at $\alpha = 0.05$ (the extreme table $3/3$ versus $0/3$ has $p = 2/\binom{6}{3} = 0.1$); with $n = 4$ only $4/4$ versus $0/4$ is significant ($p = 2/\binom{8}{4} \approx 0.029$); with $n = 5$ exactly the outcomes $5/5$ vs $0/5$, $5/5$ vs $1/5$ and $4/5$ vs $0/5$ are significant (for instance $5/5$ vs $1/5$ gives $p = 12/252 \approx 0.048$).

## Depends on

- [Reproduction number from one-to-one transmission trials](reproduction-number-from-one-to-one-transmission-trials.md)

## Expansion

Because $R_0 \mapsto q$ is strictly increasing, hypotheses about $R_0$ are hypotheses about a binomial proportion, and the exact binomial upper tail is the uniformly most powerful one-sided test statistic. The p-value is smallest when $k = n$, which gives the bound $q_{\mathrm{ref}}^{\,n} \le \alpha$. For two groups the Fisher test conditions on the total number of infected pairs; the most extreme table among $\binom{2n}{n}$ equally likely allocations (and its mirror image) gives the minimum attainable two-sided p-value $2/\binom{2n}{n}$, which is $0.1$ for $n = 3$ and below $0.05$ from $n = 4$ on. Thus the common design with three pairs per group cannot establish either $R_0 > 1$ or a difference between two viruses, and an observed $k = n$ only bounds $R_0$ from below.

## Sources

- H. Nishiura, H.-L. Yen and B. J. Cowling, "Sample size considerations for one-to-one animal transmission studies of the influenza A viruses", PLoS ONE 8 (2013), e55358, Eqs. (8)–(11), Results (Tables 2 and 3, Figure 1), <https://doi.org/10.1371/journal.pone.0055358> (PMCID: PMC3561278).
