# Validity of the one-sided Fisher exact test

Let $X \sim \mathrm{Bin}(n_1, p)$ and $Y \sim \mathrm{Bin}(n_2, p)$ be independent with a common
$p \in (0, 1)$, and let $t \le n_1 + n_2$. Conditionally on the margin $X + Y = t$, the upper Fisher exact
p-value $P$ of $X$ is valid: $\Pr[P \le s \mid X + Y = t] \le s$ for every $s \in [0, 1]$. The bound holds
for every nuisance value $p$, because the conditional law of $X$ does not depend on it.

## Sources

- Lehmann and Romano (2005), Section 4.5 and Lemma 3.3.1.
