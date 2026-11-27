# Maynard Smith–Haigh hitchhiking recursion and the final neutral frequency

**Model (haploid, deterministic).** A favourable allele $B$ (fitness $1 + s$, $s > 0$) replaces $b$ (fitness $1$) at one locus; a neutral locus with alleles $A, a$ lies at recombination fraction $c \in (0, 1]$. Let $p_n$ be the frequency of $B$ in generation $n$, and $Q_n$, $R_n$ the proportions of $A$ among $B$- and $b$-bearing chromosomes. All $B$ descend from one mutant on an $a$ chromosome, so $Q_0 = 0$, and $0 < p_0 < 1$. The population frequency of $A$ in generation $n$ is $p_n Q_n + (1 - p_n) R_n$; initially it is $(1 - p_0) R_0$, not $R_0$. The recursions are

$$p_{n+1} = \frac{(1 + s) p_n}{1 + s p_n}, \qquad Q_n - R_n = -R_0 (1 - c)^n,$$

$$Q_{n+1} = Q_n + c\, \frac{(1 - p_n)(R_n - Q_n)}{1 + s p_n}.$$

**Result.** $p_n = p_0 (1 + s)^n / (1 - p_0 + p_0 (1 + s)^n)$, and the proportion of $A$ on $B$ chromosomes after $B$ has replaced $b$ is

$$Q_\infty = c R_0 (1 - p_0) \sum_{n=0}^{\infty} \frac{(1 - c)^n}{1 - p_0 + p_0 (1 + s)^{n+1}},$$

Since $p_n \to 1$, $Q_\infty$ is also the final population frequency of $A$. If $A$ is initially present ($R_0 > 0$), then $Q_\infty < (1 - p_0) R_0$: the population frequency of a neutral allele not carried by the original mutant strictly decreases from its initial value $(1 - p_0) R_0$ to $Q_\infty$, and $Q_\infty \to 0$ as $c \to 0$. If $R_0 = 0$, then $Q_\infty = 0$. A decrease in the frequency of $A$ does not by itself imply a decrease in the heterozygosity $2x(1-x)$ at the neutral locus, which increases as $x$ falls toward $1/2$ from above.

## Expansion

Substituting $Q_n - R_n = -R_0 (1-c)^n$ into the $Q$ recursion and using

$$\frac{1 - p_n}{1 + s p_n} = \frac{1 - p_0}{1 - p_0 + p_0 (1 + s)^{n+1}},$$

which follows from the closed form of $p_n$, telescopes $Q_\infty = \sum_n (Q_{n+1} - Q_n)$ into the stated series. Since $s > 0$ and $p_0 > 0$, each denominator $1 - p_0 + p_0(1+s)^{n+1}$ exceeds $1$, so for $R_0 > 0$ the series is strictly below the geometric sum $\sum_n (1-c)^n = 1/c$, giving $Q_\infty < (1-p_0) R_0$. The denominators grow geometrically, so $\sum_n 1/(1 - p_0 + p_0(1+s)^{n+1})$ is finite and $Q_\infty \le c R_0 (1-p_0) \sum_n 1/(1 - p_0 + p_0(1+s)^{n+1}) \to 0$ as $c \to 0$. For example, with $p_0 = 0.001$, $R_0 = 1$, $s = 0.2$ and $c = 0.002$, the frequency of $A$ starts at $0.999$ and ends strictly below it, while its first series term already exceeds $0.001$; the neutral heterozygosity $2x(1-x)$ therefore rises from its initial value. The discrete closed form of $p_n$ is the generation-by-generation analogue of the [logistic sweep trajectory](sweep-traj.md). The continuous-time approximation of the same model, for $c \ll s$, gives $Q_\infty / R_0 \approx (c/s) \log(1/p_0)$, see [the logarithmic approximation](maynard-smith-haigh-log-approximation.md).

## Depends on

Its statement uses only the notions recalled above.

## Proof depends on

- [The geometric series of a real ratio r with |r| < 1 sums to 1/(1 − r)](../../../Analysis/sequences-and-series/convergence/limits-of-specific-sequences-and-partial-sums/geometric-series-convergence.md)

## Sources

- J. Maynard Smith and J. Haigh, "The hitch-hiking effect of a favourable gene", *Genetical Research* 23 (1974), 23–35, <https://doi.org/10.1017/S0016672300014634>. Section 2, equations (2)–(9).
