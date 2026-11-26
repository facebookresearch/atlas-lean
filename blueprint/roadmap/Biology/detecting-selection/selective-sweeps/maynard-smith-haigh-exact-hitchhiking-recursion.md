# Maynard Smith–Haigh hitchhiking recursion and the final neutral frequency

**Model (haploid, deterministic).** A favourable allele $B$ (fitness $1 + s$, $s > 0$) replaces $b$ (fitness $1$) at one locus; a neutral locus with alleles $A, a$ lies at recombination fraction $c \in (0, 1]$. Let $p_n$ be the frequency of $B$ in generation $n$, and $Q_n$, $R_n$ the proportions of $A$ among $B$- and $b$-bearing chromosomes. All $B$ descend from one mutant on an $a$ chromosome, so $Q_0 = 0$, and $0 < p_0 < 1$. The recursions are

$$p_{n+1} = \frac{(1 + s) p_n}{1 + s p_n}, \qquad Q_n - R_n = -R_0 (1 - c)^n,$$
$$Q_{n+1} = Q_n + c\, \frac{(1 - p_n)(R_n - Q_n)}{1 + s p_n}.$$

**Result.** $p_n = p_0 (1 + s)^n / (1 - p_0 + p_0 (1 + s)^n)$, and the proportion of $A$ on $B$ chromosomes after $B$ has replaced $b$ is

$$Q_\infty = c R_0 (1 - p_0) \sum_{n=0}^{\infty} \frac{(1 - c)^n}{1 - p_0 + p_0 (1 + s)^{n+1}},$$

which satisfies $Q_\infty \le R_0 (1 - p_0) < R_0$. Thus the frequency of a neutral allele not carried by the original mutant is reduced from $R_0$ to $Q_\infty$; for $c \to 0$ it is eliminated.

## Expansion

Substituting $Q_n - R_n = -R_0 (1-c)^n$ into the $Q$ recursion and using

$$\frac{1 - p_n}{1 + s p_n} = \frac{1 - p_0}{1 - p_0 + p_0 (1 + s)^{n+1}},$$

which follows from the closed form of $p_n$, telescopes $Q_\infty = \sum_n (Q_{n+1} - Q_n)$ into the stated series. Each denominator is at least $1$, so the series is at most $\sum_n (1-c)^n = 1/c$. The continuous-time approximation of the same model, for $c \ll s$, gives $Q_\infty / R_0 \approx (c/s) \log(1/p_0)$, see [the logarithmic approximation](maynard-smith-haigh-log-approximation.md).

## Depends on

- [Logistic trajectory of a selective sweep](sweep-traj.md)

## Sources

- J. Maynard Smith and J. Haigh, "The hitch-hiking effect of a favourable gene", *Genetical Research* 23 (1974), 23–35, <https://doi.org/10.1017/S0016672300014634>. Section 2, equations (2)–(9).
