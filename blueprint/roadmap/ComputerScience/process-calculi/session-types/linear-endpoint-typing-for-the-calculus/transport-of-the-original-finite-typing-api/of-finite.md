# Finite passive-name typing embeds into endpoint typing

Let $n$, $N$ be natural numbers, $\Gamma$ a finite binary session context with $\Gamma(c) =
\mathrm{end}$ for every $c \ge N$, $p$ a process, $r$ a polarity and $\rho : \mathbb{N} \to
\mathbb{N}$ a rank assignment. If $\Gamma \vdash_n p$ in the typing of sequential threads, then
$\Gamma^{r}_{N,\rho} \vdash_n p$ in endpoint typing, where $\Gamma^{r}_{N,\rho}$ maps
$\mathrm{c}_i^{r}$ to $(\rho(i), \iota(\Gamma(i)))$ for $i < N$ and $\iota$ translates sends and
receives of $\Gamma(i)$ into passive-name sends and receives.
