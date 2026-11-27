# Survival criterion for the birth–death process with random birth-rate mutation

Let $\mu$ be a probability distribution on $[0,\infty)$, absolutely continuous with respect to Lebesgue measure, and $r \in [0,1]$. Start with one individual whose birth rate $\lambda$ is sampled from $\mu$. Each individual gives birth at its rate $\lambda$ and dies at rate $1$. At each birth the newborn keeps its parent's birth rate with probability $1-r$, and with probability $r$ (mutation) receives a new birth rate sampled independently from $\mu$. Let $Z(t)$ be the number of individuals alive; the process **survives** if $Z(t) > 0$ for all $t$.

**Theorem.** The process survives with positive probability iff at least one of the following holds:

$$

\text{(I)}\quad \mu\big(\{\lambda : \lambda(1-r) > 1\}\big) > 0, \qquad\qquad
\text{(II)}\quad \int_{\{\lambda(1-r) \le 1\}} \frac{\lambda r}{1 - \lambda(1-r)}\,d\mu(\lambda) > 1 .

$$

Condition (I) says some genotype is supercritical on its own (its non-mutant offspring rate exceeds the death rate); condition (II) says that, when every genotype is subcritical, a single genotype nevertheless produces on average more than one mutant founder.

**Corollary (uniform birth rates).** Let $\mu$ be uniform on $[0,a]$.

- If $0 < a \le 1$, the process dies out almost surely for every $r$.
- If $a > 2$, it survives with positive probability for every $r$.
- If $a = 2$, it dies out for $r = 1$ and survives for every $r < 1$.
- If $1 < a < 2$, there is $r_c \in (1 - \tfrac1a, 1)$ such that the process survives by (I) for $r < 1 - \tfrac1a$, survives by (II) for $1 - \tfrac1a \le r < r_c$, and dies out for $r \ge r_c$.

So a high mutation probability can make a virus population go extinct even though some mutants are fit, and an intermediate mutation probability can rescue a population made only of unfit genotypes.

## Expansion

Group individuals into genotype families: a family founded by a type-$\lambda$ individual grows as a linear birth–death process with birth rate $\lambda(1-r)$ and death rate $1$, while mutant births at rate $\lambda r$ found new families. If $\lambda(1-r) > 1$ for a $\mu$-positive set, some family is supercritical and survives with positive probability. Otherwise each family dies out, its total progeny has mean $1/(1-\lambda(1-r))$ individual-lifetimes, and the expected number of mutant families it founds is $\lambda r/(1-\lambda(1-r))$. The families then form a Galton–Watson process whose mean offspring is the integral in (II), and the process survives iff that mean exceeds $1$ (the critical case $=1$ dies out).

## Sources

- J. Theodore Cox, Rinaldo B. Schinazi, "A Branching Process for Virus Survival", arXiv (2011); Journal of Applied Probability (2012). Section 1 (Theorem 1, Corollary 1), Sections 2–3 (proofs). <https://doi.org/10.48550/arXiv.1109.5124>. Published version: Journal of Applied Probability 49(3) (2012), 888–894, <https://doi.org/10.1239/jap/1346955342>; locators above refer to the arXiv version.
