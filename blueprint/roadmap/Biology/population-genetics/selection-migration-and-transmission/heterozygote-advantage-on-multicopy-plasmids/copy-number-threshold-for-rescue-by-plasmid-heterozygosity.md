# Copy-number threshold for rescue by plasmid heterozygosity

**Model.** Each bacterial cell carries $n$ plasmid copies, of which $i \in \{0,\dots,n\}$ carry a mutant allele. A cell of type $i$ divides at rate $\lambda_i = 1 + s_i$ and dies at rate $1$; before division its plasmids are replicated to $2n$ copies and split into two daughters with $n$ copies each, uniformly at random.
- *Regular replication*: every copy is duplicated once, so the $2n$ copies contain $2i$ mutants, and a daughter receives $j$ mutants with hypergeometric probability $\binom{2i}{j}\binom{2n-2i}{n-j}\big/\binom{2n}{n}$.
- *Random replication*: copies to be replicated are drawn one at a time uniformly from the current pool (a Pólya urn), then the $2n$ copies are split as above.

Under the *dominant* fitness function (heterozygote advantage), both homozygotes have $s_0 = s_n = s_{\min} < 0$ and every heterozygote $1 \le i \le n-1$ has $s_i = s_{\max} > 0$, so a cell reproduces before dying with probability $\rho_{\rm hom} = (1+s_{\min})/(2+s_{\min})$ or $\rho_{\rm het} = (1+s_{\max})/(2+s_{\max})$.

**Theorem.** A single heterozygous lineage has positive probability of establishment (and hence a declining wild-type population has positive rescue probability) if and only if $n \ge 2$ and
- with regular replication: $\displaystyle s_{\max} > \frac{2}{2n-3}$;
- with random replication: $\displaystyle s_{\max} > \frac{4n}{2n^2 - 3n - 1}$, and in the long run all heterozygote types are equally abundant among surviving cells.

Both thresholds decrease to $0$ as $n \to \infty$; for $n = 2$ they are $s_{\max} > 2$ and $s_{\max} > 8$. With a homozygous wild-type population of initial size $N_0$ declining at rate $|s_{\min}|$, per-copy mutation rate $u$, and $P_{\rm est}$ the establishment probability of a new mutation arising at a cell division — equal to $1 - Q_1$ (a single-mutant cell, Eq. (4)) under regular replication and given by Eq. (5) of Dewan and Uecker (2025) under random replication (accounting for replication and segregation of the novel mutant plasmid during its first generation) — independent rare mutations give

$$P_{\rm rescue} = 1 - \exp\!\Big(-\,u\,n\,N_0\,\frac{1 + s_{\min}}{|s_{\min}|}\,P_{\rm est}\Big).$$

## Expansion

Embed the process in discrete generations: a type-$i$ cell reproduces before dying with probability $\rho_i$ and then yields two daughters, so the mean offspring matrix is $m_{ij} = 2\rho_i\,P(i \to j)$, where $P(i \to j)$ is the probability that a given daughter has $j$ mutant copies. By the extinction criterion for multitype Galton–Watson processes (no final classes), establishment is possible exactly when the spectral radius of $M$ exceeds $1$. Homozygous types produce only homozygous offspring and are eventually lost, so only the heterozygote block $\{1,\dots,n-1\}$ matters, and there every row is multiplied by the same factor $2\rho_{\rm het}$. The threshold therefore reduces to computing the largest eigenvalue of the heterozygote block of $P(i \to j)$, which combinatorial identities give in closed form; the condition $2\rho_{\rm het}\cdot(\text{that eigenvalue}) > 1$ rearranges to the stated bounds. For $n = 2$ and regular replication, a heterozygote gives each daughter one mutant copy with probability $4/6$, so the condition is $\tfrac43\rho_{\rm het} > 1$, i.e. $s_{\max} > 2$. The rescue formula integrates the Poisson rate $u\,n\,P_{\rm est}\,\lambda_0 N_0 e^{s_{\min}t}$ of successful mutations over time.

## Sources

- I. Dewan, H. Uecker, "Evolutionary rescue of bacterial populations by heterozygosity on multicopy plasmids", Journal of Mathematical Biology (2025), Eqs. (1)–(2), (6)–(9), Theorems 1–2, Proposition 1 and Lemma 1, <https://doi.org/10.1007/s00285-025-02182-4>, PMCID PMC11799102.
