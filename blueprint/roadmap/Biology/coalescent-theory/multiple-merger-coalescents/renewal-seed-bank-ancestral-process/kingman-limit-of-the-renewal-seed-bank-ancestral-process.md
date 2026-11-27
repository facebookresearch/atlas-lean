# Kingman limit of the renewal seed-bank ancestral process

Consider a haploid population of constant size $N$ in discrete generations indexed by $\mathbb Z$. Fix a probability measure $\mu$ on $\mathbb N = \{1,2,\dots\}$ with $\mu(\{1\}) > 0$, the **seed-bank age distribution**: an individual of generation $i$ chooses the generation $i - \eta$ of its parent with $\eta \sim \mu$, and then the parent uniformly among the $N$ individuals of that generation, independently of everything else. The ancestral line of one individual therefore visits generations $0 > -S_1 > -S_2 > \cdots$, where $S_l = \eta_1 + \dots + \eta_l$ is a discrete renewal process with interarrival law $\mu$; let $q_n$ be the probability that $n$ is a renewal time, so an individual of generation $i_w < i_v$ is an ancestor of $v$ with probability $q_{i_v - i_w}/N$. Lines that hit a common ancestor merge.

For a sample of $n \le N$ individuals from generation $0$, let $A_{N,n}(k)$ be the partition of $\{1,\dots,n\}$ into classes of individuals sharing an ancestor at most $k$ generations back.

**Theorem.** If $\mathbb E_\mu[\eta] < \infty$, set $\beta = 1/\mathbb E_\mu[\eta]$. As $N \to \infty$,

$$\big(A_{N,n}(\lfloor N t/\beta^2 \rfloor)\big)_{t \ge 0} \Longrightarrow \text{Kingman's } n\text{-coalescent}$$

weakly in the Skorokhod space. In particular, for two individuals with a common ancestor, $\lim_{N\to\infty} \mathbb E[\tau]/N = 1/\beta^2$, where $\tau$ is their time to the most recent common ancestor.

This extends the bounded-age seed bank of Kaj, Krone and Lascoux to unbounded age distributions with finite mean: the seed bank only slows coalescence by the factor $(\mathbb E_\mu\eta)^2$.

## Depends on

- [Weak seed bank: Kingman coalescent with rates multiplied by 1/(E B)^2](../../structured-coalescent/seed-bank-coalescent/weak-seed-bank-kingman-coalescent-with-rates-mul.md)

## Expansion

Track, for the $n$ sampled lines, the configuration process $X^{N,n}(k)$ recording how many lines currently sit at each forward distance from the present generation (the urn process of Kaj et al.). Without mergers it is the joint process of independent renewal "ages" and, when $\mathbb E_\mu\eta < \infty$, it is positive recurrent with a product stationary law $\nu^n$. Given configuration $x$, one pair of lines merges in the next step with probability $N^{-1}\sum_i (x_1 x_{i+1}\mu(i) + \binom{x_1}{2}\mu(i)^2) + O(N^{-2})$, and multiple mergers have probability $O(N^{-2})$. Averaging the pair-merger rate against $\nu^n$ gives $\beta^2\binom{n}{2}/N$, and a separation-of-time-scales lemma (fast configuration chain, slow mergers) yields the Kingman limit on time scale $N/\beta^2$.

## Sources

- Jochen Blath, Adrián González Casanova, Noemi Kurt, Dario Spanò, "The ancestral process of long term seed bank models", published as "The Ancestral Process of Long-Range Seed Bank Models", *Journal of Applied Probability* 50 (2013), 741–759, <https://doi.org/10.1239/jap/1378401233>; preprint arXiv:1203.5202, <https://doi.org/10.48550/arXiv.1203.5202>. Numbering of the arXiv version: Section 2.1 (renewal construction, Theorem 2.1, Theorem 2.2(c)), Section 3.1 (Lemmas 3.1 and 3.2).
