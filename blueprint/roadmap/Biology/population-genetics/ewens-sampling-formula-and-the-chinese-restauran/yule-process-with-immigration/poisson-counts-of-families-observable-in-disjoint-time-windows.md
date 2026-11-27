# Poisson counts of families observable in disjoint time windows of a Yule process with immigration

**Model.** Immigrants arrive at the points of a Poisson process of rate $\theta > 0$; each founds a family that grows as a Yule (pure-birth) process with unit birth rate, so a family started $t$ time units ago has geometric size $\mathbb{P}(B(t) = j) = e^{-t}(1-e^{-t})^{j-1}$, $j \ge 1$. At time $t$ the numbers $C_i(t)$ of families of size $i$ are independent Poisson with means $\theta(1-e^{-t})^i/i$, which is the dynamic version of the Ewens sampling formula. A family is **observable** in an interval $(a,b)$ if it has at least one birth in $(a,b)$ (the arrival of its founding immigrant counts as a birth). Let $S(a,b)$ be the number of families observable in $(a,b)$.

**Theorem.**
1. For $0 \le a < b$, $S(a,b)$ is Poisson with mean

$$\mathbb{E}\,S(a,b) = \theta\log\big(e^b - e^a + 1\big).$$

2. For $0 \le a < b \le c < d$, write $I_1 = (a,b)$, $I_2 = (c,d)$, let $K(I_1,I_2)$ count families observable in both windows and $T(I_1 \setminus I_2)$, $T(I_2 \setminus I_1)$ those observable in only one. These three counts are independent Poisson variables with means

$$\mathbb{E}K = \theta\log\frac{(e^b - e^a + 1)(e^d - e^c + 1)}{e^d - e^c + e^b - e^a + 1}, \quad \mathbb{E}T(I_1\setminus I_2) = \theta\log\frac{e^d - e^c + e^b - e^a + 1}{e^d - e^c + 1},$$

and symmetrically for $T(I_2 \setminus I_1)$. Hence $\mathrm{Cov}\big(S(a,b), S(c,d)\big) = \mathbb{E}K(I_1,I_2) > 0$.
3. (*Fisher's sampling problem.*) Take sample sizes $n_1, \dots, n_p$, cumulative totals $l_i = n_1 + \dots + n_i$, and times $t_i = \log(\theta + l_i) - \log\theta$ at which the expected population $\theta(e^{t_i}-1)$ equals $l_i$. Then $\widetilde S_i = S(t_{i-1}, t_i)$ is Poisson with mean $\theta\log\frac{\theta + n_i}{\theta}$, $\mathrm{Cov}(\widetilde S_i, \widetilde S_j) = \theta\log\frac{(\theta + n_i)(\theta + n_j)}{\theta(\theta + n_i + n_j)}$ for $i \neq j$, and for equal sample sizes $n_i = n$ the expected sample variance $\widetilde V_p = \frac{1}{p(p-1)}\sum_{i<j}(\widetilde S_i - \widetilde S_j)^2$ is

$$\mathbb{E}\,\widetilde V_p = \theta\log\frac{2n + \theta}{n + \theta} \ \longrightarrow\ \theta\log 2 \quad (n \to \infty),$$

as Fisher surmised.

## Expansion

Families are the points of the immigration process, marked by their birth histories; by the marking theorem, the families with a given observability pattern form independent Poisson processes, so all the counts are Poisson and the different patterns are independent. The means come from integrating, over arrival times $u$, the probability that a family started at $u$ has (or lacks) births in each window, computed from the Yule generating function $\phi(t;s) = e^{-t}s/(1 - (1-e^{-t})s)$ and its integral $\int_a^b \phi(c-u;s)\,du = \log\frac{1 - (1-e^{-(c-b)})s}{1 - (1-e^{-(c-a)})s}$. Given the population sizes, the family configuration process is that of the Chinese restaurant process, which links the continuous-time picture to discrete sequential sampling.

## Sources

- Poly H. da Silva, Arash Jamshidpey and Simon Tavaré, "Another view of sequential sampling in the birth process with immigration", *Journal of Mathematical Biology* 88 (2024), 27, <https://doi.org/10.1007/s00285-023-02041-0>. Numbering as in the preprint arXiv:2210.07307v2, <https://arxiv.org/abs/2210.07307v2>: Corollaries 1–3 and Theorems 1–3.
