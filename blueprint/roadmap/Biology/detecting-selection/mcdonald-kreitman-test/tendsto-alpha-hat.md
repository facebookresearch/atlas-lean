# Consistency of the adaptive proportion estimator over loci

Let an [expected-count model](mkmodel.md) be given, let $\mu$ be a measure, and let $(D_{n,i})_{i \ge 0}$, $(D_{s,i})$, $(P_{n,i})$, $(P_{s,i})$ be four sequences of real random variables (the counts at locus $i$). Suppose that, for each of the four sequences, the variables are pairwise independent and identically distributed under $\mu$, the first one is $\mu$-integrable, and its integral is the corresponding expected count: $\int D_{n,0} \, d\mu = \mathbb{E}D_n$, $\int D_{s,0} \, d\mu = \mathbb{E}D_s$, $\int P_{n,0} \, d\mu = \mathbb{E}P_n$, $\int P_{s,0} \, d\mu = \mathbb{E}P_s$. Then for $\mu$-almost every outcome,

$$\hat\alpha\Bigl(\sum_{i < m} D_{n,i}, \sum_{i < m} D_{s,i}, \sum_{i < m} P_{n,i}, \sum_{i < m} P_{s,i}\Bigr) \to \alpha \qquad (m \to \infty),$$

where $\hat\alpha$ is the [estimator](alpha-hat.md) and $\alpha$ the [proportion of adaptive substitutions](alpha.md).
