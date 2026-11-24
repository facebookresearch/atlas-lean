# Decomposition of the admixture EM objective

Let $I$ and $J$ be finite and $g$ a genotype matrix with entries in $\{0, 1, 2\}$. For all [admixture parameters](params.md) $\theta' = (Q', F')$ and $\theta$,

$$\mathcal{Q}(\theta' \mid \theta) = \sum_{i \in I} \sum_{k \in K} A_{ik}(\theta) \log Q'_{ik} + \sum_{k \in K} \sum_{j \in J} \Bigl(R_{kj}(\theta) \log F'_{kj} + S_{kj}(\theta) \log(1 - F'_{kj})\Bigr),$$

where $\mathcal{Q}$ is the EM objective of the [EM theorem](admixture-log-lik-le-of-em-q-le.md), $A$ the [expected ancestry counts](anc-count.md), and $R$, $S$ the [expected reference](ref-count.md) and [alternative](alt-count.md) counts.
