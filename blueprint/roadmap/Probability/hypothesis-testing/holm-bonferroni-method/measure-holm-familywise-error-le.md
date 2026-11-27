# Holm's procedure controls the FWER

Let $\mu$ be a measure on $\Omega$, $p_0, \dots, p_{m-1} : \Omega \to \mathbb{R}$ and $H_0 \subseteq \{0, \dots, m-1\}$ the set of true nulls, each $p_i$ with $i \in H_0$ being a valid p-value under $\mu$ ($\mu(p_i \le t) \le t$ for $t \in [0,1]$). For every $\alpha \in [0, 1]$, the probability that Holm's step-down procedure at level $\alpha$ rejects at least one true null is at most $\alpha$:

$$\mu(R \cap H_0 \ne \emptyset) \le \alpha,$$

where $R$ is the [Holm rejection set](holm-rejections.md) of $(p_0(\omega), \dots, p_{m-1}(\omega))$. No independence is assumed.

## Sources

- S. Holm, *A simple sequentially rejective multiple test procedure*, Scand. J. Statist. 6 (1979), 65–70.
