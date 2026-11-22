# One step of the collapsed forward recursion

Let $R$ be a field and $\rho, \varepsilon \in R$. For a [site observation](obs.md) $o$, a vector $v \in R^K$ of forward variables and a haplotype $k$, the collapsed forward step is

$$\Phi(o, v)(k) = e_\varepsilon(k, o)\Bigl((1 - \rho)\, v_k + \frac{\rho}{K} \sum_{j=1}^{K} v_j\Bigr),$$

where $e_\varepsilon$ is the [emission weight](emit.md) and $x/0 = 0$.
