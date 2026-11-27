# Poisson mutation likelihood on time-resolved mutation trees

**Setting.** A mutation tree $T$ has root $0$ and nodes $0, \dots, n$; node $i$ stands for the mutation creating subclone $i$, has out-degree $d_i$, and its children are the subclones born from $i$. Each subclone $i$ acquires new mutations as a Poisson process with its own rate $\theta_i > 0$ (its **mutability**). Let $t_i$ be the birth time of subclone $i$ ($t_0 = 0$) and $H$ the common sampling time. Because sibling birth orders are not determined by $T$, a time-resolved binary phylogeny is specified by an ordering $\sigma_i = (\sigma_{i,0} = i, \sigma_{i,1}, \dots, \sigma_{i,d_i})$ of the children of every node, with $t_{\sigma_{i,0}} \le t_{\sigma_{i,1}} \le \cdots \le H$.

**Likelihood.** Intervals between consecutive births from clone $i$ are Erlang with shape 2 and rate $\theta_i$, and the last interval before sampling is exponential, so

$$p(T \mid \theta, t, H, \sigma) = \prod_{i=0}^{n}\Big(\prod_{j=1}^{d_i}\theta_i^2\,(t_{\sigma_{i,j}} - t_{\sigma_{i,j-1}})\,e^{-\theta_i (t_{\sigma_{i,j}} - t_{\sigma_{i,j-1}})}\Big)\,\theta_i\,e^{-\theta_i (H - t_{\sigma_{i,d_i}})},$$

$$L(T \mid \theta, t, H, \sigma) = \sum_{i=0}^n \theta_i t_i + \sum_{i=0}^n\sum_{j=1}^{d_i}\log(t_{\sigma_{i,j}} - t_{\sigma_{i,j-1}}) - H\sum_{i=0}^n \theta_i + \sum_{i=0}^n (2d_i + 1)\log\theta_i .$$

For fixed $\sigma$ and $\theta$, maximizing over $t, H$ is a convex problem with linear constraints, and for fixed times $\partial L/\partial\theta_i = t_i - H + (2d_i + 1)/\theta_i$, so the maximizing rates are $\theta_i = (2d_i + 1)/(H - t_i)$. (The source uses $\theta_i = d_i/(H - t_i)$ as the expected-rate update of its EM procedure, Eq. 4, not as this maximizer.)

**Theorem (stable optimal orderings).** Fix $\theta$ and let $L_{T,\theta}(H) = \max_{\sigma, t} L(T \mid \theta, t, H, \sigma)$. For all sufficiently large $H$ the maximizing ordering is the same and has the recursive form $\sigma^* = \{\sigma_0^*\} \cup \bigcup_{k=1}^{d} \sigma_k^*$, where $\sigma_k^*$ is an optimal ordering of the subtree rooted at the $k$-th child of the root and $\sigma_0^*$ is the permutation of the root's children maximizing the recurrence

$$L_{T,\theta}(H) \approx \max_{\sigma_0}\max_{0 \le t_1 \le \cdots \le t_d \le 1}\Big(H\sum_k \Theta_k t_k + \sum_k \log(t_k - t_{k-1}) + \sum_k n_k \log(1 - t_k) + \sum_k L_{T_k,\theta_k}((1 - t_k)H)\Big) - \Theta_0 H + n\log H + \sum_i (2d_i + 1)\log\theta_i,$$

with times rescaled by $H$, $n_k$ the size of subtree $T_k$ and $\Theta_k$ its total rate.

## Expansion

Rescaling times by $H$ separates the log-likelihood into a term linear in $H$, which rewards placing high-total-rate subtrees early, and lower-order logarithmic terms. For large $H$ the linear term dominates and its maximizer does not depend on $H$, so optimal sub-orderings found for subtrees remain optimal inside the parent problem. This makes a dynamic program exact: optimize each subtree recursively, then search only over permutations of each node's children, with cost $O(\sum_i T(n_i)\,d_i!)$ for convex solves of size $n_i$, instead of the $\prod_i d_i!$ joint orderings. Alternating this step with the rate update gives an EM procedure for inferring subclone-specific mutation rates from single-cell mutation trees; constrained variants allow at most $s$ rate changes on the tree.

## Sources

- V. Tsyvina, A. Zelikovsky, S. Snir, P. Skums, "Inference of mutability landscapes of tumors from single cell sequencing data", PLoS Computational Biology 16(11) (2020) e1008454, Section 2.1 (Eqs 1–3), Section 2.2 (Algorithms 1–2, Eq 4, Lemma 1 with Eq 6, Theorem 1) and Section 2.3, <https://doi.org/10.1371/journal.pcbi.1008454>, PMCID PMC7728263.
