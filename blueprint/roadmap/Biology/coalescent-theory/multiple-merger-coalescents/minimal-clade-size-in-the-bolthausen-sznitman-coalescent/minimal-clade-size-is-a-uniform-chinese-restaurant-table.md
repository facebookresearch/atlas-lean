# Minimal clade size is a uniform Chinese restaurant table

Let $(\Pi^{(n)}_t)_{t\ge0}$ be the Bolthausen–Sznitman $n$-coalescent, the $\Lambda$-coalescent on partitions of $[n] = \{1,\dots,n\}$ with $\Lambda$ uniform on $[0,1]$. For an individual $I$ chosen uniformly from $[n]$, let $E_n = \inf\{t \ge 0 : C_I(\Pi^{(n)}_t) \neq \{I\}\}$ be the length of its external branch, where $C_i(\eta)$ is the block of $i$ in the partition $\eta$. The **minimal clade size** is

$$X_n = \big| C_I\big(\Pi^{(n)}_{E_n}\big) \big|,$$

the size of the block containing $I$ right after the first merger in which $I$ takes part. By exchangeability one may take $I = 1$.

For $m \ge 1$, the Chinese restaurant process $\mathrm{CRP}(m)$ seats customers $1,\dots,m$: customer $i$ sits to the left of one of the $i-1$ seated customers or at a new table, each of the $i$ options with probability $1/i$. Its table partition follows the Ewens sampling formula with $\theta = 1$.

**Theorem (Freund–Siri-Jégousse, main theorem of the section on the Bolthausen–Sznitman $n$-coalescent).** For $n \ge 2$, $X_n$ takes values in $\{2,\dots,n\}$, and $X_n - 1$ has the law of the size of a uniformly chosen table of a $\mathrm{CRP}(n-1)$. Moreover

$$\frac{\log X_n}{\log n} \longrightarrow U_{[0,1]} \quad \text{in distribution as } n \to \infty,$$

where $U_{[0,1]}$ is uniform on $[0,1]$.

The same law describes $M_n$, the total size of the blocks not containing $1$ that take part in the last merger, studied by Goldschmidt and Martin: the relatives of individual 1 through time, $(S^{(n)}_i \setminus \{1\})_i$, have the law of the time-reversed process of its non-relatives.

## Depends on

- [Merger rates of the Bolthausen–Sznitman coalescent](../../coalescents/merger-rate-volume.md)
- [The allelic partition of the Chinese restaurant process follows the Ewens sampling formula](../../../population-genetics/ewens-sampling-formula-and-the-chinese-restauran/crp-map-block-sizes.md)

## Expansion

Goldschmidt and Martin construct the jump chain of the Bolthausen–Sznitman $n$-coalescent from a uniform random recursive tree on $[n]$ rooted at $1$: repeatedly pick a uniform edge, cut it, and merge the labels of the detached subtree into the vertex at the root side of the cut. The subtrees attached directly to the root $1$ form an exchangeable partition of $\{2,\dots,n\}$ distributed as the tables of a $\mathrm{CRP}(n-1)$, and individual 1 absorbs these subtrees one at a time in uniformly random order. Hence the block of 1 after its $i$-th merger is $\{1\}$ together with the first $i$ tables in random order; in particular the first merger adds one uniformly chosen table, which gives the law of $X_n - 1$. The size of a uniform table of a uniform random permutation of $n-1$ elements has $\log(\text{size})/\log n$ asymptotically uniform, because a uniform permutation has about $\log n$ cycles whose log-sizes are spread evenly over $[0, \log n]$.

## Sources

- F. Freund and A. Siri-Jégousse, *Minimal clade size in the Bolthausen–Sznitman coalescent*, *Journal of Applied Probability* 51 (2014), 657–668, <https://doi.org/10.1239/jap/1409932665>; preprint arXiv:1301.2908, <https://doi.org/10.48550/arXiv.1301.2908>.
