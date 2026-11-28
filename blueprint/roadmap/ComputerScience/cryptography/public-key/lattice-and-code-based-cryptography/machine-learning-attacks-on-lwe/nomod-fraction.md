# The NoMod fraction of an LWE training set

For a known secret and a training set of $N\ge1$ LWE pairs written in centred representatives, counted with repetition, the NoMod fraction is the share of indices $j$ with $|a_j\cdot s-b_j|<q/2$ over the integers; when the integer errors lie in $(-q/2,q/2)$ this is the share of labels formed without a modular wrap.

Let $q$ be odd, $s$ a known secret with small integer entries, and $(a_j,b_j)_{j=1}^{N}$, $N\ge1$, a training set of pairs indexed with repetition, with coordinates represented in $(-q/2,q/2)$. Put $x_j=a_j\cdot s-b_j$, computed over the integers. The **NoMod** fraction is

$$
\mathrm{NoMod}=\frac{\#\{j\in\{1,\dots,N\}:\ |x_j|<q/2\}}{N} .
$$

If $b$ is the representative of $a\cdot s+e$ for an integer error $e$ with $|e|<q/2$, then $b=a\cdot s+e-kq$ for an integer $k$, $x=kq-e$, and $|x|<q/2$ holds exactly when $k=0$, i.e. when forming $b$ needed no reduction modulo $q$. Without the error bound the criterion and the absence of a wrap can differ. The fraction needs $s$, so it explains rather than runs an attack.

**Observation and model (SALSA VERDE).** In 210 experiments with $n=256$, $\log_2q=20$, secrets were recovered only when NoMod exceeded about $67\%$. A Gaussian model of $x$ for a binary secret of weight $h\gg1$, with $\sigma_x\approx\sqrt h\,\sigma_a$ for coordinates of $a$ of standard deviation $\sigma_a$ and ignoring correlations and the error, suggests recoverability when $\sqrt h\,\sigma_a\le q/2$; for uniform $a$, approximating the standard deviation of a uniform coordinate by $q/\sqrt{12}$ gives $h\le3$. Both are empirical or model statements.

## Expansion

The no-wrap criterion: if $k\ne0$ then $|kq-e|\ge q-|e|>q/2$. The same paper proposes, when recovery fails, to permute the columns of the original (unreduced) sample matrices, rerun the preprocessing on the permuted matrices and attack the correspondingly permuted secret; NoMod of the new training set can then differ (its Table 7). The scaling model is reported to underestimate the recovered $h$ by about a factor of two after preprocessing.

## Depends on

- [LWE with a prescribed secret distribution](../small-and-sparse-secret-lwe/lwe-with-a-secret-distribution.md)
- [Reduced LWE pairs from lattice reduction of the sample matrix](reduced-lwe-samples.md)

## Proof depends on

None.

## Sources

- Cathy Yuanchen Li, Emily Wenger, Zeyuan Allen-Zhu, François Charton, Kristin Lauter, "SALSA VERDE: a machine learning attack on Learning With Errors with sparse small secrets", Advances in Neural Information Processing Systems 36 (NeurIPS 2023); numbers from arXiv:2306.11641v2, Section 5 (NoMod definition, Figure 4, Table 7) and Section 6 (scaling law).
