# Topology and epoch lengths are independent under a variable population size

For the variable-size coalescent with integrated intensity $\Lambda$, $\Lambda(t) \to \infty$, the holding times $T^v_n, \dots, T^v_2$ are functions of the constant-size holding times $T_n, \dots, T_2$ alone (Tavaré 2004, equation (2.4.9)), and the sequence of mergers is the jump chain of the constant-size coalescent, since the time change $A^v_n(t) = A_n(\Lambda(t))$ (equation (2.4.8)) moves the jump times but not the jumps. In Kingman's coalescent the jump chain is independent of the holding times (Tavaré 2004, Sections 2.2 and 4.1), so the topology of the variable-size genealogy, with the random-joining law, is independent of the whole family $(T^v_k)$. This is the hypothesis of the expected-spectrum identity

$$E[\xi_i] = \frac\theta2 \sum_{k=2}^n \frac{k\binom{n-i-1}{k-2}}{\binom{n-1}{k-1}}\, E[T^v_k], \qquad 1 \le i \le n - 1,$$

which therefore holds for every deterministic size history with $\Lambda(\infty) = \infty$ and integrable $T^v_k$, even though the $T^v_k$ are dependent. The expected epoch lengths are $E[T^v_k] = \int_0^\infty P(A^v_n(t) = k)\, dt = \int_0^\infty g_{nk}(\Lambda(t))\, dt$, by Tavaré's formula for $P(A_n(s) = k)$.

## Depends on

- [Clock and epoch lengths of the variable-size coalescent](../../../Biology/coalescent-theory/site-frequency-spectrum-under-variable-populatio/deterministic-coalescent-time-change.md)
- [Expected SFS under a variable population size](../../../Biology/coalescent-theory/site-frequency-spectrum-under-variable-populatio/integral-sfs-of-indep.md)
- [Tavaré's formula for the number of ancestral lineages](../../../Biology/coalescent-theory/ancestral-lineage-counting-and-tavar-s-formula/tavare-prob.md)

## Expansion

1. The time-changed coalescent on a probability space carrying the constant-size jump chain and holding times, with $T^v_k$ given by (2.4.9).
2. Measurability of $(T^v_k)$ with respect to the constant-size holding times, and the resulting independence of the topology and $(T^v_k)$.
3. The expected spectrum for a general history, from the identity for independent topology and epoch lengths.
4. The occupation-time formula $E[T^v_k] = \int_0^\infty g_{nk}(\Lambda(t))\, dt$ and its finiteness conditions.

## Sources

- S. Tavaré, Ancestral inference in population genetics, in *Lectures on Probability Theory and Statistics*, Lecture Notes in Math. 1837, Springer, 2004, 1–188, Section 2.4, equations (2.4.8), (2.4.9), and Sections 2.2, 2.3 and 4.1.
- A. Polanski and M. Kimmel, New explicit expressions for relative frequencies of single-nucleotide polymorphisms with application to statistical inference on population growth, Genetics 165 (2003), 427–436, abstract. <https://doi.org/10.1093/genetics/165.1.427>
