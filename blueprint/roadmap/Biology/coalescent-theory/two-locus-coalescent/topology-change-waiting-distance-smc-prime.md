# Topology-unchanging probability and the waiting distance between topology changes

Keep the notation of the SMC' tree-unchanging probability: a sample of size $n$, epoch lengths $T_i$,
coalescence times $\sigma_i$, lineage counts $A_n(t)$, branch endpoints $t_b^l$ and $t_b^u$, total branch
length $L(\mathcal{T})$, and the coefficients

$$P_{ii} = -\frac1i e^{-i\sigma_i}, \qquad P_{ij} = \exp\Bigl(-i\sigma_i - \sum_{k=j+1}^{i-1} k T_k\Bigr)\frac1j\bigl(1-e^{-jT_j}\bigr).$$

For a branch $b$ let $b'$ be the branch it coalesces with and $c$ their parental branch, labelled so that
$t_b^l \le t_{b'}^l$. Under the SMC', the probability that a recombination event does not change the tree
topology is
$$\mathbb{P}(\text{topology unchanged} \mid \mathcal{T}) = \frac{1}{L(\mathcal{T})}\sum_{b=1}^{2n-2}
\Bigl[\sum_{i = A_n(t_{b'}^l)+1}^{A_n(t_b^l)} p_{b,1}(i) + \sum_{i = A_n(t_{b'}^u)+1}^{A_n(t_{b'}^l)} p_{b,2}(i)\Bigr],$$
where

$$p_{b,1}(i) = \frac1i\Bigl[T_i + \bigl(e^{i\sigma_i} - e^{i\sigma_{i+1}}\bigr)\Bigl(\sum_{j = A_n(t_{b'}^u)+1}^{A_n(t_{b'}^l)} P_{ij} + \sum_{j = A_n(t_c^u)+1}^{i} P_{ij}\Bigr)\Bigr],$$

$$p_{b,2}(i) = \frac1i\Bigl[2T_i + \bigl(e^{i\sigma_i} - e^{i\sigma_{i+1}}\bigr)\Bigl(2\sum_{j = A_n(t_c^u)+1}^{i} P_{ij} - \sum_{j = A_n(t_c^u)+1}^{A_n(t_c^l)} P_{ij}\Bigr)\Bigr].$$

Write $\beta(\mathcal{T}) = 1 - \mathbb{P}(\text{topology unchanged} \mid \mathcal{T})$. The waiting
distance to the next topology change is not exactly exponential, because recombinations that change the
tree without changing the topology alter the intensity of the remaining process. Using the empirical
observation that the product $L(\mathcal{T})\beta(\mathcal{T})$ is nearly unchanged by a
topology-unchanging recombination, even though $L(\mathcal{T})$ and $\beta(\mathcal{T})$ separately are
not, the distribution is approximated by
$$p_r(d \mid \mathcal{T}) \approx \frac{\rho}{2}\,\beta(\mathcal{T})\,L(\mathcal{T})\,
\exp\Bigl[-\frac{\rho}{2}\,\beta(\mathcal{T})\,L(\mathcal{T})\,d\Bigr].$$

## Depends on

- [Probability that a recombination leaves the local tree unchanged under the SMC'](smc-prime-tree-unchanging-probability.md)
- [Waiting distance until the next tree change under the SMC'](waiting-distance-until-next-tree-change-smc-prime.md)

## Expansion

The topology survives a recombination in three ways rather than one: the detached lineage can rejoin the
branch it left, or rejoin the sibling branch once both are available, or rejoin the parental branch $c$,
each of which rearranges coalescence times without rearranging the topology. Splitting the breakpoint
range into $[t_b^l, t_{b'}^l]$, where only a return to $b$ is harmless, and $[t_{b'}^l, t_{b'}^u]$, where
a return to either $b$ or $b'$ is harmless, and integrating the same no-earlier-reattachment factor as in
the tree-unchanging computation produces $p_{b,1}$ and $p_{b,2}$; the factor $2$ in $p_{b,2}$ is the two
admissible target branches. The thinning argument that gives an exact exponential for tree changes fails
here because the surviving tree is a different tree, with a different topology-changing probability; the
approximation replaces that inhomogeneity with the observed near-constancy of
$L(\mathcal{T})\beta(\mathcal{T})$, a tree with longer deep branches having both larger length and
smaller $\beta$.

## Sources

- Y. Deng, Y. S. Song and R. Nielsen, "The distribution of waiting distances in ancestral recombination graphs", Theoretical Population Biology 141 (2021), 34-43, <https://doi.org/10.1016/j.tpb.2021.06.003> (PMC8556732). (Theorem 3 and Equation 5.)
