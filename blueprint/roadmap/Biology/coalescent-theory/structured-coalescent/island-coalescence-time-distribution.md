# Distribution of the pairwise coalescence time in the island model

For two lineages in the finite island model with $d \ge 2$ demes and scaled migration rate $M > 0$, the coalescence time $T$ is the absorption time of a chain with two transient states, same deme ($s$) and different demes ($\delta$), whose transient generator, from the island-model rates, is

$$S = \begin{pmatrix} -(1 + M) & M \\ M/(d - 1) & -M/(d - 1) \end{pmatrix}.$$

Hence, for a start in state $i$, $P_i(T > t) = e_i^{\top} e^{tS}\mathbf 1$, and since coalescence occurs only from the same-deme state, at rate $1$, the density of $T$ is $f_i(t) = P_i(X_t = s)$. The eigenvalues of $S$ are $-\alpha$ and $-\beta$, the roots of $x^2 + (1 + M + b)x + b = 0$ with $b = M/(d - 1)$; the discriminant is $(1 + M - b)^2 + 4Mb > 0$, so $\alpha \ne \beta$ are real and positive, and both the survival function and the density are combinations of $e^{-\alpha t}$ and $e^{-\beta t}$. Integrating the survival function, $E_i[T] = e_i^{\top}(-S)^{-1}\mathbf 1$, which gives $d$ and $d + (d - 1)/M$. This is a direct derivation; the inverse instantaneous coalescence rate of the island model is computed from this two-exponential law.

## Depends on

- [Transition rates of the two-lineage structured coalescent](../../../Biology/coalescent-theory/structured-coalescent/rate.md)
- [Exit rate of a structured-coalescent state](../../../Biology/coalescent-theory/structured-coalescent/exit-rate.md)
- [Closed-form mean coalescence times in the island model](../../../Biology/coalescent-theory/structured-coalescent/mean-coalescence-time.md)

## Expansion

1. The transient generator $S$ from the island-model rates and the phase-type representation of $T$ for both sampling schemes.
2. The density as the probability of being in the same-deme state, and the eigenvalues $-\alpha$, $-\beta$ with the discriminant identity.
3. The mean as $e_i^{\top}(-S)^{-1}\mathbf 1$, recovering the closed-form mean coalescence times.
4. The explicit weights of the two exponentials for each sampling scheme, as the input to the inverse instantaneous coalescence rate of the island model.

## Sources

- O. Mazet, W. Rodríguez, S. Grusea, S. Boitard and L. Chikhi, On the importance of being structured: instantaneous coalescence rates and human evolution—lessons for ancestral population size inference?, Heredity 116 (2016), 362–371, section Linking population structure and population size change (the $n$-island coalescence-time density in the same two-exponential form). <https://doi.org/10.1038/hdy.2015.104>
