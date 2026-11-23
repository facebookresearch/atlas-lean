# The number of alleles is sufficient for the mutation parameter

Let $\theta > 0$. Then for every partition $\pi$ of $n$,

$$P_\theta(\pi \mid K = K(\pi)) = \frac{w(\pi)}{\sum_{\pi' :\, K(\pi') = K(\pi)} w(\pi')},$$

where the left side is the [conditional probability](ewens-cond-prob.md) and $w$ the [cycle-type weight](cycle-type-weight.md): the conditional law of the allelic partition given the number of alleles does not depend on $\theta$ (Ewens 1972).

## Sources

- W. J. Ewens, *The sampling theory of selectively neutral alleles*, Theor. Popul. Biol. 3 (1972), 87–112.
