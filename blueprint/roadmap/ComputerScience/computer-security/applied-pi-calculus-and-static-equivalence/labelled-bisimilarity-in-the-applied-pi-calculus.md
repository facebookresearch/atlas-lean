# Labelled bisimilarity in the applied pi calculus

A *labelled bisimulation* is a symmetric relation $\mathcal R$ on closed extended processes of the [applied pi calculus](terms-and-processes-of-the-applied-pi-calculus.md) such that
$A \mathrel{\mathcal R} B$ implies

1. $A \approx_s B$: the frames of $A$ and $B$ are [statically equivalent](frames-and-static-equivalence.md);
2. if $A \to A'$ and $A'$ is closed, then $B \to^* B'$ and $A' \mathrel{\mathcal R} B'$ for some $B'$;
3. if $A \xrightarrow{\alpha} A'$ (a [labelled transition](labelled-transitions-in-the-applied-pi-calculus.md)), $A'$ is closed and the free variables of $\alpha$ lie in the domain of $A$, then $B \to^* \xrightarrow{\alpha} \to^* B'$ and $A' \mathrel{\mathcal R} B'$ for some $B'$.

*Labelled bisimilarity* $\approx_l$ is the largest labelled bisimulation.

## Depends on

- [Terms and processes of the applied pi calculus](terms-and-processes-of-the-applied-pi-calculus.md)
- [Frames and static equivalence](frames-and-static-equivalence.md)
- [Labelled transitions in the applied pi calculus](labelled-transitions-in-the-applied-pi-calculus.md)
- [Internal reduction in the applied pi calculus](internal-reduction-in-the-applied-pi-calculus.md)

## Sources

- M. Abadi, B. Blanchet and C. Fournet, "The applied pi calculus: mobile values, new names, and secure communication", *Journal of the ACM* 65(1), 2018, arXiv:1609.03003v2, <https://arxiv.org/abs/1609.03003v2>: Section 4.3, Definition 4.4.
- V. Cortier and S. Kremer, "Formal models and techniques for analyzing security protocols: a tutorial", *Foundations and Trends in Programming Languages* 1(3), 2014, doi:10.1561/2500000001, copy at <https://inria.hal.science/hal-01090874>: Section 5.3.3, Definition 5.2.
