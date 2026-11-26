# Shaping conserves arrival constraints

Assume a flow with [arrival curve](arrival-curves.md) $\alpha$ is input to a [greedy shaper](greedy-shapers.md) whose shaping curve $\sigma$ is good. Then the output flow is still constrained by the original arrival curve $\alpha$, so it has $\min(\alpha, \sigma)$ as an arrival curve, and $\alpha \otimes \sigma$ when $\alpha$ is good as well. Shaping cannot be undone by shaping.

**Proof.** $R^* = R \otimes \sigma \le (R \otimes \alpha) \otimes \sigma = (R \otimes \sigma) \otimes \alpha = R^* \otimes \alpha$.

## Depends on

- [Greedy shapers](greedy-shapers.md)
- [Sub-additive closure](min-plus-algebra/sub-additive-closure.md): the good curves.

## Proof depends on

- [Input-output characterization of greedy shapers](input-output-characterization-of-greedy-shapers.md)
- [Arrival curves as min-plus inequalities](arrival-curves-as-min-plus-inequalities.md)
- [Algebraic properties of min-plus convolution](min-plus-algebra/algebraic-properties-of-min-plus-convolution.md)

## Sources

- J.-Y. Le Boudec and P. Thiran, *Network Calculus: A Theory of Deterministic Queuing Systems for the Internet*, Lecture Notes in Computer Science 2050, Springer, 2001; online version of 2022, <https://leboudec.github.io/netcal/latex/netCalBook.pdf>, whose numbering is used here, Section 1.5.3, Theorem 1.5.3 with its proof, and Lemma 1.2.5 (the sub-additive closure of $\min(\gamma_1, \gamma_2)$ for good $\gamma_1, \gamma_2$ is $\gamma_1 \otimes \gamma_2$).
