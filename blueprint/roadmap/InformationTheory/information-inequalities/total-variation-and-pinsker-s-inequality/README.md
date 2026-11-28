# Total variation and Pinsker's inequality

For probability measures on an arbitrary measurable space, the total variation distance $\mathrm{TV}(\mu, \nu) = \sup_B |\mu(B) - \nu(B)|$ is attained at a Hahn set, equals half of the total variation norm $\|\mu - \nu\|$, and determines the least total error $1 - \mathrm{TV}(\mu, \nu)$ of a test between $\mu$ and $\nu$. Pinsker's inequality $2\,\mathrm{TV}(\mu, \nu)^2 \le D(\mu \,\|\, \nu)$ holds with no positivity or absolute-continuity hypothesis; its proof applies the data-processing inequality for the Kullback–Leibler divergence to the indicator of a Hahn set and reduces to two Bernoulli laws. The Bretagnolle–Huber inequality $\mu(A) + \nu(A^c) \ge \frac12 e^{-D(\mu \,\|\, \nu)}$ bounds the total error of a test from below by the divergence alone, and stays informative when the divergence is large.

- [An event's probabilities differ by at most the total variation](abs-sub-le-total-variation-dist.md)
- [The optimal test has total error 1 − TV](exists-add-compl-eq-one-sub-total-variat.md)
- [Common part of two probability measures](exists-le-le-measure-univ-eq.md)
- [Pinsker's inequality for the total variation norm](of-real-tv-dist-sq-div-two-le-kl-div.md)
- [Pinsker's inequality for probability measures](of-real-two-mul-total-variation-dist-sq.md)
- [Two-point testing bound](one-sub-total-variation-dist-le-add-comp.md)
- [Total variation is attained at a Hahn set](total-variation-dist-eq-of-is-hahn-decom.md)
- [Pinsker's inequality, square-root form](total-variation-dist-le-sqrt-kl-div.md)
- [Bretagnolle–Huber inequality](bretagnolle-huber-inequality.md)
- [Total variation norm is twice the supremum over events](tv-dist-eq-two-mul-total-variation-dist.md)

## Related topics

- [Total variation distance](../../../Probability/convergence-of-measures/total-variation-distance/README.md)
- [Strong data processing and Dobrushin's coefficient](../strong-data-processing-and-dobrushin-s-coefficie/README.md)
- [Minimax lower bounds](../../../Probability/statistical-estimation/minimax-lower-bounds/README.md)
- [Donsker–Varadhan variational formula](../donsker-varadhan-variational-formula/README.md)
- [Hellinger distance](../../../Probability/convergence-of-measures/hellinger-distance/README.md): another distance between probability measures, comparable to total variation on both sides.
