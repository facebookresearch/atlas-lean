---
article_id: af_6670cfcb118bb5b97ea6c908
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: TotalVariation.defProp_5_4
---

# Definition-Proposition 5.4

The total variation distance between two probability measures $\mathbb{P}_0$ and $\mathbb{P}_1$ on a measurable space $(\mathcal{X}, \mathcal{A})$ is defined by $$\mathsf{TV}(\mathbb{P}_0, \mathbb{P}_1) = \sup_{R \in \mathcal{A}} |\mathbb{P}_0(R) - \mathbb{P}_1(R)| = \sup_{R \in \mathcal{A}} \left| \int_{R} p_0 - p_1 \right| = \frac{1}{2} \int |p_0 - p_1| = 1 - \int \min(p_0, p_1) = 1 - \inf_{\psi} \left[ \mathbb{P}_0(\psi = 1) + \mathbb{P}_1(\psi = 0) \right]$$ where the infimum above is taken over all tests.

## Depends on

This node has no prerequisites.

## Proof depends on

- [Lemma 5.3 (Neyman-Pearson)](061-neyman-pearson.md)

## Sources

- [MIT 18.S997 High-Dimensional Statistics (Spring 2015), Section 5.3](../../../../sources/v1/HighDimensionalStatistics.md)
