# SLDP first-moment identity

Let a [first-moment SLDP model](model.md) on a measure $P$ have mean effects $m = \mu v$ for a real number $\mu$ and a vector $v \in \mathbb{R}^M$, and let $X$ be a real $N \times M$ genotype matrix. Then for every marker $j$,

$$\int \hat\alpha_j \, dP = \mu\, (\hat R v)_j,$$

where $\hat\alpha$ is the vector of [normalized marginal scores](alpha-hat.md) and $\hat R$ the [in-sample LD matrix](ld-matrix.md); $\hat R v$ is the signed LD profile of $v$.

This is the exact in-sample analogue, with the in-sample LD matrix, of the first-moment part of Equation 5 in the Online Methods of the author manuscript of Reshef et al. (2018), which uses the population LD matrix and holds approximately.

## Sources

- Y. A. Reshef, H. K. Finucane, D. R. Kelley, A. Gusev, D. Kotliar, J. C. Ulirsch, et al., *Detecting genome-wide directional effects of transcription factor binding on polygenic disease risk*, Nat. Genet. 50 (2018), 1483–1493; author manuscript PMC6202062, Online Methods, Equation 5.
