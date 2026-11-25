# Weak PAC learnability

A concept class $C$ is weakly PAC learnable over a family $\mathcal{D}$ of distributions if there is an accuracy $\varepsilon \in (0, 1)$ with $\varepsilon < 1/2$ such that for every confidence $\delta \in (0, 1)$ some sample size $m$ admits a learner that, for every $D \in \mathcal{D}$, outputs with probability at least $1 - \delta$ over $m$ i.i.d. examples a hypothesis of error at most $\operatorname{opt}_C(D) + \varepsilon$.

Because the learners here are measured against $\operatorname{opt}_C(D)$, this matches Kearns and Valiant's notion only when every distribution in $\mathcal{D}$ is realizable ($\operatorname{opt}_C(D) = 0$), as for the realizable family used in [the converse](is-paclearnable-realizable-family.md); over other distributions it is an agnostic variant. On realizable distributions it is Kearns and Valiant's notion, as stated by Schapire, without its computational part. Schapire's definition also requires the learner to run in polynomial time and lets the advantage $1/2 - \varepsilon$ shrink as an inverse polynomial in the size parameters; the definition here counts examples only.

## Sources

- R. E. Schapire, "The strength of weak learnability", *Machine Learning* 5 (1990), 197–227, Section 2.
