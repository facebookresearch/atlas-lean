# Unbiasedness of the summed Hudson denominator estimator

Let $\mu$ be a measure and $s$ a finite set of sites. For each $i \in s$ let $m_{A,i}, m_{B,i} \ge 1$, $q_{A,i}, q_{B,i} \in [0, 1]$, and let $X_{A,i}, X_{B,i}$ be independent under $\mu$ with binomial laws $\mathrm{Bin}(m_{A,i}, q_{A,i})$ and $\mathrm{Bin}(m_{B,i}, q_{B,i})$. Then

$$\int \sum_{i \in s} \hat D(m_{A,i}, m_{B,i}, X_{A,i}, X_{B,i}) \, d\mu = \sum_{i \in s} D(q_{A,i}, q_{B,i}),$$

where $\hat D$ is the [denominator estimator](hudson-den-hat.md) and $D$ [Hudson's denominator](hudson-den.md).
