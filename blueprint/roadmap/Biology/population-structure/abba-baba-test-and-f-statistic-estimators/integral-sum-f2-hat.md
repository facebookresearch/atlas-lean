# Unbiasedness of the summed f2 estimator

Let $\mu$ be a measure and $s$ a finite set of sites. For each $i \in s$ let $m_{A,i}, m_{B,i} \ge 2$, $q_{A,i}, q_{B,i} \in [0, 1]$, and let $X_{A,i}, X_{B,i}$ be independent under $\mu$ with binomial laws $\mathrm{Bin}(m_{A,i}, q_{A,i})$ and $\mathrm{Bin}(m_{B,i}, q_{B,i})$. Then

$$\int \sum_{i \in s} \hat f_2(m_{A,i}, m_{B,i}, X_{A,i}, X_{B,i}) \, d\mu = \sum_{i \in s} (q_{A,i} - q_{B,i})^2,$$

where $\hat f_2$ is the [f2 estimator](f2-hat.md). Independence is needed only within each site.
