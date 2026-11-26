# Graded-response cumulative probability at a threshold

In the graded-response model with discrimination $a$, thresholds $b_1, \dots, b_m$ and ability $\theta$ (all real), the cumulative value at index $j + 1$, for $j < m$, is $\sigma(a(\theta - b_{j+1}))$, where $\sigma(u) = 1/(1 + e^{-u})$ is the logistic function. These values are cumulative category probabilities, nonincreasing in the index, when for example $a \ge 0$ and the thresholds are nondecreasing; for other parameters they need not be monotone.

## Sources

- J. P. Weeks, "plink: An R package for linking mixed-format tests using IRT-based methods", Journal of Statistical Software 35(12) (2010), equation (2).
