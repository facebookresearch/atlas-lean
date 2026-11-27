# Conditional surrogate risk

For a loss $\varphi : \mathbb{R} \to \mathbb{R}$, a conditional probability $\eta = \mathbb{P}(Y = 1 \mid X = x)$ and a real prediction $\alpha$,

$$C_\eta(\alpha) = \eta\, \varphi(\alpha) + (1 - \eta)\, \varphi(-\alpha),$$

the expected margin loss $\mathbb{E}[\varphi(Y \alpha) \mid X = x]$ with labels $Y \in \{-1, 1\}$.

## Sources

- P. L. Bartlett, M. I. Jordan and J. D. McAuliffe, *Convexity, classification, and risk bounds*, Journal of the American Statistical Association 101 (2006) 138–156; numbering of the technical report version <https://www.stat.berkeley.edu/~bartlett/papers/bjm-ccrb-05.pdf>, Section 2.2.
