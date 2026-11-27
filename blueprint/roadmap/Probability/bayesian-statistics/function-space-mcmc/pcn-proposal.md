# The pCN proposal map

Let $E$ be a real normed space and $\beta \in \mathbb{R}$. The preconditioned Crank–Nicolson proposal moves from $u \in E$, given $\xi \in E$, to

$$
v = \sqrt{1 - \beta^2} \, u + \beta \, \xi ,
$$

where, in the algorithm, $\xi \sim N(0, C)$ is drawn from the prior independently of $u$. For $|\beta| > 1$ the square root of the negative number $1 - \beta^2$ is read as $0$. The case
$\beta = 1$ is the independence sampler (proposals drawn from the prior) and $\beta = 0$ never moves.

## Sources

- Masoumeh Dashti and Andrew M. Stuart, *The Bayesian approach to inverse problems*, in *Handbook of Uncertainty Quantification*, Springer (2017), 311–428, DOI 10.1007/978-3-319-12385-1_7; numbering of arXiv:1302.6989v4 (2015), Algorithm 5.10.
- Simon L. Cotter, Gareth O. Roberts, Andrew M. Stuart and David White, *MCMC methods for functions: modifying old algorithms to make them faster*, Statist. Sci. 28 (2013), no. 3, 424–446, DOI 10.1214/13-STS421; arXiv:1202.0709, equation (4.8) (the pCN proposal (4.7) with $\beta^2 = 8\delta/(2 + \delta)^2$).
