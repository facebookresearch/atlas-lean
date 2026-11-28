# Cox score map on the indicator space

For an arbitrary coordinate vector $\mu$ (not necessarily an encoded sample mean), the Cox score map is $\Psi(\mu, b) = \sum_{j,a}\mu(\text{event}, j, a)\big(c_a - S^{(1)}(\mu, b, j)/S^{(0)}(\mu, b, j)\big)$, where a quotient with $S^{(0)}(\mu, b, j) = 0$ is $0$. When the grid times and the covariate levels are each distinct and contain every observed time and every covariate of the first $n$ observations, the Cox score of those observations is $U_n(b) = n\Psi(\bar x_n, b)$, with $\bar x_n$ the mean of the encoded observations.
