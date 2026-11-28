# Weight matrix of a generalized estimating equation

For a mean model $\mu$ with Jacobian $D(\beta)$ and a declared working covariance $V$, the GEE weight of one cluster is $D(\beta)^\top V^{-1}$. Here $V^{-1}$ is the matrix inverse, taken as $0$ when $V$ is singular.
