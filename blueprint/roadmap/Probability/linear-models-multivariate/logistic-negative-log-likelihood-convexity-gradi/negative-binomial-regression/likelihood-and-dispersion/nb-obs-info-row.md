# Observed information of one negative binomial regression observation

For a shape $\theta$, a covariate row $x$, a count $y$ and a linear predictor $\eta$, the observed information in $(\beta, \theta)$ is the block matrix $\begin{pmatrix}w\,xx^\top & -c\,x\\ -c\,x^\top & v\end{pmatrix}$ with $w$ the observed weight $\theta(y + \theta)\mu/(\theta + \mu)^2$, $c = (y - \mu)\mu/(\theta + \mu)^2$ and $v$ the observed shape information, with $\mu = e^\eta$.
