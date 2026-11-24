# The ridge estimate maximizes the ridge posterior

Let $X$ be a real design matrix with $m$
rows and columns indexed by a finite type $\iota$, let $y \in \mathbb{R}^m$, and let $v$ and $\tau$
be positive reals. Let $p$ be the posterior kernel of linear regression with Gaussian noise of
variance $v$ and independent $N(0, \tau)$ priors on the coordinates of the parameter, and let
$\hat\theta = (X^\top X + \lambda I)^{-1} X^\top y$ be the ridge estimate with $\lambda = v / \tau$.
Then $\hat\theta$ maximizes $p$: for every $\theta \in \mathbb{R}^\iota$ we have
$p(\theta) \le p(\hat\theta)$.
