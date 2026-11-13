# Ridge regression is MAP estimation

Let $X$ be a real design matrix with $m$ rows and
columns indexed by a finite type $\iota$, let $y \in \mathbb{R}^m$, and let $v$ and $\tau$ be
positive reals. Let $p$ be the posterior kernel of linear regression with Gaussian noise of
variance $v$ and independent $N(0, \tau)$ priors on the coordinates of the parameter, and let $R$
be the ridge objective with $\lambda = v / \tau$. Then for all
$\theta, \theta' \in \mathbb{R}^\iota$ we have $p(\theta) \le p(\theta')$ if and only if
$R(\theta') \le R(\theta)$.

So the posterior kernel is a decreasing function of the ridge objective.
