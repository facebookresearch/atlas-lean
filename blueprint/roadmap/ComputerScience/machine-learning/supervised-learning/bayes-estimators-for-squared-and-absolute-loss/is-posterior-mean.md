# Measurable versions of the posterior mean

Let $P$ be a finite kernel from $\mathbb{R}$ to
a measurable space $\mathcal{X}$, sending $\theta$ to the measure $P_\theta$, let $\pi$ be a
finite measure on $\mathbb{R}$, and write $P^\dagger\pi$ for the posterior kernel from
$\mathcal{X}$ to $\mathbb{R}$. A function $f : \mathcal{X} \to \mathbb{R}$ is a measurable version
of the posterior mean if $f$ is measurable and $f(x) = \int \theta \, d(P^\dagger\pi)(x)(\theta)$
(the posterior mean, taken to be $0$ when the posterior has no finite first moment) for almost
every $x$ with respect to the marginal distribution of the data, the measure
$A \mapsto \int P_\theta(A) \, d\pi(\theta)$ on $\mathcal{X}$.
