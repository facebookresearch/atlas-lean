# Posterior of a latent-variable model

For a joint model $p$ with finite latent space $Z$,
the posterior of the latent value $z$ given the observation $x$ at the parameter $\theta$ is
$p_\theta(z \mid x) = p_\theta(x, z) / p_\theta(x)$, where
$p_\theta(x) = \sum_{z' \in Z} p_\theta(x, z')$ is the marginal (the quotient is read as $0$
when the marginal is $0$). Computing it is the E-step of expectation-maximization.
