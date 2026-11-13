# Posterior of an unnormalized joint

Let $Z$ be a finite set and let
$p : Z \to \mathbb{R}$ give the joint values $p(z) = p(x, z)$ of a fixed observation $x$ with each
latent value $z \in Z$. The posterior of $z$ is $p(z \mid x) = p(z) / p(x)$, where
$p(x) = \sum_{z' \in Z} p(z')$ is the evidence (the quotient is read as $0$ when $p(x) = 0$).
