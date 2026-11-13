# The ELBO is the log evidence minus the KL divergence

Let $Z$ be a nonempty finite set
and let $p : Z \to \mathbb{R}$ give the joint values $p(z) = p(x, z)$ of a fixed observation $x$
with each latent value $z \in Z$, where $p(z) > 0$ for every $z \in Z$. Let
$p(x) = \sum_{z \in Z} p(z)$ be the evidence and $p(z \mid x) = p(z) / p(x)$ the posterior. For
$q, r : Z \to \mathbb{R}$ write
$\mathrm{ELBO}(p, q) = \sum_{z \in Z} q(z) \bigl(\log p(z) - \log q(z)\bigr)$ and
$\mathrm{KL}(q \,\|\, r) = \sum_{z \in Z} q(z) \bigl(\log q(z) - \log r(z)\bigr)$. Then for every
probability distribution $q$ on $Z$,
$\mathrm{ELBO}(p, q) = \log p(x) - \mathrm{KL}\bigl(q \,\|\, p(\cdot \mid x)\bigr)$.
