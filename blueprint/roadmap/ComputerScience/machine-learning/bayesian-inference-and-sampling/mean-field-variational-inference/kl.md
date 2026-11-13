# Finite Kullback–Leibler formula

Let $Z$ be a finite set and let $q, r : Z \to \mathbb{R}$.
The Kullback–Leibler formula of $q$ against $r$ is
$\mathrm{KL}(q \,\|\, r) = \sum_{z \in Z} q(z) \bigl(\log q(z) - \log r(z)\bigr)$; terms with
$q(z) = 0$ vanish.

This is the Kullback–Leibler divergence of $q$ from $r$ when $r(z) > 0$ for every $z$, the only
case used here (where $r$ is the posterior of a positive joint). If $r$ vanishes where $q$ does
not, the divergence is infinite, but this real-valued formula is finite, since it reads $\log 0$
as $0$.
