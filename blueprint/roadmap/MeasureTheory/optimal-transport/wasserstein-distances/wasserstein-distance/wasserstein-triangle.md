# Triangle inequality for the Wasserstein distance

Let $X$ be a second-countable standard Borel pseudo-extended metric space with its Borel σ-algebra
(for example a Polish metric space) and $p \ge 1$. For all probability measures
$\mu_1, \mu_2, \mu_3$ on $X$,

$$W_p(\mu_1, \mu_3) \le W_p(\mu_1, \mu_2) + W_p(\mu_2, \mu_3).$$

Proof: [glue](exists-gluing.md) a coupling of $(\mu_1, \mu_2)$ to a coupling of $(\mu_2, \mu_3)$
along $\mu_2$, read off a coupling of $(\mu_1, \mu_3)$, and apply the triangle inequality for $d$ and
Minkowski's inequality in $L^p$. Villani glues optimal couplings; gluing arbitrary couplings and
taking infima avoids the existence of optimal couplings.

## Sources

- C. Villani, *Optimal Transport: Old and New*, Grundlehren der mathematischen Wissenschaften 338, Springer 2009, Chapter 6, proof that $W_p$ satisfies the axioms of a distance, after Definition 6.1.
