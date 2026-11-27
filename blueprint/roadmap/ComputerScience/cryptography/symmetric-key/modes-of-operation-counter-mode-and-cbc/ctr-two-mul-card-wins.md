# Fresh counter ranges give an exact half guessing chance

Let $N > 0$, $\ell \le N$, and let $Y$ be a finite additive commutative group. Fix query counters $\rho \in (\mathbb{Z}/N)^q$ and a challenge counter $r_s$ such that the challenge counter range $r_s, \dots, r_s + \ell - 1$ is [fresh](ctr-fresh.md) for the query counters $\rho \in (\mathbb{Z}/N)^q$, and fix a first-phase computation $c$ of a CPA adversary. Count the pairs $(f, b)$ of a function $f \colon \mathbb{Z}/N \to Y$ and a bit $b$ for which the [fixed-tape guess](../../security-games/generic-security-games/cpa-tape-guess.md) $\mathrm{guess}(\mathrm{ctrEncrypt}(f, \cdot, \cdot), c, q, \rho, r_s, b)$ equals $b$. Then twice this number equals the number $2|Y|^N$ of all pairs.

The count concerns this fixed-tape guess (in which a query beyond the $q$ tape entries makes the guess `false`) for fixed $c$, $\rho$ and $r_s$; no query-bound hypothesis is needed.
