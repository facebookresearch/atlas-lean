# Without-replacement bounds for uniform random injections

Let $T, \alpha$ be finite sets with $1 \le |T| \le |\alpha|$, and let $e$ be a uniformly random injection $T \hookrightarrow \alpha$. For every subset $Q \subseteq \alpha$,

$$
\Pr[e(i) \in Q \text{ for all } i \in T] \le \Bigl(\frac{|Q|}{|\alpha|}\Bigr)^{|T|}
$$

(negative correlation of without-replacement draws; Bender, Farach-Colton, Kuszmaul, Kuszmaul and Liu, Section 5.3).

## Proof sketch

The without-replacement probability is $\prod_{k<|T|}\frac{|Q|-k}{|\alpha|-k} \le (|Q|/|\alpha|)^{|T|}$, since $(|Q|-k)/(|\alpha|-k) \le |Q|/|\alpha|$ whenever $|Q| \le |\alpha|$.

The following consequences are derived here and are not stated in the cited sources: (1) each fixed $a \in \alpha$ lies in the image of $e$ with probability $|T|/|\alpha|$, by symmetry, since the image of $e$ is a uniformly random $|T|$-element subset of $\alpha$; (2) (per-coordinate targets) if $2|T|^2 \le |\alpha|$, then for all $Q_i \subseteq \alpha$, $\Pr[e(i) \in Q_i \text{ for all } i \in T] \le 2\prod_{i \in T}(|Q_i|/|\alpha|)$, comparing sequential conditional probabilities $|Q_i|/(|\alpha| - k)$ with $|Q_i|/|\alpha|$ and using $\prod_{k<|T|}(1 - k/|\alpha|)^{-1} \le 2$; (3) (injections versus functions) the total variation distance between the law of $e$, viewed as a function $T \to \alpha$, and a uniformly random function $T \to \alpha$ is at most $|T|(|T|-1)/(2|\alpha|)$, since a uniform function conditioned on being injective is a uniform injection, so the distance equals the collision probability, bounded by the birthday bound.

## Proof depends on

- [Total variation distance between finite measures](../../convergence-of-measures/total-variation-distance/total-variation-dist.md)
- [Birthday upper bound](../../../ComputerScience/cryptography/hash-functions/birthday-bound/collision-prob-le.md)

## Sources

- M. A. Bender, M. Farach-Colton, J. Kuszmaul, W. Kuszmaul and M. Liu, "On the Optimal Time/Space Tradeoff for Hash Tables", Proceedings of the 54th Annual ACM Symposium on Theory of Computing (STOC), 2022; full version arXiv:2111.00602v2, Section 5.3, p. 35.
- Y. Arbitman, M. Naor and G. Segev, "Backyard Cuckoo Hashing: Constant Worst-Case Operations with a Succinct Representation", Proceedings of the 51st Annual IEEE Symposium on Foundations of Computer Science (FOCS), 2010.
