# Without-replacement bounds for uniform random injections

Let $T, \alpha$ be finite sets with $1 \le |T| \le |\alpha|$, and let $e$ be a uniformly random injection $T \hookrightarrow \alpha$.

1. Each fixed $a \in \alpha$ lies in the image of $e$ with probability $|T|/|\alpha|$.
2. (Negative correlation) For every $Q \subseteq \alpha$, $\Pr[e(i) \in Q \text{ for all } i \in T] \le (|Q|/|\alpha|)^{|T|}$.
3. (Per-coordinate targets) If $2|T|^2 \le |\alpha|$, then for all $Q_i \subseteq \alpha$, $\Pr[e(i) \in Q_i \text{ for all } i] \le 2\prod_{i \in T}|Q_i|/|\alpha|$.
4. (Injections versus functions) The statistical distance between the law of $e$, viewed as a function $T \to \alpha$, and a uniformly random function $T \to \alpha$ is at most $|T|(|T|-1)/(2|\alpha|)$.

## Proof sketch

Item 1 is symmetry. Item 2 is the without-replacement product $\prod_{k<|T|}\frac{|Q|-k}{|\alpha|-k} \le (|Q|/|\alpha|)^{|T|}$. Item 3 compares sequential conditional probabilities $|Q_i|/(|\alpha| - k)$ with $|Q_i|/|\alpha|$, and $\prod_k (1 - k/|\alpha|)^{-1} \le 2$ when $2|T|^2 \le |\alpha|$. Item 4: a uniform function conditioned on being injective is a uniform injection, so the distance equals the probability of a collision, at most $|T|(|T|-1)/(2|\alpha|)$ by the birthday bound.

## Proof depends on

- [Birthday upper bound](../../../ComputerScience/cryptography/hash-functions/birthday-bound/collision-prob-le.md)

## Sources

- M. A. Bender, M. Farach-Colton, J. Kuszmaul, W. Kuszmaul and M. Liu, "On the Optimal Time/Space Tradeoff for Hash Tables", Proceedings of the 54th Annual ACM Symposium on Theory of Computing (STOC), 2022.
- Y. Arbitman, M. Naor and G. Segev, "Backyard Cuckoo Hashing: Constant Worst-Case Operations with a Succinct Representation", Proceedings of the 51st Annual IEEE Symposium on Foundations of Computer Science (FOCS), 2010.
