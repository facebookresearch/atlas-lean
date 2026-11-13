# Distribution of a sum of independent Bernoulli variables

Let $\mu$ be a probability
measure on a measurable space $\Omega$, let $m \in \mathbb{N}$, and let
$X_1, \dots, X_m : \Omega \to \mathbb{N}$ be measurable, mutually independent random variables
such that each $X_i$ is a Bernoulli random variable with real parameter $p_i$ under $\mu$.
Then for every $j \in \mathbb{N}$ the probability that $X_1 + \dots + X_m = j$ equals

$$
\sum_{A \subseteq \{1, \dots, m\},\ |A| = j} \ \prod_{i \in A} p_i \prod_{i \notin A} (1 - p_i).
$$

This is the Poisson binomial distribution.
