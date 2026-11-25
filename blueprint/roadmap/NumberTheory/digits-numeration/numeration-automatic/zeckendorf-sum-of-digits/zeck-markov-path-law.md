# The Zeckendorf Markov chain has the invariant law

Let $\mathbb{X}$ be the set of
Zeckendorf-adic integers: the digit sequences $x \in \{0, 1\}^{\mathbb{N}}$ with $x_0 = x_1 = 0$
and no two consecutive digits equal to $1$. Let $\mu$ be a probability measure on
$\{0, 1\}^{\mathbb{N}}$ with $\mu(\mathbb{X}^c) = 0$ that is preserved by the odometer $T$. Let
$(\Omega, \nu)$ be a probability space and let $(U_n)_{n \ge 0}$ be independent measurable real
random variables on $\Omega$, each uniformly distributed on $[0, 1]$. Then the law under $\nu$ of
the digit sequence $\omega \mapsto (y_j(\omega))_{j \in \mathbb{N}}$ of the Zeckendorf Markov chain
driven by $(U_n(\omega))_{n \ge 0}$ is $\mu$.

The paper indexes the uniform variables from $2$, writing $U_{n+2}$ for the $U_n$ here; the
measure $\mu$ is the paper's $\mathbb{P}$.

## Sources

- Yohan Hosten, *On the Variation of the Sum of Digits in the Zeckendorf Representation: An Algorithm to Compute the Distribution and Mixing Properties*, Journal of Integer Sequences 27 (2024), Article 24.3.2, Lemma 20 (`jis-2024-24.3.2-lem-20`).
