# Conditional probability that prescribed later digits vanish

Let
$\mathbb{X} \subseteq \{0,1\}^{\mathbb{N}}$ be the set of Zeckendorf-adic integers (sequences
with $x_0 = x_1 = 0$ and no two consecutive ones), let $T$ be the Zeckendorf odometer, and let
$\varphi$ be the golden ratio. Let $\mu$ be a probability measure on $\{0,1\}^{\mathbb{N}}$ with
$\mu(\mathbb{X}^c) = 0$ that is preserved by $T$. Let $\ell \in \mathbb{N}$ and let
$k_0, \dots, k_\ell$ be natural numbers with $2 \le k_0 < k_1 < \dots < k_\ell$. Let
$A \subseteq \{0,1\}^{\mathbb{N}}$ be a set such that whether $x \in A$ depends only on the digits
$x_2, \dots, x_{k_0}$, with $x_{k_0} = 0$ for every $x \in A$ and $\mu(A) > 0$. Then the event
$E = \{x : x_{k_i} = 0 \text{ for } 1 \le i \le \ell\}$ has conditional probability
$1/\varphi^\ell \le \mu(E \mid A) \le (2/\varphi^2)^\ell$.

## Sources

- Yohan Hosten, *On the Variation of the Sum of Digits in the Zeckendorf Representation: An Algorithm to Compute the Distribution and Mixing Properties*, Journal of Integer Sequences 27 (2024), Article 24.3.2, Proposition 21 (`jis-2024-24.3.2-prop-21`).
