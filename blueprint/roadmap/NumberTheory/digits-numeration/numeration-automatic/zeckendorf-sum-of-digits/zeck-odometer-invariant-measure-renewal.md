# Renewal property of the invariant measure

Let
$\mathbb{X} \subseteq \{0,1\}^{\mathbb{N}}$ be the set of Zeckendorf-adic integers (sequences
with $x_0 = x_1 = 0$ and no two consecutive ones) and let $T$ be the Zeckendorf odometer. Let
$\mu$ be a probability measure on $\{0,1\}^{\mathbb{N}}$ with $\mu(\mathbb{X}^c) = 0$ that is
preserved by $T$. Let $k \ge 2$, $\ell_0 \in \mathbb{N}$ and $y, z \in \mathbb{X}$, and let
$C = \{x : x_i = z_i \text{ for } 2 \le i \le \ell_0\}$. Let
$E_0 = \{x : x_{k+1} = 0 \text{ and } x_i = y_i \text{ for } 2 \le i \le k\}$ and
$E_1 = \{x : x_{k+1} = 1 \text{ and } x_i = y_i \text{ for } 2 \le i \le k\}$. Then
$\mu(\{x : x_{i+k} = z_i \text{ for } 2 \le i \le \ell_0\} \mid E_0) = \mu(C)$, and if
$y_k = 0$, then also
$\mu(\{x : x_{i+k+1} = z_i \text{ for } 2 \le i \le \ell_0\} \mid E_1) = \mu(C)$.

With the shift $(\sigma x)_i = x_{i+1}$, the two conditioned events are $\sigma^k x \in C$ and
$\sigma^{k+1} x \in C$.

## Sources

- Yohan Hosten, *On the Variation of the Sum of Digits in the Zeckendorf Representation: An Algorithm to Compute the Distribution and Mixing Properties*, Journal of Integer Sequences 27 (2024), Article 24.3.2, Proposition 16 (`jis-2024-24.3.2-prop-16`).
