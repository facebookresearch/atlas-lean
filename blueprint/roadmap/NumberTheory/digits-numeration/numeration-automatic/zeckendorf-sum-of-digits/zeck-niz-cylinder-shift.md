# Shifting a new-information cylinder by two orders

Let $\mathbb{X}$ be the set of
Zeckendorf-adic integers: the digit sequences $x = (x_i)_{i \in \mathbb{N}}$ in $\{0, 1\}$ with
$x_0 = x_1 = 0$ and no two consecutive digits equal to $1$. Let $r \ge 1$, $k \ge 2$ and
$y \in \mathbb{X}$. Suppose that every $x \in \mathbb{X}$ with $x_{k+1} = x_k = 0$ and $x_i = y_i$
for $2 \le i \le k - 1$ lies in the new-information zone $\mathrm{NIZ}_k$ (for the shift $r$).
Then every $x \in \mathbb{X}$ with $x_{k+3} = x_{k+2} = 0$, $x_{k+1} = 1$, $x_k = 0$ and
$x_i = y_i$ for $2 \le i \le k - 1$ lies in $\mathrm{NIZ}_{k+2}$.

In the paper's cylinder notation, where $C_w$ is the set of points of $\mathbb{X}$ whose digits
ending at $x_2$ read $w$, and with $n_i = y_i$: $C_{00 n_{k-1} \cdots n_2} \subseteq \mathrm{NIZ}_k$
implies $C_{0010 n_{k-1} \cdots n_2} \subseteq \mathrm{NIZ}_{k+2}$.

## Sources

- Yohan Hosten, *On the Variation of the Sum of Digits in the Zeckendorf Representation: An Algorithm to Compute the Distribution and Mixing Properties*, Journal of Integer Sequences 27 (2024), Article 24.3.2, Lemma 33 (`jis-2024-24.3.2-lem-33`).
