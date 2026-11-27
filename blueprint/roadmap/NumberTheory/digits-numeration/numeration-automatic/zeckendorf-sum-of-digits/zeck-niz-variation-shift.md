# Lifting a cylinder of $\mathrm{NIZ}_k$ to order $k + 2$ lowers the variation by $1$

Let $\ell \ge 2$, let $r$ satisfy $F_\ell \le r < F_{\ell+1}$, where $F_1 = F_2 = 1, F_3 = 2,
\dots$ are the Fibonacci numbers, and let $k \ge \ell$. Write $\Delta^{(r)}$ for the variation
of the Zeckendorf sum of digits under adding $r$ on the Zeckendorf-adic integers $\mathbb{X}$,
and $\mathrm{NIZ}_k$ for the new-information zone of order $k$ for $r$. Let $y \in \mathbb{X}$
and $d \in \mathbb{Z}$. Let $C$ be the set of $x \in \mathbb{X}$ with $x_{k+1} = x_k = 0$ and
$x_i = y_i$ for $2 \le i \le k - 1$, and let $C'$ be the set of $x \in \mathbb{X}$ with
$x_{k+3} = x_{k+2} = 0$, $x_{k+1} = 1$, $x_k = 0$ and $x_i = y_i$ for $2 \le i \le k - 1$. If
$C \subseteq \mathrm{NIZ}_k$ and $\Delta^{(r)}(x) = d$ for every $x \in C$, then
$\Delta^{(r)}(x) = d - 1$ for every $x \in C'$.

In the paper's notation, $C = C_{00 n_{k-1} \cdots n_2}$ and $C' = C_{0010 n_{k-1} \cdots n_2}$
with $n_i = y_i$.

## Sources

- Yohan Hosten, *On the Variation of the Sum of Digits in the Zeckendorf Representation: An Algorithm to Compute the Distribution and Mixing Properties*, Journal of Integer Sequences 27 (2024), Article 24.3.2, Lemma 35 (`jis-2024-24.3.2-lem-35`).
