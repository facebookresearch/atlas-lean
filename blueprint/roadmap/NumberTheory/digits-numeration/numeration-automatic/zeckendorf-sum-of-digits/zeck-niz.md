# New-information zone

Let $F_1 = F_2 = 1, F_3 = 2, \dots$ be the Fibonacci numbers, and
for a digit sequence $x = (x_i)_{i \ge 0}$ with $x_i \in \{0, 1\}$ and $j \in \mathbb{N}$ let
$v_j(x) = \sum_{i=2}^{j+1} x_i F_i$. For $r \in \mathbb{N}$ let $\mathrm{CST}_j$ be the
set of digit sequences $x$ with $v_j(x) + r < F_{j+1}$, or with $F_{j+1} \le v_j(x)$ and
$v_j(x) + r < F_{j+2}$. For $k \in \mathbb{N}$, the new-information zone of order $k$
for $r$ is $\mathrm{NIZ}_k = \mathrm{CST}_k \setminus \mathrm{CST}_{k-1}$, where $k - 1$ is read
as $0$ when $k = 0$ (so $\mathrm{NIZ}_0 = \emptyset$).

## Sources

- Yohan Hosten, *On the Variation of the Sum of Digits in the Zeckendorf Representation: An Algorithm to Compute the Distribution and Mixing Properties*, Journal of Integer Sequences 27 (2024), Article 24.3.2, Section 5.1 (definition of `NIZ_k`).
