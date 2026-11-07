# The Zeckendorf Markov chain

Let $\varphi$ be the golden ratio, and let $\psi(0, t) = 1$
if $t < 1/\varphi^2$, $\psi(0, t) = 0$ otherwise, and $\psi(1, t) = 0$. For a real sequence
$(u_n)_{n \ge 0}$, written $u_n = U_{n+2}$, the chain $(y_j)_{j \in \mathbb{N}}$ is the sequence in
$\{0, 1\}$ with $y_0 = y_1 = 0$ and $y_j = \psi(y_{j-1}, U_j)$ for $j \ge 2$; that is,
$y_{n+2} = 1$ exactly when $y_{n+1} = 0$ and $u_n < 1/\varphi^2$.

The paper starts the chain at $y_1 = 0$; the extra digit $y_0 = 0$ matches the indexing of
Zeckendorf-adic digit sequences.

## Sources

- Yohan Hosten, *On the Variation of the Sum of Digits in the Zeckendorf Representation: An Algorithm to Compute the Distribution and Mixing Properties*, Journal of Integer Sequences 27 (2024), Article 24.3.2, Section 3.3 (the maps `ψ` and `(y_j)`).
