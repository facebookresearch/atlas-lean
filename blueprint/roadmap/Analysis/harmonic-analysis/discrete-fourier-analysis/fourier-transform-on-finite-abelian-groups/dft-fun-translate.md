# Translation modulates the discrete Fourier transform

Let $G$ be a finite abelian group,
$f : G \to \mathbb{C}$, $t \in G$, and $\psi$ an additive character of $G$ with values in
$\mathbb{C}$, and write $\hat h(\psi) = \sum_{x \in G} \psi(x) h(x)$ for the discrete Fourier
transform of $h : G \to \mathbb{C}$. If $g(x) = f(x - t)$ for all $x \in G$, then
$\hat g(\psi) = \psi(t) \hat f(\psi)$.

Proof: reindex the finite sum by $x \mapsto x + t$ and use $\psi(x + t) = \psi(x) \psi(t)$.

## Sources

- A. Terras, Fourier Analysis on Finite Groups and Applications, Ch. 2 (translation and modulation).
