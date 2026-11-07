# Fourier inversion on a finite abelian group

Let $G$ be a finite abelian group with $|G|$
elements, let $f : G \to \mathbb{C}$, and write $\hat f(\psi) = \sum_{y \in G} \psi(y) f(y)$ for
the discrete Fourier transform of $f$ at an additive character $\psi$ of $G$ with values in
$\mathbb{C}$. Then for every $x \in G$,
$f(x) = \frac{1}{|G|} \sum_{\psi} \overline{\psi(x)} \, \hat f(\psi)$, where $\psi$ runs over
all additive characters of $G$ with values in $\mathbb{C}$.

Proof: expand the transform and collapse the inner sum with the orthogonality of characters.
This is the Fourier inversion formula (4.4) of K. Conrad, Characters of finite abelian groups,
Section 4, https://kconrad.math.uconn.edu/blurbs/grouptheory/charthy.pdf, up to reindexing
$\psi \mapsto \psi^{-1}$ (Conrad conjugates the character in the transform rather than in the
inversion sum).

## Sources

- `undergrad.yaml`, section "Fourier transform", entry "discrete Fourier transform on a finite abelian group"; A. Terras, Fourier Analysis on Finite Groups and Applications, Ch. 2, Fourier inversion theorem.
