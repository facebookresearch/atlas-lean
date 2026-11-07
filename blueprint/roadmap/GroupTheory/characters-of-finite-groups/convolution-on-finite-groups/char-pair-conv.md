# Convolution theorem for one-dimensional characters

Let $G$ be a finite group, let
$\varphi : G \to \mathbb{C}$ satisfy $\varphi(1) = 1$ and $\varphi(xy) = \varphi(x)\varphi(y)$
for all $x, y \in G$ (a one-dimensional character), and let $f, g : G \to \mathbb{C}$. Writing
$f \ast g$ for the convolution $(f \ast g)(x) = \sum_{y \in G} f(y)\, g(y^{-1} x)$, we have

$$
\sum_{x \in G} \varphi(x)\,(f \ast g)(x) =
\Big(\sum_{x \in G} \varphi(x) f(x)\Big)\Big(\sum_{x \in G} \varphi(x) g(x)\Big).
$$

Proof: Swap the finite sums, reindex by $x = yz$, and use multiplicativity of $\varphi$ to
factor the character pairing, following Terras, Ch. 2–3.

## Sources

- `undergrad.yaml`, section "Representation theory of finite groups", entry "convolution"; A. Terras, Fourier Analysis on Finite Groups and Applications, Ch. 2–3 (the Fourier transform takes convolution to pointwise products).
