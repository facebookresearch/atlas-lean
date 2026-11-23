# The Miller–Rabin squaring loop

Fix a modulus $n$. With no squarings remaining, the loop
at the current value $x$ reports a witness exactly when $x \ne 1$, at no cost. With $k + 1$
squarings remaining, it costs one modular multiplication and computes $y = x^2 \bmod n$; it
reports a witness if $y = 1$, $x \ne 1$ and $x \ne n - 1$, and otherwise continues at $y$ with
$k$ squarings remaining.

Here $x^2 \bmod 0 = x^2$, and $n - 1$ is $0$ when $n = 0$.
