# Innocuous double rounding of square roots

Let $p \ge 1$ and $p' \ge 2p + 2$ be natural
numbers. For every real binary floating-point number $x$ with a $p$-bit significand and unbounded
exponent, rounding $\sqrt{x}$ to nearest, ties to even, first with $p'$ bits and then with $p$ bits
gives the same as rounding it directly with $p$ bits:
$\mathrm{fl}_p(\mathrm{fl}_{p'}(\sqrt{x})) = \mathrm{fl}_p(\sqrt{x})$.

For $x < 0$ both sides are $0$, with the convention $\sqrt{x} = 0$.
