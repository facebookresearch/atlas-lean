# Growth function of the dense-set construction

Let $\operatorname{Log}_2$ be the second
iterated truncated logarithm. For real numbers $C_0$ and $x$, let $k$ be the natural number
$\max(\lceil C_0 \sqrt{\operatorname{Log}_2 x}\,\rceil - 1, 0)$, and set
$h = \operatorname{Log}_2 x - k^2/C_0^2 + 1$, $x' = \exp(\exp((k + 1)^2/C_0^2))$,
$h' = \operatorname{Log}_2 x' - k^2/C_0^2 + 1$ and $\psi = 1 + h^2/h'$. The growth function at
$(C_0, x)$ is $F_{C_0}(x) = \psi\, k^{2k} / (C_0^{2k}\, k!)$. Here division by $0$ gives $0$ and
$0^0 = 1$.

In the source, $h'$ is the value at $x_{k+1} = x'$ of the expression defining $h$, with $k$ kept
fixed, and $F_{C_0}(x)$ is written $\psi(x)\, k^{2k} C_0^{-2k}/k!$; the function is used only for
$C_0 > 0$ and sufficiently large $x$.

## Sources

- Terence Tao, *Dense Sets of Natural Numbers with Unusually Large Least Common Multiples*, INTEGERS 24 (2024), Article A100, Equations (13)--(15).
