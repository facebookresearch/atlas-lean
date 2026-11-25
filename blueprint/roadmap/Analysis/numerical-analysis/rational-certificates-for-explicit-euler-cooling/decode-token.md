# Decoding a rational token

A list of characters is split at every $\texttt{'/'}$. If there are exactly two pieces $a$ and $b$, and $a$ decodes as a signed numerator $z$ and $b$ as a denominator $d \in [1, 10^{10}]$, the token decodes to the rational $z/d$; otherwise the result is none.
