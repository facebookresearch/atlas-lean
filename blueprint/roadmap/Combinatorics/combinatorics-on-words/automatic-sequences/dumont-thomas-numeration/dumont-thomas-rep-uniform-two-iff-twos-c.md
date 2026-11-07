# Two's complement as a Dumont–Thomas numeration system

Let $\psi$ send each letter of an
alphabet $A$ to a word of length $2$ over $A$, and let $\beta$ be a two-sided infinite word over
$A$ that is a periodic point of $\psi$ with period $1$, that is, $\psi(\beta) = \beta$. For a
finite word $w = w_{k-1} \cdots w_1 w_0$ of natural numbers (most significant digit first), let
$\operatorname{val}_{2c}(w) = \sum_{i=0}^{k-1} w_i 2^i - w_{k-1} 2^k$ be its two's complement
value. Then for every integer $n$ and every such word $w$, $w$ is the Dumont–Thomas complement
representation $\operatorname{rep}_\beta(n)$ of $n$ for $\psi$, $\beta$ and period $1$ if and
only if $w$ is the two's complement representation of $n$: $w$ is nonempty, every digit of $w$
is $0$ or $1$, $w$ does not begin with $00$ or with $11$, and $\operatorname{val}_{2c}(w) = n$.

The hypotheses that $\psi$ is a substitution with a growing seed are implied by this
$2$-uniformity, and period $1$ is automatically the least period.

## Sources

- Sébastien Labbé and Jana Lepšová, *Dumont-Thomas Complement Numeration Systems for ℤ*, INTEGERS 24 (2024), Article A112, Proposition 9.1.
