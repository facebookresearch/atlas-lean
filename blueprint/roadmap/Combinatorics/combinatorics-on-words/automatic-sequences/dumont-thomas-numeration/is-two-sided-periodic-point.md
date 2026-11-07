# Two-sided periodic points

Let $\eta$ map each letter of an alphabet $A$ to a finite
word over $A$, extended to finite words by concatenation, with iterates $\eta^j$; let
$u = (u_i)_{i \in \mathbb{Z}}$ be a two-sided word over $A$ and let $p$ be a natural number.
Then $u$ is a two-sided periodic point of $\eta$ with period $p$ when $p \ge 1$, for every
natural number $n$ the word $\eta^p(u_0 u_1 \cdots u_{n-1})$ is a prefix of the right-infinite
word $u_0 u_1 u_2 \cdots$, and for every natural number $m$ the word
$\eta^p(u_{-m} \cdots u_{-2} u_{-1})$ is a suffix of the left-infinite word
$\cdots u_{-3} u_{-2} u_{-1}$.

When $\eta$ is non-erasing this says that $\eta^p(u) = u$, where $\eta$ acts on the two-sided
word $\cdots u_{-2} u_{-1} \mid u_0 u_1 \cdots$ letterwise and keeps the origin between
$\eta(u_{-1})$ and $\eta(u_0)$.

## Sources

- Sébastien Labbé and Jana Lepšová, *Dumont-Thomas Complement Numeration Systems for ℤ*, INTEGERS 24 (2024), Article A112, Section 2 (periodic points `Per(η)`).
