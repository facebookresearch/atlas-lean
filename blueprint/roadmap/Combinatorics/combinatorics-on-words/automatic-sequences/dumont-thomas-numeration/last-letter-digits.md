# Digit word along last letters

Let $\eta$ send each letter of an alphabet $A$ to a
finite word over $A$. For $k \in \mathbb{N}$ and a letter $c \in A$, the word
$\mathrm{last}_{\eta,k}(c)$ of natural numbers is defined by recursion on $k$:
$\mathrm{last}_{\eta,0}(c)$ is the empty word; if $\eta(c)$ is nonempty with last letter $d$,
then $\mathrm{last}_{\eta,k+1}(c)$ is the digit $|\eta(c)| - 1$ followed by
$\mathrm{last}_{\eta,k}(d)$; and if $\eta(c)$ is empty, then $\mathrm{last}_{\eta,k+1}(c)$ is
the empty word.

For a substitution $\eta$, a number $p \ge 1$ and a letter $c \in A$, the word
$\mathrm{last}_{\eta,p}(c)$ is the digit word of the last position of $\eta^p(c)$, written
$\mathrm{tail}_{\eta,p,c}(|\eta^p(c)| - 1)$ in the source. In Section 7 of the source, where
$u : \mathbb{Z} \to A$ is a two-sided periodic point of $\eta$ with least period $p$ and seed
letters $u_{-1}$ and $u_0$, the words $W_{\max} = \mathrm{last}_{\eta,p}(u_{-1})$ and
$W_{\min} = 0^p$ are used.

## Sources

- Sébastien Labbé and Jana Lepšová, *Dumont-Thomas Complement Numeration Systems for ℤ*, INTEGERS 24 (2024), Article A112, Section 7 (the words `W_min` and `W_max`).
