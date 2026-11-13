# Last-letter digit word for the Fibonacci substitution

Let $\varphi$ be the Fibonacci
substitution on the alphabet $\{0, 1\}$, given by $\varphi(0) = 01$ and $\varphi(1) = 0$.
Following the last letter twice from the letter $1$, where each step from a letter $c$ records
the digit $|\varphi(c)| - 1$ and moves to the last letter of $\varphi(c)$, gives the digit word
$01$: the word $\varphi(1) = 0$ gives the digit $|\varphi(1)| - 1 = 0$ and ends with $0$, and
then the word $\varphi(0) = 01$ gives the digit $|\varphi(0)| - 1 = 1$ and ends with $1$.

This digit word $01$ is the word that Labbé and Lepšová denote $W_{\max}$ for the Fibonacci
substitution, written there $a \mapsto ab$, $b \mapsto a$ with $a = 0$ and $b = 1$, and the
period $p = 2$.

## Sources

- Labbé and Lepšová, *Dumont-Thomas Complement Numeration Systems for ℤ*, INTEGERS 24 (2024), Article A112, proof of Proposition 9.2 (`W_max = 01`).
